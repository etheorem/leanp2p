// Dial one peer, or listen for one, and close on stdin EOF.
//
// `ping-go <multiaddr>` dials. The argument's last component is the
// expected peer id. `ping-go listen` binds `/ip4/127.0.0.1/tcp/0` and
// prints `ADDR <multiaddr> <peerid>` for the address the kernel bound.
// The host is TCP, Noise, and yamux. Listen uses the host's enabled
// ping service. A failed setup, connection, deadline, or ping exits 1.
// A bad argument count exits 2.
//
// ping.Ping runs until its context ends. After the first successful
// result the helper cancels that context, reads the result channel
// until it closes, prints the result, and waits for stdin EOF. The
// listen path prints ADDR and waits for the same EOF. The host stays
// open through that wait. The host closes on every return after it
// exists.
package main

import (
	"context"
	"fmt"
	"io"
	"os"
	"strings"
	"time"

	"github.com/libp2p/go-libp2p"
	"github.com/libp2p/go-libp2p/core/host"
	"github.com/libp2p/go-libp2p/core/peer"
	"github.com/libp2p/go-libp2p/p2p/muxer/yamux"
	"github.com/libp2p/go-libp2p/p2p/protocol/ping"
	"github.com/libp2p/go-libp2p/p2p/security/noise"
	"github.com/libp2p/go-libp2p/p2p/transport/tcp"
)

const pingBudget = 20 * time.Second

func main() {
	switch {
	case len(os.Args) == 2 && os.Args[1] == "listen":
		if err := listen(); err != nil {
			fmt.Fprintf(os.Stderr, "ping-go: %s\n", err)
			os.Exit(1)
		}
	case len(os.Args) == 2:
		if err := run(os.Args[1]); err != nil {
			fmt.Fprintf(os.Stderr, "ping-go: %s\n", err)
			os.Exit(1)
		}
	default:
		fmt.Fprintln(os.Stderr, "usage: ping-go <multiaddr>")
		fmt.Fprintln(os.Stderr, "       ping-go listen")
		os.Exit(2)
	}
}

func listen() (err error) {
	h, err := libp2p.New(
		libp2p.ListenAddrStrings("/ip4/127.0.0.1/tcp/0"),
		libp2p.Transport(tcp.NewTCPTransport),
		libp2p.Security(noise.ID, noise.New),
		libp2p.Muxer("/yamux/1.0.0", yamux.DefaultTransport),
		libp2p.Ping(true),
	)
	if err != nil {
		return fmt.Errorf("host: %s", err)
	}
	defer func() {
		if cerr := h.Close(); cerr != nil && err == nil {
			err = fmt.Errorf("close: %s", cerr)
		}
	}()
	addr, err := loopbackAddr(h)
	if err != nil {
		return err
	}
	fmt.Printf("ADDR %s %s\n", addr, h.ID())
	if err := os.Stdout.Sync(); err != nil {
		return fmt.Errorf("stdout: %s", err)
	}
	return waitStdin()
}

func loopbackAddr(h host.Host) (string, error) {
	const prefix = "/ip4/127.0.0.1/tcp/"
	for _, addr := range h.Network().ListenAddresses() {
		text := addr.String()
		if !strings.HasPrefix(text, prefix) || strings.Contains(text, "/p2p/") {
			continue
		}
		port := strings.TrimPrefix(text, prefix)
		if port == "" || port == "0" || strings.Contains(port, "/") {
			continue
		}
		return text, nil
	}
	return "", fmt.Errorf("no loopback listen address")
}

func run(target string) (err error) {
	info, err := peer.AddrInfoFromString(target)
	if err != nil {
		return fmt.Errorf("address: %s", err)
	}
	host, err := libp2p.New(
		libp2p.Transport(tcp.NewTCPTransport),
		libp2p.Security(noise.ID, noise.New),
		libp2p.Muxer("/yamux/1.0.0", yamux.DefaultTransport),
		libp2p.NoListenAddrs,
	)
	if err != nil {
		return fmt.Errorf("host: %s", err)
	}
	defer func() {
		if cerr := host.Close(); cerr != nil && err == nil {
			err = fmt.Errorf("close: %s", cerr)
		}
	}()

	ctx, cancel := context.WithTimeout(context.Background(), pingBudget)
	defer cancel()
	if err := host.Connect(ctx, *info); err != nil {
		return fmt.Errorf("connect: %s", err)
	}
	results := ping.Ping(ctx, host, info.ID)
	var rtt time.Duration
	select {
	case result, ok := <-results:
		if !ok {
			return fmt.Errorf("ping returned no result")
		}
		if result.Error != nil {
			return fmt.Errorf("ping: %s", result.Error)
		}
		rtt = result.RTT
	case <-ctx.Done():
		return fmt.Errorf("ping deadline: %s", ctx.Err())
	}
	if err := stopPing(cancel, results); err != nil {
		return err
	}
	fmt.Printf("PING OK rtt=%s\n", rtt)
	if err := os.Stdout.Sync(); err != nil {
		return fmt.Errorf("stdout: %s", err)
	}
	return waitStdin()
}

// stopPing ends ping.Ping and waits until its result channel closes.
// The library resets the ping stream when the context ends. The bound
// is pingBudget.
func stopPing(cancel context.CancelFunc, results <-chan ping.Result) error {
	cancel()
	timer := time.NewTimer(pingBudget)
	defer timer.Stop()
	for {
		select {
		case _, ok := <-results:
			if !ok {
				return nil
			}
		case <-timer.C:
			return fmt.Errorf("ping stop deadline")
		}
	}
}

// waitStdin reads until EOF. Bytes before EOF are discarded.
func waitStdin() error {
	buf := make([]byte, 256)
	for {
		_, err := os.Stdin.Read(buf)
		if err == io.EOF {
			return nil
		}
		if err != nil {
			return fmt.Errorf("teardown: %s", err)
		}
	}
}
