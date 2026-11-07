// pingd is the Go peer of the W5.8 live interoperability check.
// It uses tcp, Noise and yamux explicitly. The module version is pinned
// by ping-interop.py. Successful compilation is not an interop result.
package main

import (
	"context"
	"errors"
	"flag"
	"fmt"
	"io"
	"os"
	"time"

	"github.com/libp2p/go-libp2p"
	"github.com/libp2p/go-libp2p/core/peer"
	"github.com/libp2p/go-libp2p/p2p/muxer/yamux"
	"github.com/libp2p/go-libp2p/p2p/protocol/ping"
	"github.com/libp2p/go-libp2p/p2p/security/noise"
	"github.com/libp2p/go-libp2p/p2p/transport/tcp"
)

var errUsage = errors.New("usage error")

func run(args []string) error {
	flags := flag.NewFlagSet("pingd", flag.ContinueOnError)
	mode := flags.String("mode", "", "serve or dial")
	port := flags.Int("port", 0, "loopback TCP listen port")
	address := flags.String("addr", "", "dial target with a peer suffix")
	if err := flags.Parse(args); err != nil {
		return fmt.Errorf("%w: %v", errUsage, err)
	}
	if flags.NArg() != 0 || (*mode != "serve" && *mode != "dial") || *port < 0 || *port > 65535 {
		return fmt.Errorf("%w: pingd -mode serve -port N | -mode dial -addr <multiaddr>", errUsage)
	}
	var remote *peer.AddrInfo
	if *mode == "dial" {
		var err error
		remote, err = peer.AddrInfoFromString(*address)
		if err != nil {
			return fmt.Errorf("%w: %v", errUsage, err)
		}
	}
	host, err := libp2p.New(
		libp2p.NoTransports,
		libp2p.Transport(tcp.NewTCPTransport),
		libp2p.Security(noise.ID, noise.New),
		libp2p.Muxer("/yamux/1.0.0", yamux.DefaultTransport),
		libp2p.ListenAddrStrings(fmt.Sprintf("/ip4/127.0.0.1/tcp/%d", *port)),
	)
	if err != nil {
		return err
	}
	defer host.Close()
	_ = ping.NewPingService(host)
	if *mode == "serve" {
		if len(host.Addrs()) == 0 {
			return errors.New("no bound address")
		}
		fmt.Printf("ADDR %s %s\n", host.Addrs()[0], host.ID())
		_, err = io.Copy(io.Discard, os.Stdin)
		return err
	}
	ctx, cancel := context.WithTimeout(context.Background(), 30*time.Second)
	defer cancel()
	if err := host.Connect(ctx, *remote); err != nil {
		return fmt.Errorf("connect: %w", err)
	}
	select {
	case result, ok := <-ping.Ping(ctx, host, remote.ID):
		if !ok {
			return errors.New("ping ended without a result")
		}
		if result.Error != nil {
			return result.Error
		}
		fmt.Printf("PING OK rtt=%dms\n", result.RTT.Milliseconds())
		return nil
	case <-ctx.Done():
		return ctx.Err()
	}
}

func main() {
	if err := run(os.Args[1:]); err != nil {
		fmt.Fprintln(os.Stderr, err)
		if errors.Is(err, errUsage) {
			os.Exit(2)
		}
		os.Exit(1)
	}
}
