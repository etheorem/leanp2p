// Dial one peer and complete one ping.
//
// The argument is a multiaddr whose last component is the expected
// peer id. The host is TCP, Noise, and yamux. A failed setup,
// connection, deadline, or ping exits 1. A bad argument count exits 2.
// The host closes on every return after it exists.
package main

import (
	"context"
	"fmt"
	"os"
	"time"

	"github.com/libp2p/go-libp2p"
	"github.com/libp2p/go-libp2p/core/peer"
	"github.com/libp2p/go-libp2p/p2p/muxer/yamux"
	"github.com/libp2p/go-libp2p/p2p/protocol/ping"
	"github.com/libp2p/go-libp2p/p2p/security/noise"
	"github.com/libp2p/go-libp2p/p2p/transport/tcp"
)

const pingBudget = 20 * time.Second

func main() {
	if len(os.Args) != 2 {
		fmt.Fprintln(os.Stderr, "usage: ping-go <multiaddr>")
		os.Exit(2)
	}
	if err := run(os.Args[1]); err != nil {
		fmt.Fprintf(os.Stderr, "ping-go: %s\n", err)
		os.Exit(1)
	}
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
	select {
	case result, ok := <-results:
		if !ok {
			return fmt.Errorf("ping returned no result")
		}
		if result.Error != nil {
			return fmt.Errorf("ping: %s", result.Error)
		}
		fmt.Printf("PING OK rtt=%s\n", result.RTT)
		return nil
	case <-ctx.Done():
		return fmt.Errorf("ping deadline: %s", ctx.Err())
	}
}
