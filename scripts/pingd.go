// pingd — a minimal go-libp2p node for the leanp2p phase 4 loopback ping
// interop (VECTOR_TEST_PLAN.md, phase 4 step 24). Run inside docker with
// --network host so 127.0.0.1 is the host's loopback.
//
//	pingd -mode serve -port 45001     start a host, print "ADDR <ma> <id>"
//	                                  on stdout, serve /ipfs/ping/1.0.0 until
//	                                  stdin EOF
//	pingd -mode dial -addr <ma>       connect to the peer (multiaddr with
//	                                  /p2p/), do one ping round trip, print
//	                                  "PING OK rtt=<dur>", exit 0
//
// Defaults: tcp transport, /noise security, yamux muxer (go-libp2p v0.50
// defaults) - the same stack leanp2p upgrades with.
package main

import (
	"context"
	"flag"
	"fmt"
	"os"
	"time"

	"github.com/libp2p/go-libp2p"
	"github.com/libp2p/go-libp2p/core/peer"
	"github.com/libp2p/go-libp2p/p2p/protocol/ping"
)

func main() {
	mode := flag.String("mode", "", "serve|dial")
	port := flag.Int("port", 0, "serve: tcp port to listen on")
	addr := flag.String("addr", "", "dial: peer multiaddr (with /p2p/ suffix)")
	flag.Parse()

	h, err := libp2p.New(libp2p.ListenAddrStrings(fmt.Sprintf("/ip4/127.0.0.1/tcp/%d", *port)))
	if err != nil {
		panic(err)
	}
	defer h.Close()
	_ = ping.NewPingService(h)

	switch *mode {
	case "serve":
		fmt.Printf("ADDR %s %s\n", h.Addrs()[0], h.ID())
		// block until stdin closes (the driver drops the pipe)
		buf := make([]byte, 16)
		for {
			if _, err := os.Stdin.Read(buf); err != nil {
				return
			}
		}
	case "dial":
		ai, err := peer.AddrInfoFromString(*addr)
		if err != nil {
			panic(err)
		}
		ctx, cancel := context.WithTimeout(context.Background(), 30*time.Second)
		defer cancel()
		if err := h.Connect(ctx, *ai); err != nil {
			panic(fmt.Sprintf("connect: %v", err))
		}
		res := <-ping.Ping(ctx, h, ai.ID)
		if res.Error != nil {
			panic(fmt.Sprintf("ping: %v", res.Error))
		}
		fmt.Printf("PING OK rtt=%s\n", res.RTT)
	default:
		fmt.Fprintln(os.Stderr, "usage: pingd -mode serve -port N | -mode dial -addr <ma>")
		os.Exit(2)
	}
}
