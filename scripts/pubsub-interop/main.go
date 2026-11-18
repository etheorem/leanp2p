// Command pubsub-peer is the go side of scripts/pubsub-interop.sh: one
// go-libp2p-pubsub v0.19.0 gossipsub node over go-libp2p v0.51.0, on
// loopback TCP.
//
// The node joins the topic "interop" with the message policy of the Lean
// router: no author, no signature, and the message id from the data. It
// prints "ADDR <multiaddr>/p2p/<id>" once it listens, and "GOT <data>" for
// each message from a peer. It publishes "<publish>-<n>" every 200 ms.
// It exits 0 once a message with the prefix "<expect>" arrives, and 1 at
// the timeout.
//
//	pubsub-peer [-connect ADDR] -publish TEXT -expect PREFIX [-timeout S]
//
// With -connect, the node dials ADDR. Without it, it waits for a peer.
package main

import (
	"context"
	"flag"
	"fmt"
	"os"
	"strings"
	"time"

	"github.com/libp2p/go-libp2p"
	pubsub "github.com/libp2p/go-libp2p-pubsub"
	pb "github.com/libp2p/go-libp2p-pubsub/pb"
	"github.com/libp2p/go-libp2p/core/peer"
)

func die(format string, args ...any) {
	fmt.Fprintf(os.Stderr, "pubsub-peer: "+format+"\n", args...)
	os.Exit(1)
}

func main() {
	connect := flag.String("connect", "", "dial this multiaddr")
	publish := flag.String("publish", "from-go", "publish this text and a count every 200 ms")
	expect := flag.String("expect", "from-lean", "exit 0 once a message with this prefix arrives")
	timeout := flag.Int("timeout", 40, "seconds before exit 1")
	flag.Parse()

	ctx, cancel := context.WithTimeout(context.Background(), time.Duration(*timeout)*time.Second)
	defer cancel()
	h, err := libp2p.New(libp2p.ListenAddrStrings("/ip4/127.0.0.1/tcp/0"))
	if err != nil {
		die("host: %v", err)
	}
	defer h.Close()

	ps, err := pubsub.NewGossipSub(ctx, h,
		pubsub.WithMessageSignaturePolicy(pubsub.StrictNoSign),
		pubsub.WithNoAuthor(),
		pubsub.WithMessageIdFn(func(m *pb.Message) string { return string(m.Data) }))
	if err != nil {
		die("gossipsub: %v", err)
	}
	t, err := ps.Join("interop")
	if err != nil {
		die("join: %v", err)
	}
	sub, err := t.Subscribe()
	if err != nil {
		die("subscribe: %v", err)
	}

	for _, a := range h.Addrs() {
		fmt.Printf("ADDR %s/p2p/%s\n", a, h.ID())
	}
	if *connect != "" {
		info, err := peer.AddrInfoFromString(*connect)
		if err != nil {
			die("connect %s: %v", *connect, err)
		}
		if err := h.Connect(ctx, *info); err != nil {
			die("connect %s: %v", *connect, err)
		}
	}

	done := make(chan struct{}, 1)
	go func() {
		for {
			m, err := sub.Next(ctx)
			if err != nil {
				return
			}
			if m.ReceivedFrom == h.ID() {
				continue
			}
			fmt.Printf("GOT %s\n", m.Data)
			if strings.HasPrefix(string(m.Data), *expect) {
				select {
				case done <- struct{}{}:
				default:
				}
			}
		}
	}()

	// The message id is the data, so each publish carries a count: the
	// routers would drop a repeat as a duplicate.
	tick := time.NewTicker(200 * time.Millisecond)
	defer tick.Stop()
	for n := 0; ; n++ {
		select {
		case <-done:
			// A few more rounds, so the peer gets ours too.
			for i := 0; i < 10; i++ {
				_ = t.Publish(ctx, []byte(fmt.Sprintf("%s-%d", *publish, n+i)))
				time.Sleep(200 * time.Millisecond)
			}
			fmt.Println("DONE")
			return
		case <-ctx.Done():
			die("timeout: no message with the prefix %q", *expect)
		case <-tick.C:
			_ = t.Publish(ctx, []byte(fmt.Sprintf("%s-%d", *publish, n)))
		}
	}
}
