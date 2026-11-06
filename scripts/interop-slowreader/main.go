// The slow-reader scenario of the W5.9 gate (packages/cli/docs/PLAN.md,
// "Test milestones (unit 2)"). The program dials the listener that
// published its address under `listenerAddr`, opens a ping stream, and
// writes 32-byte payloads without ever reading the echoes. The peer's
// ping handler then parks on its full send window, stops reading, and
// its receive window fills, so the writes here stall. The scenario
// passes when:
//
//   - the writes stall before maxWrittenBytes: the peer's receive path is
//     bounded (root ARCHITECTURE §5.1);
//   - a second ping over a fresh stream on the same connection completes:
//     one stalled stream does not block the session.
//
// It prints one JSON line to stdout and exits 0 on a pass. It builds
// inside go-libp2p's test-plans module (scripts/interop-matrix.sh), so
// it shares that module's go.mod and go.sum.
package main

import (
	"context"
	"crypto/rand"
	"encoding/json"
	"fmt"
	"log"
	"os"
	"strconv"
	"sync/atomic"
	"time"

	"github.com/go-redis/redis/v8"
	"github.com/libp2p/go-libp2p"
	"github.com/libp2p/go-libp2p/core/peer"
	"github.com/libp2p/go-libp2p/p2p/muxer/yamux"
	"github.com/libp2p/go-libp2p/p2p/protocol/ping"
	"github.com/libp2p/go-libp2p/p2p/security/noise"
	"github.com/libp2p/go-libp2p/p2p/transport/tcp"
	ma "github.com/multiformats/go-multiaddr"
)

// maxWrittenBytes fails the scenario when the writes have not stalled by
// then. The windows between the two peers hold a few MiB at most: the
// peer's yamux receive window (256 KiB, §5.1), our yamux receive window,
// which stays at its initial size because we never read, and the TCP
// buffers of both kernels.
const maxWrittenBytes = 64 << 20

// stallFor is how long the byte count must stand still to count as a stall.
const stallFor = 2 * time.Second

func main() {
	redisAddr := os.Getenv("redis_addr")
	timeout := 60 * time.Second
	if s, err := strconv.Atoi(os.Getenv("test_timeout_seconds")); err == nil {
		timeout = time.Duration(s) * time.Second
	}
	ctx, cancel := context.WithTimeout(context.Background(), timeout)
	defer cancel()

	rc := redis.NewClient(&redis.Options{Addr: redisAddr})
	defer rc.Close()
	val, err := rc.BLPop(ctx, timeout, "listenerAddr").Result()
	if err != nil {
		log.Fatalf("no listener address: %v", err)
	}
	addr, last := ma.SplitLast(ma.StringCast(val[1]))
	pid, err := peer.Decode(last.Value())
	if err != nil {
		log.Fatalf("listener address has no peer id: %v", err)
	}

	h, err := libp2p.New(
		libp2p.Transport(tcp.NewTCPTransport),
		libp2p.Security(noise.ID, noise.New),
		libp2p.Muxer("/yamux/1.0.0", yamux.DefaultTransport),
		libp2p.NoListenAddrs,
	)
	if err != nil {
		log.Fatalf("host: %v", err)
	}
	defer h.Close()
	if err := h.Connect(ctx, peer.AddrInfo{ID: pid, Addrs: []ma.Multiaddr{addr}}); err != nil {
		log.Fatalf("connect: %v", err)
	}

	s, err := h.NewStream(ctx, pid, ping.ID)
	if err != nil {
		log.Fatalf("ping stream: %v", err)
	}
	var written atomic.Int64
	go func() {
		buf := make([]byte, 32)
		for {
			if _, err := rand.Read(buf); err != nil {
				return
			}
			n, err := s.Write(buf)
			written.Add(int64(n))
			if err != nil {
				return
			}
		}
	}()

	// Wait until the count stands still for stallFor, or passes the bound.
	lastCount, lastChange := int64(-1), time.Now()
	for {
		select {
		case <-ctx.Done():
			log.Fatalf("no stall within the timeout: %d bytes written", written.Load())
		case <-time.After(100 * time.Millisecond):
		}
		n := written.Load()
		if n > maxWrittenBytes {
			log.Fatalf("the writes did not stall: %d bytes written", n)
		}
		if n != lastCount {
			lastCount, lastChange = n, time.Now()
		} else if time.Since(lastChange) >= stallFor {
			break
		}
	}
	log.Printf("the writes stalled after %d bytes", lastCount)

	// A fresh stream on the same connection still pings.
	res := <-ping.Ping(ctx, h, pid)
	if res.Error != nil {
		log.Fatalf("second ping while the first stream is stalled: %v", res.Error)
	}
	out, _ := json.Marshal(struct {
		StalledAfterBytes int64   `json:"stalledAfterBytes"`
		PingRTTMillis     float32 `json:"pingRTTMillis"`
	}{lastCount, float32(res.RTT.Microseconds()) / 1000})
	fmt.Println(string(out))
	s.Reset()
}
