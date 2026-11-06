// Command yamux-interop is the go side of the yamux interop check
// (packages/net/yamux/docs/PLAN.md). It runs go-yamux v5.1.0, the
// version go-libp2p v0.50 pins, over plain loopback TCP, configured as
// go-libp2p's yamux transport configures it
// (p2p/muxer/yamux/transport.go). Test-only tooling (CLAUDE.md,
// "Dependencies").
//
//	yamux-interop listen        accept one connection as the server, echo every stream
//	yamux-interop dial PORT     connect to 127.0.0.1:PORT as the client, open streams, check the echoes
package main

import (
	"bytes"
	"context"
	"fmt"
	"io"
	"math"
	"net"
	"os"
	"sync"

	"github.com/libp2p/go-yamux/v5"
)

// config mirrors go-libp2p v0.50 p2p/muxer/yamux/transport.go.
func config() *yamux.Config {
	c := yamux.DefaultConfig()
	c.MaxStreamWindowSize = uint32(16 * 1024 * 1024)
	c.LogOutput = io.Discard
	c.ReadBufSize = 0
	c.MaxIncomingStreams = math.MaxUint32
	return c
}

// payload is a deterministic byte pattern of n bytes for stream i.
func payload(i, n int) []byte {
	b := make([]byte, n)
	for k := range b {
		b[k] = byte((k*7 + i*13) % 251)
	}
	return b
}

const streams = 4
const size = 1<<20 + 7 // past the 256 KiB window, so flow control runs

func listen() error {
	l, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		return err
	}
	fmt.Println(l.Addr().(*net.TCPAddr).Port)
	conn, err := l.Accept()
	l.Close()
	if err != nil {
		return err
	}
	s, err := yamux.Server(conn, config(), nil)
	if err != nil {
		return err
	}
	var wg sync.WaitGroup
	// One slot per stream the dialer opens; a dialer that opens more
	// fails the count below before it can fill the channel.
	errs := make(chan error, streams)
	accepted := 0
	for {
		st, err := s.AcceptStream()
		if err != nil {
			break // the peer ended the session
		}
		accepted++
		if accepted > streams {
			st.Reset()
			continue
		}
		wg.Add(1)
		go func() {
			defer wg.Done()
			// Read to the peer's FIN, then answer: the response after
			// the peer's half-close must still arrive.
			data, err := io.ReadAll(st)
			if err != nil {
				errs <- fmt.Errorf("read: %w", err)
				st.Reset()
				return
			}
			if _, err := st.Write(data); err != nil {
				errs <- fmt.Errorf("write: %w", err)
				return
			}
			st.CloseWrite()
		}()
	}
	wg.Wait()
	close(errs)
	for err := range errs {
		return err
	}
	if accepted != streams {
		return fmt.Errorf("accepted %d streams, want %d", accepted, streams)
	}
	return nil
}

func dial(addr string) error {
	conn, err := net.Dial("tcp", addr)
	if err != nil {
		return err
	}
	s, err := yamux.Client(conn, config(), nil)
	if err != nil {
		return err
	}
	if _, err := s.Ping(); err != nil {
		return fmt.Errorf("ping: %w", err)
	}
	var wg sync.WaitGroup
	errs := make(chan error, streams)
	for i := 0; i < streams; i++ {
		wg.Add(1)
		go func(i int) {
			defer wg.Done()
			st, err := s.OpenStream(context.Background())
			if err != nil {
				errs <- fmt.Errorf("open %d: %w", i, err)
				return
			}
			want := payload(i, size)
			if _, err := st.Write(want); err != nil {
				errs <- fmt.Errorf("write %d: %w", i, err)
				return
			}
			st.CloseWrite()
			got, err := io.ReadAll(st)
			if err != nil {
				errs <- fmt.Errorf("read %d: %w", i, err)
				return
			}
			if !bytes.Equal(got, want) {
				errs <- fmt.Errorf("stream %d: echo of %d bytes differs (got %d)", i, len(want), len(got))
			}
			st.Close()
		}(i)
	}
	wg.Wait()
	close(errs)
	for err := range errs {
		return err
	}
	return s.Close()
}

func main() {
	var err error
	switch {
	case len(os.Args) == 2 && os.Args[1] == "listen":
		err = listen()
	case len(os.Args) == 3 && os.Args[1] == "dial":
		err = dial(net.JoinHostPort("127.0.0.1", os.Args[2]))
	default:
		err = fmt.Errorf("usage: yamux-interop listen | dial PORT")
	}
	if err != nil {
		fmt.Fprintln(os.Stderr, "go:", err)
		os.Exit(1)
	}
	fmt.Fprintln(os.Stderr, "go: ok")
}
