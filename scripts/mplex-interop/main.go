// Command mplex-interop is the go side of the mplex interop check
// (packages/libp2p/mux/docs/PLAN.md, unit 2). It runs go-mplex v0.7.0
// over plain loopback TCP. go-libp2p v0.50 dropped mplex from its
// defaults, so go-mplex itself is the peer. Test-only tooling
// (CLAUDE.md, "Dependencies").
//
//	mplex-interop listen        accept one connection, echo every stream
//	mplex-interop dial PORT     connect to 127.0.0.1:PORT, open streams, check the echoes
package main

import (
	"bytes"
	"context"
	"fmt"
	"io"
	"net"
	"os"
	"sync"

	mplex "github.com/libp2p/go-mplex"
)

// payload is a deterministic byte pattern of n bytes for stream i.
func payload(i, n int) []byte {
	b := make([]byte, n)
	for k := range b {
		b[k] = byte((k*7 + i*13) % 251)
	}
	return b
}

const streams = 4
const size = mplex.MaxMessageSize + 7 // past the message cap

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
	s, err := mplex.NewMultiplex(conn, false, nil)
	if err != nil {
		return err
	}
	var wg sync.WaitGroup
	// One slot per stream the dialer opens; a dialer that opens more
	// fails the count below before it can fill the channel.
	errs := make(chan error, streams)
	accepted := 0
	for {
		st, err := s.Accept()
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
			// Read to the peer's close, then answer: the response after
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
	s, err := mplex.NewMultiplex(conn, true, nil)
	if err != nil {
		return err
	}
	var wg sync.WaitGroup
	errs := make(chan error, streams)
	for i := 0; i < streams; i++ {
		wg.Add(1)
		go func(i int) {
			defer wg.Done()
			st, err := s.NewStream(context.Background())
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
		err = fmt.Errorf("usage: mplex-interop listen | dial PORT")
	}
	if err != nil {
		fmt.Fprintln(os.Stderr, "go:", err)
		os.Exit(1)
	}
	fmt.Fprintln(os.Stderr, "go: ok")
}
