// Command noise-interop is the go side of the Noise interop check
// (packages/libp2p/security/docs/PLAN.md). It runs go-libp2p v0.50.0's
// Noise transport (p2p/security/noise), with flynn/noise v1.1.0 under
// it, over plain loopback TCP: no multistream-select, so the check sees
// the Noise handshake and transport frames alone. Test-only tooling
// (CLAUDE.md, "Dependencies").
//
//	noise-interop listen        accept one connection as the responder, echo the bytes
//	noise-interop dial PORT     connect to 127.0.0.1:PORT as the initiator, check the echo
//
// Both sides take fixed Ed25519 identities from 32-byte seeds, so each
// side knows the peer id the other must prove.
package main

import (
	"bytes"
	"context"
	"fmt"
	"io"
	"net"
	"os"

	"github.com/libp2p/go-libp2p/core/crypto"
	"github.com/libp2p/go-libp2p/core/peer"
	"github.com/libp2p/go-libp2p/p2p/security/noise"
)

// The identity seeds: 32 bytes of 'G' for this side, 32 bytes of 'L'
// for the Lean side (Tests/Interop/Noise.lean).
var goSeed = bytes.Repeat([]byte{'G'}, 32)
var leanSeed = bytes.Repeat([]byte{'L'}, 32)

// size is past three full Noise frames of 65519 plaintext bytes, so the
// transport chunks a write into four frames.
const size = 200000

// payload is the deterministic byte pattern both sides build.
func payload(n int) []byte {
	b := make([]byte, n)
	for k := range b {
		b[k] = byte((k*7 + 3) % 251)
	}
	return b
}

// identity is the Ed25519 key of a seed: GenerateEd25519Key reads the
// 32-byte seed from the reader.
func identity(seed []byte) (crypto.PrivKey, error) {
	k, _, err := crypto.GenerateEd25519Key(bytes.NewReader(seed))
	return k, err
}

// transport is go-libp2p's Noise transport with our identity, and the
// peer id the Lean side must prove.
func transport() (*noise.Transport, peer.ID, error) {
	k, err := identity(goSeed)
	if err != nil {
		return nil, "", err
	}
	t, err := noise.New(noise.ID, k, nil)
	if err != nil {
		return nil, "", err
	}
	lk, err := identity(leanSeed)
	if err != nil {
		return nil, "", err
	}
	want, err := peer.IDFromPrivateKey(lk)
	return t, want, err
}

func listen() error {
	t, want, err := transport()
	if err != nil {
		return err
	}
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
	sc, err := t.SecureInbound(context.Background(), conn, "")
	if err != nil {
		return fmt.Errorf("handshake: %w", err)
	}
	if sc.RemotePeer() != want {
		return fmt.Errorf("remote peer %s, want %s", sc.RemotePeer(), want)
	}
	got := make([]byte, size)
	if _, err := io.ReadFull(sc, got); err != nil {
		return fmt.Errorf("read: %w", err)
	}
	if _, err := sc.Write(got); err != nil {
		return fmt.Errorf("write: %w", err)
	}
	// The dialer closes after it has read the echo: an orderly end.
	// ReadAll reads to io.EOF; a single Read may answer (0, nil) first,
	// when it releases the drained buffer of the last frame (rw.go).
	rest, err := io.ReadAll(sc)
	if err != nil || len(rest) != 0 {
		return fmt.Errorf("after the echo: read %d bytes, %v; want the end", len(rest), err)
	}
	return sc.Close()
}

func dial(addr string) error {
	t, want, err := transport()
	if err != nil {
		return err
	}
	conn, err := net.Dial("tcp", addr)
	if err != nil {
		return err
	}
	// SecureOutbound checks that the remote proves `want`.
	sc, err := t.SecureOutbound(context.Background(), conn, want)
	if err != nil {
		return fmt.Errorf("handshake: %w", err)
	}
	data := payload(size)
	if _, err := sc.Write(data); err != nil {
		return fmt.Errorf("write: %w", err)
	}
	got := make([]byte, size)
	if _, err := io.ReadFull(sc, got); err != nil {
		return fmt.Errorf("read: %w", err)
	}
	if !bytes.Equal(got, data) {
		return fmt.Errorf("the echo of %d bytes differs", size)
	}
	return sc.Close()
}

func main() {
	var err error
	switch {
	case len(os.Args) == 2 && os.Args[1] == "listen":
		err = listen()
	case len(os.Args) == 3 && os.Args[1] == "dial":
		err = dial(net.JoinHostPort("127.0.0.1", os.Args[2]))
	default:
		err = fmt.Errorf("usage: noise-interop listen | dial PORT")
	}
	if err != nil {
		fmt.Fprintln(os.Stderr, "go:", err)
		os.Exit(1)
	}
	fmt.Fprintln(os.Stderr, "go: ok")
}
