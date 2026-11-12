// Command tls-interop is the go side of the TLS interop check
// (packages/libp2p/security/docs/PLAN.md, unit 2). It runs go-libp2p
// v0.50.0's TLS transport (p2p/security/tls) over plain loopback TCP:
// no multistream-select, so the check sees the TLS handshake, the
// certificate checks, and the records alone. Test-only tooling
// (CLAUDE.md, "Dependencies").
//
//	tls-interop listen        accept one connection as the server, echo the bytes
//	tls-interop dial PORT     connect to 127.0.0.1:PORT as the client, check the echo
//
// refuse.go adds the refusal and no-ALPN modes.
//
// The transport offers yamux in ALPN, as go-libp2p does in production,
// so the check also covers the inlined muxer offer that the Lean side
// does not take: both sides land on the ALPN "libp2p".
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
	yamux "github.com/libp2p/go-libp2p/p2p/muxer/yamux"
	tptu "github.com/libp2p/go-libp2p/p2p/net/upgrader"
	libp2ptls "github.com/libp2p/go-libp2p/p2p/security/tls"
)

// The identity seeds: 32 bytes of 'G' for this side, 32 bytes of 'L'
// for the Lean side (Tests/Interop/Tls.lean).
var goSeed = bytes.Repeat([]byte{'G'}, 32)
var leanSeed = bytes.Repeat([]byte{'L'}, 32)

// size is past twelve TLS records of 16384 bytes.
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

// transport is go-libp2p's TLS transport with our identity and the
// yamux muxer in its ALPN offer, and the peer id the Lean side must
// prove.
func transport() (*libp2ptls.Transport, peer.ID, error) {
	k, err := identity(goSeed)
	if err != nil {
		return nil, "", err
	}
	muxers := []tptu.StreamMuxer{{ID: yamux.ID, Muxer: yamux.DefaultTransport}}
	t, err := libp2ptls.New(libp2ptls.ID, k, muxers)
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

// check fails when the connection settled on an inlined muxer: the Lean
// side offers and selects "libp2p" alone.
func check(muxer string) error {
	if muxer != "" {
		return fmt.Errorf("the handshake selected the muxer %q, want none", muxer)
	}
	return nil
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
	if err := check(string(sc.ConnState().StreamMultiplexer)); err != nil {
		return err
	}
	got := make([]byte, size)
	if _, err := io.ReadFull(sc, got); err != nil {
		return fmt.Errorf("read: %w", err)
	}
	if _, err := sc.Write(got); err != nil {
		return fmt.Errorf("write: %w", err)
	}
	// The dialer closes after it has read the echo: an orderly end.
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
	if err := check(string(sc.ConnState().StreamMultiplexer)); err != nil {
		return err
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
	case len(os.Args) == 3 && os.Args[1] == "dial-noext":
		err = dialNoExt(net.JoinHostPort("127.0.0.1", os.Args[2]))
	case len(os.Args) == 3 && os.Args[1] == "dial-chain":
		err = dialChain(net.JoinHostPort("127.0.0.1", os.Args[2]))
	case len(os.Args) == 3 && os.Args[1] == "dial-nocert":
		err = dialNoCert(net.JoinHostPort("127.0.0.1", os.Args[2]))
	case len(os.Args) == 3 && os.Args[1] == "dial-noalpn":
		err = dialNoALPN(net.JoinHostPort("127.0.0.1", os.Args[2]))
	case len(os.Args) == 2 && os.Args[1] == "listen-expired":
		err = listenExpired()
	case len(os.Args) == 2 && os.Args[1] == "listen-refuse":
		err = listenRefuse()
	case len(os.Args) == 2 && os.Args[1] == "listen-noalpn":
		err = listenNoALPN()
	case len(os.Args) == 2 && os.Args[1] == "listen-nosni":
		err = listenNoSNI()
	default:
		err = fmt.Errorf("usage: tls-interop listen | dial PORT | dial-noext PORT | " +
			"dial-chain PORT | dial-nocert PORT | dial-noalpn PORT | listen-expired | " +
			"listen-refuse | listen-noalpn | listen-nosni")
	}
	if err != nil {
		fmt.Fprintln(os.Stderr, "go:", err)
		os.Exit(1)
	}
	fmt.Fprintln(os.Stderr, "go: ok")
}
