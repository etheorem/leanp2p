// Command quic-interop is the go side of the QUIC interop check
// (packages/libp2p/quic/docs/PLAN.md, unit 1). It runs go-libp2p
// v0.50.0's own host (libp2p.New) with its QUIC transport only
// (p2p/transport/quic over quic-go), so the two hosts meet on
// quic-v1 with the libp2p TLS handshake inside it. Test-only tooling
// (CLAUDE.md, "Dependencies").
//
//	quic-interop listen        serve /test/echo and /test/done, print the UDP port
//	quic-interop listen-retry  the same, and answer every new connection with a Retry
//	quic-interop dial PORT     dial the Lean host at 127.0.0.1:PORT over QUIC, check the echo
//
// refuse.go adds the refusal modes.
//
// go-libp2p asks its resource manager whether to validate a client's
// address before it accepts (config/config.go, lines 412 to 414). An
// answer of true makes quic-go send a Retry packet (RFC 9000 §8.1.2), so
// listen-retry runs the path a go node under load takes.
//
// The protocols:
//
//   - /test/echo: read the stream to its end, write the bytes back, and
//     close the write side;
//   - /test/done: the dialer opens it last. The listener writes "bye",
//     then reads the stream until the dialer's close of its host ends
//     it, and only then closes its own host. The dialer reads "bye" and
//     closes its host. So the dialer always closes first, and neither
//     side tears down a session the other is still using.
//
// Each side checks that the other proved the peer id of its fixed
// Ed25519 seed. The go host also runs identify on every connection, and
// this side waits for it and checks what the Lean host answered
// (identified).
package main

import (
	"bytes"
	"context"
	"fmt"
	"io"
	"net"
	"os"
	"sync/atomic"
	"time"

	"github.com/libp2p/go-libp2p"
	"github.com/libp2p/go-libp2p/core/crypto"
	"github.com/libp2p/go-libp2p/core/host"
	"github.com/libp2p/go-libp2p/core/network"
	"github.com/libp2p/go-libp2p/core/peer"
	"github.com/libp2p/go-libp2p/core/protocol"
	"github.com/libp2p/go-libp2p/p2p/protocol/identify"
	libp2pquic "github.com/libp2p/go-libp2p/p2p/transport/quic"
	ma "github.com/multiformats/go-multiaddr"
)

// The identity seeds: 32 bytes of 'G' for this side, 32 bytes of 'H'
// for the Lean host (Tests/Interop/Quic.lean).
var goSeed = bytes.Repeat([]byte{'G'}, 32)
var leanSeed = bytes.Repeat([]byte{'H'}, 32)

const echoID = protocol.ID("/test/echo")
const doneID = protocol.ID("/test/done")

// size is 2 MiB. go-libp2p keeps quic-go's initial windows: 512 KiB for
// a stream and 768 KiB for the connection. The Lean host starts with the
// same, so the echo passes only when each receiver sends window updates.
// It is also past the Lean host's 1 MiB cap of unacknowledged bytes.
const size = 2 << 20

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

// leanID is the peer id the Lean host must prove.
func leanID() (peer.ID, error) {
	k, err := identity(leanSeed)
	if err != nil {
		return "", err
	}
	return peer.IDFromPrivateKey(k)
}

// retryManager is the null resource manager, except that it asks the
// transport to validate every client's address. quic-go asks it for each
// Initial that carries no token, and a true answer sends a Retry
// (quic-go v0.62.0, server.go, lines 744 to 753); asked counts the calls.
type retryManager struct {
	network.NullResourceManager
	asked atomic.Int64
}

func (m *retryManager) VerifySourceAddress(net.Addr) bool {
	m.asked.Add(1)
	return true
}

// newHost builds the go host: the QUIC transport and nothing else. QUIC
// brings its own security and muxing, so the host needs no Security or
// Muxer option. A non-nil rm replaces the null resource manager.
func newHost(listen bool, rm network.ResourceManager) (host.Host, error) {
	k, err := identity(goSeed)
	if err != nil {
		return nil, err
	}
	if rm == nil {
		rm = &network.NullResourceManager{}
	}
	opts := []libp2p.Option{
		libp2p.Identity(k),
		libp2p.Transport(libp2pquic.NewTransport),
		libp2p.DisableRelay(),
		libp2p.ResourceManager(rm),
	}
	if listen {
		opts = append(opts, libp2p.ListenAddrStrings("/ip4/127.0.0.1/udp/0/quic-v1"))
	} else {
		opts = append(opts, libp2p.NoListenAddrs)
	}
	return libp2p.New(opts...)
}

// leanAgent is the agent version the Lean host sends in identify
// (Tests/Interop/Quic.lean).
const leanAgent = "leanp2p-interop"

// identified waits until the host's identify of the peer on c has run,
// then checks what the Lean host answered: its agent version, and that
// it serves each of protos. go-libp2p identifies every new connection
// on its own; IdentifyWait returns once that attempt has ended.
func identified(h host.Host, c network.Conn, protos ...protocol.ID) error {
	ids, ok := h.(interface{ IDService() identify.IDService })
	if !ok {
		return fmt.Errorf("the host exposes no identify service")
	}
	select {
	case <-ids.IDService().IdentifyWait(c):
	case <-time.After(10 * time.Second):
		return fmt.Errorf("no identify of the Lean peer within 10 s")
	}
	p := c.RemotePeer()
	agent, err := h.Peerstore().Get(p, "AgentVersion")
	if err != nil {
		return fmt.Errorf("identify recorded no agent version: %w", err)
	}
	if agent != leanAgent {
		return fmt.Errorf("identify recorded agent %v, want %s", agent, leanAgent)
	}
	got, err := h.Peerstore().SupportsProtocols(p, protos...)
	if err != nil {
		return fmt.Errorf("identify protocols: %w", err)
	}
	if len(got) != len(protos) {
		return fmt.Errorf("identify recorded protocols %v, want %v", got, protos)
	}
	return nil
}

// echo serves /test/echo, and checks the peer the stream came from.
func echo(want peer.ID, failed chan<- error) network.StreamHandler {
	return func(s network.Stream) {
		defer s.Close()
		if s.Conn().RemotePeer() != want {
			failed <- fmt.Errorf("echo from %s, want %s", s.Conn().RemotePeer(), want)
			return
		}
		got, err := io.ReadAll(s)
		if err != nil {
			failed <- fmt.Errorf("echo read: %w", err)
			return
		}
		if _, err := s.Write(got); err != nil {
			failed <- fmt.Errorf("echo write: %w", err)
			return
		}
		if err := s.CloseWrite(); err != nil {
			failed <- fmt.Errorf("echo close write: %w", err)
		}
	}
}

func listen(retry bool) error {
	want, err := leanID()
	if err != nil {
		return err
	}
	var rm *retryManager
	var hostRM network.ResourceManager
	if retry {
		rm = &retryManager{}
		hostRM = rm
	}
	h, err := newHost(true, hostRM)
	if err != nil {
		return err
	}
	defer h.Close()
	failed := make(chan error, 4)
	done := make(chan struct{})
	h.SetStreamHandler(echoID, echo(want, failed))
	h.SetStreamHandler(doneID, func(s network.Stream) {
		defer close(done)
		// The Lean dialer serves identify alone.
		if err := identified(h, s.Conn(), identify.ID); err != nil {
			failed <- err
			return
		}
		if _, err := s.Write([]byte("bye")); err != nil {
			failed <- fmt.Errorf("done write: %w", err)
			return
		}
		// The dialer closes its host after "bye", which ends this read,
		// with EOF or a reset. Either is the end.
		io.ReadAll(s)
		s.Close()
	})
	port, err := h.Addrs()[0].ValueForProtocol(ma.P_UDP)
	if err != nil {
		return err
	}
	fmt.Println(port)
	select {
	case <-done:
	case err := <-failed:
		return err
	case <-time.After(60 * time.Second):
		return fmt.Errorf("no /test/done within 60 s")
	}
	select {
	case err := <-failed:
		return err
	default:
	}
	if rm != nil && rm.asked.Load() == 0 {
		return fmt.Errorf("the transport never asked to validate an address, so no Retry was sent")
	}
	return nil
}

func dial(port string) error {
	want, err := leanID()
	if err != nil {
		return err
	}
	h, err := newHost(false, nil)
	if err != nil {
		return err
	}
	defer h.Close()
	addr, err := ma.NewMultiaddr("/ip4/127.0.0.1/udp/" + port + "/quic-v1")
	if err != nil {
		return err
	}
	ctx, cancel := context.WithTimeout(context.Background(), 60*time.Second)
	defer cancel()
	if err := h.Connect(ctx, peer.AddrInfo{ID: want, Addrs: []ma.Multiaddr{addr}}); err != nil {
		return fmt.Errorf("connect: %w", err)
	}
	conns := h.Network().ConnsToPeer(want)
	if len(conns) == 0 {
		return fmt.Errorf("no connection to the Lean peer after the connect")
	}
	// The Lean listener serves the echo, the done, and identify.
	if err := identified(h, conns[0], echoID, doneID, identify.ID); err != nil {
		return err
	}
	// The first id is one the Lean host lacks, so its responder answers
	// `na`, and the negotiation lands on /test/echo.
	s, err := h.NewStream(ctx, want, "/test/unknown", echoID)
	if err != nil {
		return fmt.Errorf("new stream: %w", err)
	}
	if s.Protocol() != echoID {
		return fmt.Errorf("negotiated %s, want %s", s.Protocol(), echoID)
	}
	data := payload(size)
	if _, err := s.Write(data); err != nil {
		return fmt.Errorf("write: %w", err)
	}
	if err := s.CloseWrite(); err != nil {
		return fmt.Errorf("close write: %w", err)
	}
	got, err := io.ReadAll(s)
	if err != nil {
		return fmt.Errorf("read: %w", err)
	}
	if !bytes.Equal(got, data) {
		return fmt.Errorf("the echo of %d bytes differs, got %d", size, len(got))
	}
	s.Close()
	d, err := h.NewStream(ctx, want, doneID)
	if err != nil {
		return fmt.Errorf("done stream: %w", err)
	}
	bye := make([]byte, 3)
	if _, err := io.ReadFull(d, bye); err != nil {
		return fmt.Errorf("done read: %w", err)
	}
	if string(bye) != "bye" {
		return fmt.Errorf("done answered %q, want \"bye\"", bye)
	}
	// The deferred h.Close ends the session; the listener sees it and
	// closes after us.
	return nil
}

func main() {
	var err error
	switch {
	case len(os.Args) == 2 && os.Args[1] == "listen":
		err = listen(false)
	case len(os.Args) == 2 && os.Args[1] == "listen-retry":
		err = listen(true)
	case len(os.Args) == 2 && os.Args[1] == "listen-sni":
		err = listenSNI()
	case len(os.Args) == 2 && os.Args[1] == "listen-badcert":
		err = listenBadCert()
	case len(os.Args) == 3 && os.Args[1] == "dial":
		err = dial(os.Args[2])
	case len(os.Args) == 3 && os.Args[1] == "dial-refused":
		err = dialRefused(os.Args[2])
	default:
		err = fmt.Errorf("usage: quic-interop listen | listen-retry | listen-sni | listen-badcert | dial PORT | dial-refused PORT")
	}
	if err != nil {
		fmt.Fprintln(os.Stderr, "go:", err)
		os.Exit(1)
	}
	fmt.Fprintln(os.Stderr, "go: ok")
}
