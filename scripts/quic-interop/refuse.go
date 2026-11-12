// The refusal checks of the QUIC interop: go's side of the tls.md
// "Peer Authentication" MUSTs that the Lean host must keep against a go
// peer. They run quic-go directly, below go-libp2p's host, so that go
// can send what a go-libp2p host never sends: no certificate, a
// certificate without the libp2p extension, and a chain of two.
//
//	quic-interop dial-refused PORT  three refused dials, then the dial of `dial`
//	quic-interop listen-sni         accept one Lean dial, and check it sent no SNI
//	quic-interop listen-badcert     present a certificate without the extension
//
// Both sides refuse inside the TLS handshake, so every refusal reaches
// the other side as a TLS alert in a CONNECTION_CLOSE: the transport
// error 0x100 plus the alert (RFC 9001 §4.8).
package main

import (
	"context"
	"crypto/ecdsa"
	"crypto/elliptic"
	"crypto/rand"
	"crypto/tls"
	"crypto/x509"
	"errors"
	"fmt"
	"math/big"
	"net"
	"sync/atomic"
	"time"

	libp2ptls "github.com/libp2p/go-libp2p/p2p/security/tls"
	"github.com/quic-go/quic-go"
)

// alertBadCertificate is the TLS alert of a refused certificate
// (RFC 8446 §6.2).
const alertBadCertificate = 42

// alertCertificateRequired is the alert of a server that aborts when the
// client sends no certificate (RFC 8446 §4.4.2.4).
const alertCertificateRequired = 116

// plainCert is a self-signed ECDSA certificate with no libp2p
// extension. Its window holds now.
func plainCert() (tls.Certificate, error) {
	key, err := ecdsa.GenerateKey(elliptic.P256(), rand.Reader)
	if err != nil {
		return tls.Certificate{}, err
	}
	tmpl := &x509.Certificate{
		SerialNumber: big.NewInt(1),
		NotBefore:    time.Now().Add(-time.Hour),
		NotAfter:     time.Now().Add(time.Hour),
	}
	der, err := x509.CreateCertificate(rand.Reader, tmpl, tmpl, &key.PublicKey, key)
	if err != nil {
		return tls.Certificate{}, err
	}
	return tls.Certificate{Certificate: [][]byte{der}, PrivateKey: key}, nil
}

// goIdentity is go-libp2p's TLS identity for the go seed.
func goIdentity() (*libp2ptls.Identity, error) {
	k, err := identity(goSeed)
	if err != nil {
		return nil, err
	}
	return libp2ptls.NewIdentity(k)
}

// alertOf answers the TLS alert that err carries from the peer, or an
// error when err is no TLS alert of the peer's.
func alertOf(err error) (uint8, error) {
	var te *quic.TransportError
	if !errors.As(err, &te) || !te.Remote || !te.ErrorCode.IsCryptoError() {
		return 0, fmt.Errorf("want a TLS alert from the peer, got %v", err)
	}
	return uint8(te.ErrorCode - 0x100), nil
}

// refusedDial dials the Lean listener with certs and ALPN libp2p, and
// checks that the Lean side ends the attempt with the TLS alert want. A
// client sends its certificate in its last flight, so quic-go may finish
// its handshake before the Lean side refuses: the alert then ends the
// connection.
func refusedDial(name, port string, certs []tls.Certificate, want uint8) error {
	conf := &tls.Config{
		Certificates: certs,
		NextProtos:   []string{"libp2p"},
		MinVersion:   tls.VersionTLS13,
		// The Lean listener's certificate is not under test here.
		InsecureSkipVerify: true,
	}
	ctx, cancel := context.WithTimeout(context.Background(), 10*time.Second)
	defer cancel()
	conn, err := quic.DialAddr(ctx, "127.0.0.1:"+port, conf, &quic.Config{})
	if err == nil {
		select {
		case <-conn.Context().Done():
			err = context.Cause(conn.Context())
		case <-time.After(10 * time.Second):
			conn.CloseWithError(0, "")
			return fmt.Errorf("%s: the Lean listener kept the connection", name)
		}
	}
	alert, aerr := alertOf(err)
	if aerr != nil {
		return fmt.Errorf("%s: %w", name, aerr)
	}
	if alert != want {
		return fmt.Errorf("%s: alert %d, want %d", name, alert, want)
	}
	return nil
}

// dialRefused runs the three refused dials against the Lean listener,
// then the dial of `dial`, which also ends the Lean listener's run.
func dialRefused(port string) error {
	plain, err := plainCert()
	if err != nil {
		return err
	}
	id, err := goIdentity()
	if err != nil {
		return err
	}
	conf, _ := id.ConfigForPeer("")
	two := conf.Certificates[0]
	two.Certificate = append([][]byte{two.Certificate[0]}, plain.Certificate[0])
	// "servers MUST require client authentication": libssl ends the
	// handshake with certificate_required.
	if err := refusedDial("no client certificate", port, nil, alertCertificateRequired); err != nil {
		return err
	}
	// "If this extension is missing, endpoints MUST abort": the Lean
	// check sends bad_certificate.
	if err := refusedDial("no libp2p extension", port, []tls.Certificate{plain}, alertBadCertificate); err != nil {
		return err
	}
	// "Endpoints MUST abort the connection attempt if more than one
	// certificate is received": the Lean TLS engine refuses the chain
	// with bad_certificate, as over TCP.
	if err := refusedDial("a chain of two", port, []tls.Certificate{two}, alertBadCertificate); err != nil {
		return err
	}
	return dial(port)
}

// waitEnd waits for the connection's end and answers its cause.
func waitEnd(conn *quic.Conn) error {
	select {
	case <-conn.Context().Done():
		return context.Cause(conn.Context())
	case <-time.After(60 * time.Second):
		conn.CloseWithError(0, "")
		return fmt.Errorf("the Lean dialer kept the connection")
	}
}

// listenSNI serves go-libp2p's TLS configuration and records the server
// name of the Lean dialer's ClientHello. "clients that only support the
// version of the handshake defined in this document MUST NOT send any
// value in the Server Name Indication" (tls.md).
func listenSNI() error {
	id, err := goIdentity()
	if err != nil {
		return err
	}
	want, err := leanID()
	if err != nil {
		return err
	}
	// quic-go calls GetConfigForClient on its own goroutine.
	var sniSeen atomic.Pointer[string]
	conf := &tls.Config{
		GetConfigForClient: func(hello *tls.ClientHelloInfo) (*tls.Config, error) {
			name := hello.ServerName
			sniSeen.Store(&name)
			c, _ := id.ConfigForPeer(want)
			return c, nil
		},
	}
	l, err := quic.ListenAddr("127.0.0.1:0", conf, &quic.Config{})
	if err != nil {
		return err
	}
	defer l.Close()
	fmt.Println(l.Addr().(*net.UDPAddr).Port)
	ctx, cancel := context.WithTimeout(context.Background(), 60*time.Second)
	defer cancel()
	conn, err := l.Accept(ctx)
	if err != nil {
		return err
	}
	// The Accept answers once the server's handshake has finished. This
	// side closes first, with application error 0, as go-libp2p's Close
	// sends. A close of the dialer's could come before its Finished, and
	// end the connection inside our handshake (RFC 9000 §10.2.3).
	if err := conn.CloseWithError(0, ""); err != nil {
		return fmt.Errorf("close: %w", err)
	}
	sni := sniSeen.Load()
	if sni == nil {
		return fmt.Errorf("no ClientHello reached the server")
	}
	if *sni != "" {
		return fmt.Errorf("the Lean dialer sent the server name %q", *sni)
	}
	return nil
}

// listenBadCert presents a certificate without the libp2p extension, and
// checks that the Lean dialer refuses it with bad_certificate. The Lean
// check runs inside the handshake, before the client's Finished, so the
// server's handshake never completes and a plain listener's Accept never
// answers. The early listener answers once the server has the client's
// transport parameters (quic-go v0.62.0, connection.go, lines 2378 to
// 2383), and the connection's end then carries the alert.
func listenBadCert() error {
	plain, err := plainCert()
	if err != nil {
		return err
	}
	conf := &tls.Config{
		Certificates: []tls.Certificate{plain},
		NextProtos:   []string{"libp2p"},
		MinVersion:   tls.VersionTLS13,
		ClientAuth:   tls.RequireAnyClientCert,
	}
	l, err := quic.ListenAddrEarly("127.0.0.1:0", conf, &quic.Config{})
	if err != nil {
		return err
	}
	defer l.Close()
	fmt.Println(l.Addr().(*net.UDPAddr).Port)
	ctx, cancel := context.WithTimeout(context.Background(), 60*time.Second)
	defer cancel()
	conn, err := l.Accept(ctx)
	if err != nil {
		return err
	}
	alert, err := alertOf(waitEnd(conn))
	if err != nil {
		return err
	}
	if alert != alertBadCertificate {
		return fmt.Errorf("alert %d, want %d", alert, alertBadCertificate)
	}
	return nil
}
