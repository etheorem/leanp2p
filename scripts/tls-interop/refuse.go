// The refusal and no-ALPN runs of the TLS interop check
// (packages/libp2p/security/docs/PLAN.md, unit 2). Each mode builds a
// peer that breaks one rule of the TLS spec, or uses no ALPN, from
// go-libp2p's own identity (p2p/security/tls, crypto.go) with Go's
// crypto/tls under it, and checks how the other side answers:
//
//	dial-noext PORT     a client whose certificate lacks the libp2p extension
//	dial-chain PORT     a client that sends a chain of two certificates
//	dial-noalpn PORT    a client that offers no ALPN, then the echo
//	listen-expired      a server whose certificate has expired
//	listen-refuse       a go-libp2p server that must refuse our client
//	listen-noalpn       a server that selects no ALPN, then the echo
//
// A refusal must reach the peer as the TLS alert bad_certificate, which
// Go reports as "remote error: tls: bad certificate".
package main

import (
	"context"
	"crypto/ecdsa"
	"crypto/elliptic"
	"crypto/rand"
	"crypto/tls"
	"crypto/x509"
	"crypto/x509/pkix"
	"fmt"
	"io"
	"math/big"
	"net"
	"os"
	"strings"
	"time"

	"github.com/libp2p/go-libp2p/core/peer"
	libp2ptls "github.com/libp2p/go-libp2p/p2p/security/tls"
)

// badCertificate is Go's text for a received bad_certificate alert
// (crypto/tls, alert.go).
const badCertificate = "remote error: tls: bad certificate"

// template is go-libp2p's certificate template (crypto.go,
// certTemplate) with the validity window [notBefore, notAfter].
func template(notBefore, notAfter time.Time) (*x509.Certificate, error) {
	bound := big.NewInt(1 << 62)
	sn, err := rand.Int(rand.Reader, bound)
	if err != nil {
		return nil, err
	}
	subject, err := rand.Int(rand.Reader, bound)
	if err != nil {
		return nil, err
	}
	return &x509.Certificate{
		SerialNumber: sn,
		NotBefore:    notBefore,
		NotAfter:     notAfter,
		Subject:      pkix.Name{SerialNumber: subject.String()},
	}, nil
}

// plainCertificate is a self-signed P-256 certificate with no libp2p
// extension: valid TLS, and no libp2p identity.
func plainCertificate() (tls.Certificate, error) {
	key, err := ecdsa.GenerateKey(elliptic.P256(), rand.Reader)
	if err != nil {
		return tls.Certificate{}, err
	}
	tmpl, err := template(time.Now().Add(-time.Hour), time.Now().Add(time.Hour))
	if err != nil {
		return tls.Certificate{}, err
	}
	der, err := x509.CreateCertificate(rand.Reader, tmpl, tmpl, key.Public(), key)
	if err != nil {
		return tls.Certificate{}, err
	}
	return tls.Certificate{Certificate: [][]byte{der}, PrivateKey: key}, nil
}

// config is go-libp2p's tls.Config for our identity, checking that the
// peer proves the Lean side's peer id.
func config(opts ...libp2ptls.IdentityOption) (*tls.Config, error) {
	k, err := identity(goSeed)
	if err != nil {
		return nil, err
	}
	id, err := libp2ptls.NewIdentity(k, opts...)
	if err != nil {
		return nil, err
	}
	lk, err := identity(leanSeed)
	if err != nil {
		return nil, err
	}
	want, err := peer.IDFromPrivateKey(lk)
	if err != nil {
		return nil, err
	}
	conf, _ := id.ConfigForPeer(want)
	return conf, nil
}

// expectAlert passes when err is the peer's bad_certificate alert.
func expectAlert(what string, err error) error {
	if err == nil {
		return fmt.Errorf("%s: no error, want %q", what, badCertificate)
	}
	if !strings.Contains(err.Error(), badCertificate) {
		return fmt.Errorf("%s: %v, want %q", what, err, badCertificate)
	}
	return nil
}

// dialRefused runs a TLS 1.3 client with conf against PORT, and passes
// when the Lean server refuses it. The client finishes its handshake
// before the server checks its certificate (the TLS spec's "Note for
// clients"), so the alert arrives at the first read.
func dialRefused(addr string, conf *tls.Config) error {
	conn, err := net.Dial("tcp", addr)
	if err != nil {
		return err
	}
	c := tls.Client(conn, conf)
	defer c.Close()
	if err := c.Handshake(); err != nil {
		return expectAlert("handshake", err)
	}
	_, err = c.Read(make([]byte, 1))
	return expectAlert("first read", err)
}

func dialNoExt(addr string) error {
	conf, err := config()
	if err != nil {
		return err
	}
	cert, err := plainCertificate()
	if err != nil {
		return err
	}
	conf.Certificates = []tls.Certificate{cert}
	return dialRefused(addr, conf)
}

func dialChain(addr string) error {
	conf, err := config()
	if err != nil {
		return err
	}
	extra, err := plainCertificate()
	if err != nil {
		return err
	}
	// Our libp2p certificate, then one more: a chain of two.
	cert := conf.Certificates[0]
	cert.Certificate = append(append([][]byte{}, cert.Certificate...), extra.Certificate[0])
	conf.Certificates = []tls.Certificate{cert}
	return dialRefused(addr, conf)
}

// echo writes the payload and checks the echo (the client), or reads
// it and echoes it (the server), then ends with an orderly close.
func echo(c *tls.Conn, client bool) error {
	if got := c.ConnectionState().NegotiatedProtocol; got != "" {
		return fmt.Errorf("the handshake selected ALPN %q, want none", got)
	}
	if client {
		data := payload(size)
		if _, err := c.Write(data); err != nil {
			return fmt.Errorf("write: %w", err)
		}
		got := make([]byte, size)
		if _, err := io.ReadFull(c, got); err != nil {
			return fmt.Errorf("read: %w", err)
		}
		if string(got) != string(data) {
			return fmt.Errorf("the echo of %d bytes differs", size)
		}
		return c.Close()
	}
	got := make([]byte, size)
	if _, err := io.ReadFull(c, got); err != nil {
		return fmt.Errorf("read: %w", err)
	}
	if _, err := c.Write(got); err != nil {
		return fmt.Errorf("write: %w", err)
	}
	rest, err := io.ReadAll(c)
	if err != nil || len(rest) != 0 {
		return fmt.Errorf("after the echo: read %d bytes, %v; want the end", len(rest), err)
	}
	return c.Close()
}

func dialNoALPN(addr string) error {
	conf, err := config()
	if err != nil {
		return err
	}
	conf.NextProtos = nil
	conn, err := net.Dial("tcp", addr)
	if err != nil {
		return err
	}
	c := tls.Client(conn, conf)
	if err := c.Handshake(); err != nil {
		return fmt.Errorf("handshake: %w", err)
	}
	return echo(c, true)
}

// acceptOne listens, prints the port, and answers the first connection.
func acceptOne() (net.Conn, error) {
	l, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		return nil, err
	}
	fmt.Println(l.Addr().(*net.TCPAddr).Port)
	conn, err := l.Accept()
	l.Close()
	return conn, err
}

func listenExpired() error {
	// Issued two years back, expired one year back.
	tmpl, err := template(time.Now().Add(-2*365*24*time.Hour), time.Now().Add(-365*24*time.Hour))
	if err != nil {
		return err
	}
	conf, err := config(libp2ptls.WithCertTemplate(tmpl))
	if err != nil {
		return err
	}
	conn, err := acceptOne()
	if err != nil {
		return err
	}
	c := tls.Server(conn, conf)
	defer c.Close()
	return expectAlert("handshake", c.Handshake())
}

// noExtension is go-libp2p's refusal of a certificate without the
// libp2p extension (crypto.go, PubKeyFromCertChain).
const noExtension = "expected certificate to contain the key extension"

// listenRefuse runs go-libp2p's own transport as the server, and passes
// when it refuses the Lean client for the missing extension.
func listenRefuse() error {
	t, _, err := transport()
	if err != nil {
		return err
	}
	conn, err := acceptOne()
	if err != nil {
		return err
	}
	sc, err := t.SecureInbound(context.Background(), conn, "")
	if err == nil {
		sc.Close()
		return fmt.Errorf("the handshake accepted a certificate without the extension")
	}
	if !strings.Contains(err.Error(), noExtension) {
		return fmt.Errorf("handshake: %v, want %q", err, noExtension)
	}
	fmt.Fprintln(os.Stderr, "go: refused:", err)
	return nil
}

func listenNoALPN() error {
	conf, err := config()
	if err != nil {
		return err
	}
	conf.NextProtos = nil
	conn, err := acceptOne()
	if err != nil {
		return err
	}
	c := tls.Server(conn, conf)
	if err := c.Handshake(); err != nil {
		return fmt.Errorf("handshake: %w", err)
	}
	return echo(c, false)
}
