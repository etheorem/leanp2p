// interopd — the go-libp2p node for the leanp2p phase 5 transport-interop
// matrix (VECTOR_TEST_PLAN.md, step 25/26). It is the counterpart of the
// Lean `interop` exe: same environment variables, same Redis coordination,
// same stdout JSON — shape-compatible with libp2p/test-plans
// transport-interop.
//
//	transport=tcp muxer=yamux security=noise is_dialer=false ip=<dialable ip>
//	redis_addr=<ip:port> test_timeout_seconds=180 interopd
//
// The listener RPUSHes its multiaddr on `listenerAddr`, then serves
// /ipfs/ping/1.0.0 until the test timeout. The dialer BLPOPs the address,
// connects, pings once and prints
//
//	{"handshakePlusOneRTTMillis": N, "pingRTTMilllis": M}
//
// (keys verbatim from the test plan, including its `pingRTTMilllis` typo).
// Diagnostics go to stderr; any failure exits non-zero.
//
// go-libp2p v0.50 supports tcp + noise + yamux (mplex was removed upstream;
// the script reports those cells as not runnable against this go version).
package main

import (
	"bufio"
	"context"
	"fmt"
	"net"
	"os"
	"strings"
	"strconv"
	"time"

	"github.com/libp2p/go-libp2p"
	"github.com/libp2p/go-libp2p/core/peer"
	"github.com/libp2p/go-libp2p/p2p/muxer/yamux"
	"github.com/libp2p/go-libp2p/p2p/protocol/ping"
	"github.com/libp2p/go-libp2p/p2p/security/noise"
)

func fatalf(format string, args ...any) {
	fmt.Fprintf(os.Stderr, "interopd: "+format+"\n", args...)
	os.Exit(1)
}

// ---------------------------------------------------------------- redis

type redisConn struct {
	c  net.Conn
	br *bufio.Reader
}

func redisDial(addr string) *redisConn {
	c, err := net.DialTimeout("tcp", addr, 10*time.Second)
	if err != nil {
		fatalf("redis dial %s: %v", addr, err)
	}
	return &redisConn{c: c, br: bufio.NewReader(c)}
}

func readLine(r *bufio.Reader) (string, error) {
	line, err := r.ReadString('\n')
	if err != nil {
		return "", err
	}
	// RESP2 inline replies end \r\n
	line = strings.TrimRight(line, "\r\n")
	return line, nil
}

func readReply(r *bufio.Reader) ([]byte, error) {
	line, err := readLine(r)
	if err != nil {
		return nil, err
	}
	if len(line) == 0 {
		return nil, fmt.Errorf("empty reply")
	}
	switch line[0] {
	case '+', '-':
		return []byte(line[1:]), nil
	case ':':
		return []byte(line[1:]), nil
	case '$':
		n, err := strconv.Atoi(line[1:])
		if err != nil {
			return nil, err
		}
		if n < 0 {
			return nil, nil // nil bulk
		}
		buf := make([]byte, n+2)
		if _, err := ioReadFull(r, buf); err != nil {
			return nil, err
		}
		return buf[:n], nil
	case '*':
		n, err := strconv.Atoi(line[1:])
		if err != nil {
			return nil, err
		}
		if n <= 0 {
			return nil, nil
		}
		// return the last element (BLPOP yields [key, value])
		var last []byte
		for i := 0; i < n; i++ {
			if last, err = readReply(r); err != nil {
				return nil, err
			}
		}
		return last, nil
	default:
		return nil, fmt.Errorf("bad reply %q", line)
	}
}

func ioReadFull(r *bufio.Reader, buf []byte) (int, error) {
	total := 0
	for total < len(buf) {
		n, err := r.Read(buf[total:])
		total += n
		if err != nil {
			return total, err
		}
	}
	return total, nil
}

func redisCmd(rc *redisConn, args ...string) ([]byte, error) {
	cmd := fmt.Sprintf("*%d\r\n", len(args))
	for _, a := range args {
		cmd += fmt.Sprintf("$%d\r\n%s\r\n", len(a), a)
	}
	if _, err := rc.c.Write([]byte(cmd)); err != nil {
		return nil, err
	}
	return readReply(rc.br)
}

// ---------------------------------------------------------------- main

func main() {
	req := func(k string) string {
		v := os.Getenv(k)
		if v == "" {
			fatalf("missing environment variable %s", k)
		}
		return v
	}
	transport := req("transport")
	muxer := req("muxer")
	security := req("security")
	isDialer := req("is_dialer") == "true"
	ip := os.Getenv("ip")
	if ip == "" {
		ip = "0.0.0.0"
	}
	redisAddr := os.Getenv("redis_addr")
	if redisAddr == "" {
		redisAddr = "redis:6379"
	}
	timeoutSecs := 180
	if v := os.Getenv("test_timeout_seconds"); v != "" {
		if n, err := strconv.Atoi(v); err == nil {
			timeoutSecs = n
		}
	}

	if transport != "tcp" {
		fatalf("transport %s not supported by this node (tcp only)", transport)
	}
	if security != "noise" {
		fatalf("security %s not supported by this node (noise only)", security)
	}
	// noise.New (not a wrapper var) is the constructor go-libp2p v0.50's
	// own DefaultSecurity uses; fx injects the private key and the muxer
	// list (which is what fills the Noise muxer-preference extension).
	opts := []libp2p.Option{
		libp2p.ListenAddrStrings(fmt.Sprintf("/ip4/%s/tcp/0", ip)),
		libp2p.Security(noise.ID, noise.New),
	}
	switch muxer {
	case "yamux":
		opts = append(opts, libp2p.Muxer(yamux.ID, yamux.DefaultTransport))
	case "mplex":
		fatalf("muxer mplex: go-libp2p v0.50 removed mplex upstream (use yamux)")
	default:
		fatalf("unknown muxer %s", muxer)
	}

	h, err := libp2p.New(opts...)
	if err != nil {
		fatalf("node: %v", err)
	}
	defer h.Close()
	ps := ping.NewPingService(h)

	rc := redisDial(redisAddr)
	defer rc.c.Close()

	if !isDialer {
		addrs := h.Addrs()
		if len(addrs) == 0 {
			fatalf("no listen addrs")
		}
		// publish the /p2p/<id>-suffixed form: the dialer resolves the
		// identity from the suffix (AddrInfoFromString requires it)
		ai := peer.AddrInfo{ID: h.ID(), Addrs: addrs}
		p2pAddrs, err := peer.AddrInfoToP2pAddrs(&ai)
		if err != nil || len(p2pAddrs) == 0 {
			fatalf("p2p addrs: %v", err)
		}
		if _, err := redisCmd(rc, "RPUSH", "listenerAddr", p2pAddrs[0].String()); err != nil {
			fatalf("RPUSH: %v", err)
		}
		fmt.Fprintf(os.Stderr, "interopd: listening at %s\n", p2pAddrs[0])
		time.Sleep(time.Duration(timeoutSecs) * time.Second)
		fmt.Fprintln(os.Stderr, "interopd: test timeout hit")
		os.Exit(1)
	}

	// dialer
	reply, err := redisCmd(rc, "BLPOP", "listenerAddr", strconv.Itoa(timeoutSecs))
	if err != nil {
		fatalf("BLPOP: %v", err)
	}
	if reply == nil {
		fatalf("no listener address (BLPOP timeout)")
	}
	addrStr := string(reply)
	fmt.Fprintf(os.Stderr, "interopd: dialing %s\n", addrStr)
	ai, err := peer.AddrInfoFromString(addrStr)
	if err != nil {
		fatalf("bad multiaddr %s: %v", addrStr, err)
	}
	t0 := time.Now()
	ctx, cancel := context.WithTimeout(context.Background(), time.Duration(timeoutSecs)*time.Second)
	defer cancel()
	if err := h.Connect(ctx, *ai); err != nil {
		fatalf("connect: %v", err)
	}
	res := <-ps.Ping(ctx, ai.ID)
	if res.Error != nil {
		fatalf("ping: %v", res.Error)
	}
	total := time.Since(t0)
	fmt.Printf("{\"handshakePlusOneRTTMillis\": %d, \"pingRTTMilllis\": %d}\n",
		total.Milliseconds(), res.RTT.Milliseconds())
}
