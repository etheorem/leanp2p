// capture.go — capture real go-libp2p wire bytes for the leanp2p phase 3
// vector suites (VECTOR_TEST_PLAN.md, phase 3 steps 15/16/20/21).
//
// Modes:
//
//	capture mss        multistream-select traces (full + na + lazy) over net.Pipe
//	capture noise      real go-libp2p Noise initiator <-> deterministic responder
//	                   (flynn/noise, the exact library and suite go-libp2p uses);
//	                   the transcript is only a valid go-libp2p transcript because
//	                   go-libp2p's Transport accepts it live in this run
//	capture identify   two go-libp2p hosts over TCP loopback; /ipfs/id/1.0.0 protobuf
//	capture envelope   go-libp2p sealed PeerRecord envelope (fixed RFC 8032 key)
//
// Output: JSON (stdout, or per-mode file with -o).
package main

import (
	"bytes"
	"context"
	"encoding/binary"
	"encoding/hex"
	"encoding/json"
	"flag"
	"fmt"
	"io"
	"net"
	"sync"
	"os"
	"time"

	"github.com/flynn/noise"
	"golang.org/x/crypto/curve25519"
	"github.com/libp2p/go-libp2p"
	"github.com/libp2p/go-libp2p/core/crypto"
	"github.com/libp2p/go-libp2p/core/peer"
	"github.com/libp2p/go-libp2p/core/record"
	secnoise "github.com/libp2p/go-libp2p/p2p/security/noise"
	mss "github.com/multiformats/go-multistream"
	"github.com/multiformats/go-multiaddr"
)

// ---------------------------------------------------------------- recording

type rec struct {
	Dir string `json:"dir"` // "i2r" (initiator->responder) or "r2i"
	Hex string `json:"hex"`
}

// recorder is a net.Conn that logs every Write per direction.
type recorder struct {
	net.Conn
	dir string
	log *logBuf
}

type logBuf struct {
	mu      sync.Mutex
	entries []rec
}

func (l *logBuf) add(dir string, b []byte) {
	l.mu.Lock()
	defer l.mu.Unlock()
	l.entries = append(l.entries, rec{Dir: dir, Hex: hex.EncodeToString(b)})
}

func (l *logBuf) all() []rec {
	l.mu.Lock()
	defer l.mu.Unlock()
	return append([]rec{}, l.entries...)
}

func (r *recorder) Write(b []byte) (int, error) {
	r.log.add(r.dir, b)
	return r.Conn.Write(b)
}

func h(b []byte) string { return hex.EncodeToString(b) }


// dh25519Public derives the X25519 public key of a private scalar
// (flynn/noise v1.1 exposes no public-key derivation).
func dh25519Public(priv []byte) []byte {
	pub, err := curve25519.X25519(priv, curve25519.Basepoint)
	if err != nil {
		panic(err)
	}
	return pub
}

func must(b []byte, err error) []byte {
	if err != nil {
		panic(err)
	}
	return b
}

func mustJSON(v any, path string) {
	b, err := json.MarshalIndent(v, "", "  ")
	if err != nil {
		panic(err)
	}
	if path == "" {
		os.Stdout.Write(b)
		fmt.Println()
		return
	}
	if err := os.WriteFile(path, b, 0o644); err != nil {
		panic(err)
	}
}

func newPipePair(log *logBuf) (net.Conn, net.Conn) {
	c1, c2 := net.Pipe()
	return &recorder{Conn: c1, dir: "i2r", log: log},
		&recorder{Conn: c2, dir: "r2i", log: log}
}

// ---------------------------------------------------------------- mss mode

type mssTrace struct {
	Full          []rec  `json:"fullTrace"` // supported protocol, full negotiation
	NotSupp       []rec  `json:"naTrace"`   // unsupported proposal answered with na
	Lazy          []rec  `json:"lazyTrace"` // lazy client: header+proposal in one write
	NaWireHex     string `json:"naWireHex"`
	HeaderWireHex string `json:"headerWireHex"`
	LsWireHex     string `json:"lsWireHex"`
}

func captureMSS(path string) {
	var tr mssTrace
	done := make(chan error, 1)

	mkMuxer := func() *mss.MultistreamMuxer[string] {
		m := mss.NewMultistreamMuxer[string]()
		m.AddHandler("/ipfs/kad/1.0.0", func(p string, rwc io.ReadWriteCloser) error { return nil })
		return m
	}

	// --- full negotiation
	fullLog := &logBuf{}
	ci, cr := newPipePair(fullLog)
	go func() {
		_, _, err := mkMuxer().Negotiate(cr)
		done <- err
	}()
	got, err := mss.SelectOneOf[string]([]string{"/ipfs/kad/1.0.0"}, ci)
	if err != nil || got != "/ipfs/kad/1.0.0" {
		panic(fmt.Sprintf("mss full: %v %q", err, got))
	}
	if err := <-done; err != nil {
		panic(err)
	}
	ci.Close()
	cr.Close()
	tr.Full = fullLog.all()

	// --- unsupported protocol: muxer answers na, client falls through to its
	// next candidate
	naLog := &logBuf{}
	ci, cr = newPipePair(naLog)
	go func() {
		_, _, err := mkMuxer().Negotiate(cr)
		done <- err
	}()
	_, err = mss.SelectOneOf[string]([]string{"/nope/9.9.9"}, ci)
	if err == nil {
		panic("mss na: expected failure")
	}
	ci.Close() // the muxer loops for another proposal; EOF ends it
	<-done
	cr.Close()
	tr.NotSupp = naLog.all()

	// --- lazy negotiation: header + proposal coalesced into one write
	lazyLog := &logBuf{}
	ci, cr = newPipePair(lazyLog)
	go func() {
		_, _, err := mkMuxer().Negotiate(cr)
		done <- err
	}()
	lazy := mss.NewMSSelect(ci, "/ipfs/kad/1.0.0")
	// the first use triggers the lazy handshake: header + proposal written
	// back-to-back without waiting for a response (V1 lazy dialer behavior);
	// a reader must run concurrently to consume the muxer's echoes
	readDone := make(chan error, 1)
	go func() {
		buf := make([]byte, 1)
		_, err := lazy.Read(buf)
		readDone <- err
	}()
	<-done
	lazy.Close()
	ci.Close()
	<-readDone
	cr.Close()
	tr.Lazy = lazyLog.all()

	tr.NaWireHex = h([]byte("\x03na\n"))
	tr.HeaderWireHex = h([]byte("\x13/multistream/1.0.0\n"))
	tr.LsWireHex = h([]byte("\x03ls\n"))

	mustJSON(tr, path)
}

// ---------------------------------------------------------------- noise mode

type noiseTrace struct {
	ProtocolName string `json:"protocolName"`
	// initiator side: real go-libp2p Transport (its noise static/ephemeral keys
	// are generated inside go-libp2p and are NOT part of the captured data)
	InitIdentityPubHex string `json:"initIdentityPubHex"`
	InitPeerID         string `json:"initPeerId"`
	// responder side: deterministic (fixed keys, recorded)
	RespIdentityPubHex    string   `json:"respIdentityPubHex"`
	RespPeerIDStr         string   `json:"respPeerId"`
	RespStaticNoiseHex    string   `json:"respStaticNoiseHex"`
	RespEphemeralNoiseHex string   `json:"respEphemeralNoiseHex"`
	RespEphemeralPrivHex  string   `json:"respEphemeralPrivHex"`
	RespPayloadHex        string   `json:"respPayloadHex"`
	ExtensionsMuxers      []string `json:"extensionsMuxers"`
	// transcript: every write in order (wire bytes include the 2-byte BE
	// length framing); handshake messages are the first three writes
	Messages       []rec  `json:"messages"`
	InitPayloadHex string `json:"initPayloadHex"`
}

const payloadSigPrefix = "noise-libp2p-static-key:"

// fixedRandom returns an io.Reader serving exactly one key's worth of entropy,
// making flynn/noise's ephemeral generation deterministic.
func fixedRandom(seed []byte) io.Reader { return bytes.NewReader(seed) }

func varintBytes(n int) []byte {
	var out []byte
	for n >= 0x80 {
		out = append(out, byte(n)|0x80)
		n >>= 7
	}
	return append(out, byte(n))
}

// identPayload encodes the NoiseHandshakePayload protobuf exactly as
// go-libp2p's generateHandshakePayload does (fields 1, 2, optional 4).
func identPayload(identPriv crypto.PrivKey, staticPub []byte, muxers []string) []byte {
	toSign := append([]byte(payloadSigPrefix), staticPub...)
	sig, err := identPriv.Sign(toSign)
	if err != nil {
		panic(err)
	}
	idRaw, err := crypto.MarshalPublicKey(identPriv.GetPublic())
	if err != nil {
		panic(err)
	}
	var ext []byte
	for _, m := range muxers {
		ext = append(ext, 0x12)
		ext = append(ext, varintBytes(len(m))...)
		ext = append(ext, m...)
	}
	var payload []byte
	payload = append(payload, 0x0a)
	payload = append(payload, varintBytes(len(idRaw))...)
	payload = append(payload, idRaw...)
	payload = append(payload, 0x12)
	payload = append(payload, varintBytes(len(sig))...)
	payload = append(payload, sig...)
	if len(ext) > 0 {
		payload = append(payload, 0x22)
		payload = append(payload, varintBytes(len(ext))...)
		payload = append(payload, ext...)
	}
	return payload
}

// checkInitPayload validates the initiator's handshake payload the same way
// go-libp2p's handleRemoteHandshakePayload does.
func checkInitPayload(payload, remoteStatic []byte) error {
	i := 0
	var idKey, sig []byte
	for i < len(payload) {
		key := payload[i]
		i++
		l, n := protoVarint(payload[i:])
		i += n
		val := payload[i : i+int(l)]
		i += int(l)
		switch key {
		case 0x0a:
			idKey = val
		case 0x12:
			sig = val
		}
	}
	pub, err := crypto.UnmarshalPublicKey(idKey)
	if err != nil {
		return err
	}
	msg := append([]byte(payloadSigPrefix), remoteStatic...)
	ok, err := pub.Verify(msg, sig)
	if err != nil || !ok {
		return fmt.Errorf("initiator payload signature invalid")
	}
	return nil
}

func protoVarint(b []byte) (uint64, int) {
	var v uint64
	var s uint
	for i, c := range b {
		v |= uint64(c&0x7f) << s
		if c < 0x80 {
			return v, i + 1
		}
		s += 7
	}
	panic("bad varint")
}

// responder is a deterministic flynn/noise responder replicating go-libp2p's
// noise session: same cipher suite, protocol name, 2-byte BE framing, payload
// protobuf and signature prefix. go-libp2p's real Transport completes the
// handshake against it in this run, which proves byte compatibility. The
// ephemeral key is fixed via the Config.Random entropy source.
func responder(conn net.Conn, staticKeypair noise.DHKey, ephSeed []byte, identPriv crypto.PrivKey, muxers []string) error {
	suite := noise.NewCipherSuite(noise.DH25519, noise.CipherChaChaPoly, noise.HashSHA256)
	hs, err := noise.NewHandshakeState(noise.Config{
		CipherSuite:   suite,
		Random:        fixedRandom(ephSeed),
		Pattern:       noise.HandshakeXX,
		Initiator:     false,
		StaticKeypair: staticKeypair,
		Prologue:      nil,
	})
	if err != nil {
		return err
	}

	readWire := func() ([]byte, error) {
		var lb [2]byte
		if _, err := io.ReadFull(conn, lb[:]); err != nil {
			return nil, err
		}
		l := binary.BigEndian.Uint16(lb[:])
		buf := make([]byte, l)
		if _, err := io.ReadFull(conn, buf); err != nil {
			return nil, err
		}
		return buf, nil
	}
	writeWire := func(bz []byte) error {
		var lb [2]byte
		binary.BigEndian.PutUint16(lb[:], uint16(len(bz)))
		_, err := conn.Write(append(lb[:], bz...)) // recorder logs this write
		return err
	}

	// stage 0: <- e
	m0 := must(readWire())
	if _, _, _, err := hs.ReadMessage(nil, m0); err != nil {
		return fmt.Errorf("stage0: %w", err)
	}

	// stage 1: -> e, ee, s, es + payload
	payload := identPayload(identPriv, staticKeypair.Public, muxers)
	out, _, _, err := hs.WriteMessage(nil, payload)
	if err != nil {
		return fmt.Errorf("stage1 write: %w", err)
	}
	if err := writeWire(out); err != nil {
		return err
	}

	// stage 2: <- s, se + payload; this returns the transport cipher states
	m2 := must(readWire())
	in, cs1, cs2, err := hs.ReadMessage(nil, m2)
	if err != nil {
		return fmt.Errorf("stage2 read: %w", err)
	}
	if len(in) == 0 {
		return fmt.Errorf("stage2: empty payload")
	}
	if err := checkInitPayload(in, hs.PeerStatic()); err != nil {
		return err
	}
	// flynn: cs1 encrypts initiator->responder, cs2 responder->initiator
	enc, dec := cs2, cs1

	// transport phase: decrypt each message, answer with a fixed pong
	for {
		var lb [2]byte
		if _, err := io.ReadFull(conn, lb[:]); err != nil {
			return nil // eof: clean end
		}
		l := binary.BigEndian.Uint16(lb[:])
		buf := make([]byte, l)
		if _, err := io.ReadFull(conn, buf); err != nil {
			return err
		}
		pt, err := dec.Decrypt(nil, nil, buf)
		if err != nil {
			return fmt.Errorf("transport decrypt: %w", err)
		}
		_ = pt
		pong := append([]byte("pong:"), pt...)
		ct, err := enc.Encrypt(nil, nil, pong)
		if err != nil {
			return err
		}
		if err := writeWire(ct); err != nil {
			return err
		}
	}
}

func captureNoise(path string) {
	tr := noiseTrace{
		ProtocolName:   "Noise_XX_25519_ChaChaPoly_SHA256",
		ExtensionsMuxers: []string{"/yamux/1.0.0"},
	}

	// fixed Ed25519 identity keys (RFC 8032 §7.1 TEST 1/2 seeds)
	initSeed, _ := hex.DecodeString("4ccd089b28ff96da9db6c346ec114e0f5b8a319f35aba624da8cf6ed4fb8a6fb")
	respSeed, _ := hex.DecodeString("9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60")
	initPriv, initPub, err := crypto.GenerateEd25519Key(bytes.NewReader(initSeed))
	if err != nil {
		panic(err)
	}
	respPriv, respPub, err := crypto.GenerateEd25519Key(bytes.NewReader(respSeed))
	if err != nil {
		panic(err)
	}
	ipub, _ := initPub.Raw()
	tr.InitIdentityPubHex = h(ipub)
	initID, _ := peer.IDFromPublicKey(initPub)
	respID, _ := peer.IDFromPublicKey(respPub)
	tr.InitPeerID = initID.String()
	tr.RespPeerIDStr = respID.String()

	// fixed responder noise static + ephemeral keys
	staticPriv, _ := hex.DecodeString("1111111111111111111111111111111111111111111111111111111111111111")
	staticPub := dh25519Public(staticPriv)
	ephPriv, _ := hex.DecodeString("2222222222222222222222222222222222222222222222222222222222222222")
	tr.RespStaticNoiseHex = h(staticPriv)
	tr.RespEphemeralNoiseHex = h(dh25519Public(ephPriv))
	tr.RespEphemeralPrivHex = h(ephPriv)

	tr.RespPayloadHex = h(identPayload(respPriv, staticPub, tr.ExtensionsMuxers))

	log := &logBuf{}
	c1, c2 := net.Pipe()
	rec1 := &recorder{Conn: c1, dir: "i2r", log: log}
	rec2 := &recorder{Conn: c2, dir: "r2i", log: log}

	errCh := make(chan error, 1)
	go func() {
		errCh <- responder(rec2,
			noise.DHKey{Private: staticPriv, Public: staticPub},
			ephPriv, respPriv, tr.ExtensionsMuxers)
	}()

	// real go-libp2p noise transport as initiator
	tpt, err := secnoise.New("/noise", initPriv, nil)
	if err != nil {
		panic(err)
	}
	ctx, cancel := context.WithTimeout(context.Background(), 15*time.Second)
	defer cancel()
	secConn, err := tpt.SecureOutbound(ctx, rec1, respID)
	if err != nil {
		panic(fmt.Sprintf("go-libp2p SecureOutbound against deterministic responder: %v", err))
	}
	if secConn.RemotePeer() != respID {
		panic("peer id mismatch: " + secConn.RemotePeer().String())
	}

	// post-handshake: two round trips over the secure channel
	for i := 0; i < 2; i++ {
		msg := fmt.Sprintf("ping-%d", i)
		if _, err := secConn.Write([]byte(msg)); err != nil {
			panic(err)
		}
		buf := make([]byte, 128)
		n, err := secConn.Read(buf)
		if err != nil {
			panic(err)
		}
		if string(buf[:n]) != "pong:"+msg {
			panic(fmt.Sprintf("roundtrip %d: got %q", i, buf[:n]))
		}
	}
	secConn.Close()
	if err := <-errCh; err != nil {
		panic(err)
	}
	tr.Messages = log.all()

	// decrypt the initiator's handshake payload by replaying the responder
	// role with flynn and the known key material
	tr.InitPayloadHex = h(initPayloadFromTranscript(tr))

	mustJSON(tr, path)
}

// initPayloadFromTranscript decrypts recorded message 3 using the known
// responder key material (the initiator's static key rides encrypted in msg3).
func initPayloadFromTranscript(tr noiseTrace) []byte {
	var msgs [][]byte
	for _, m := range tr.Messages {
		b, err := hex.DecodeString(m.Hex)
		if err != nil {
			panic(err)
		}
		msgs = append(msgs, b[2:]) // strip the 2-byte length prefix
	}
	staticPriv, _ := hex.DecodeString(tr.RespStaticNoiseHex)
	staticPub := dh25519Public(staticPriv)
	ephPriv, _ := hex.DecodeString("2222222222222222222222222222222222222222222222222222222222222222")
	suite := noise.NewCipherSuite(noise.DH25519, noise.CipherChaChaPoly, noise.HashSHA256)
	hs, err := noise.NewHandshakeState(noise.Config{
		CipherSuite:   suite,
		Random:        fixedRandom(ephPriv),
		Pattern:       noise.HandshakeXX,
		Initiator:     false,
		StaticKeypair: noise.DHKey{Private: staticPriv, Public: staticPub},
	})
	if err != nil {
		panic(err)
	}
	if _, _, _, err := hs.ReadMessage(nil, msgs[0]); err != nil {
		panic(err)
	}
	respPayload, _ := hex.DecodeString(tr.RespPayloadHex)
	out, _, _, err := hs.WriteMessage(nil, respPayload)
	if err != nil {
		panic(err)
	}
	fmt.Fprintf(os.Stderr, "replay msg2 %d bytes vs recorded %d bytes, equal=%v\n",
		len(out), len(msgs[1]), bytes.Equal(out, msgs[1]))

	for i := range out {
		if i >= len(msgs[1]) || out[i] != msgs[1][i] {
			fmt.Fprintf(os.Stderr, "first diff at byte %d\n", i)
			fmt.Fprintf(os.Stderr, "replay eph: %x\n", out[:32])
			fmt.Fprintf(os.Stderr, "recorded:  %x\n", msgs[1][:32])
			break
		}
	}
	in, _, _, err := hs.ReadMessage(nil, msgs[2])
	if err != nil {
		panic(err)
	}
	return in
}

// ---------------------------------------------------------------- identify

type identifyTrace struct {
	ProtocolVersion string   `json:"protocolVersion"`
	AgentVersion    string   `json:"agentVersion"`
	PublicKeyHex    string   `json:"publicKeyHex"`
	PeerID          string   `json:"peerId"`
	Protocols       []string `json:"protocols"`
	ListenAddrs     []string `json:"listenAddrs"`
	ResponseHex     string   `json:"responseHex"`
}

func captureIdentify(path string) {
	priv, _, err := crypto.GenerateKeyPair(crypto.Ed25519, 256)
	if err != nil {
		panic(err)
	}
	h1, err := libp2p.New(libp2p.Identity(priv), libp2p.ListenAddrStrings("/ip4/127.0.0.1/tcp/0"))
	if err != nil {
		panic(err)
	}
	defer h1.Close()
	h2, err := libp2p.New(libp2p.ListenAddrStrings("/ip4/127.0.0.1/tcp/0"))
	if err != nil {
		panic(err)
	}
	defer h2.Close()
	if err := h2.Connect(context.Background(), peer.AddrInfo{ID: h1.ID(), Addrs: h1.Addrs()}); err != nil {
		panic(err)
	}
	s, err := h2.NewStream(context.Background(), h1.ID(), "/ipfs/id/1.0.0")
	if err != nil {
		panic(err)
	}
	resp, err := io.ReadAll(s)
	if err != nil {
		panic(err)
	}
	s.Close()
	kraw, _ := priv.GetPublic().Raw()
	tr := identifyTrace{
		ProtocolVersion: "/ipfs/1.0.0",
		PublicKeyHex:    h(kraw),
		PeerID:          h1.ID().String(),
		ResponseHex:     h(resp),
	}
	ps := h2.Peerstore()
	if v, err := ps.Get(h1.ID(), "AgentVersion"); err == nil && v != nil {
		tr.AgentVersion = v.(string)
	}
	protos, _ := ps.GetProtocols(h1.ID())
	for _, p := range protos {
		tr.Protocols = append(tr.Protocols, string(p))
	}
	for _, a := range ps.Addrs(h1.ID()) {
		tr.ListenAddrs = append(tr.ListenAddrs, a.String())
	}
	mustJSON(tr, path)
}

// ---------------------------------------------------------------- envelope

type envelopeTrace struct {
	PubKeyHex      string   `json:"pubKeyHex"`
	PeerID         string   `json:"peerId"`
	Domain         string   `json:"domain"`
	PayloadTypeHex string   `json:"payloadTypeHex"`
	PayloadHex     string   `json:"payloadHex"`
	SignatureHex   string   `json:"signatureHex"`
	EnvelopeHex    string   `json:"envelopeHex"`
	Seq            uint64   `json:"seq"`
	Addrs          []string `json:"addrs"`
}

func captureEnvelope(path string) {
	// RFC 8032 §7.1 TEST 2 seed: the same key the leanp2p suite holds
	seed, _ := hex.DecodeString("9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60")
	priv, _, err := crypto.GenerateEd25519Key(bytes.NewReader(seed))
	if err != nil {
		panic(err)
	}
	pubRaw, _ := priv.GetPublic().Raw()

	rec := peer.NewPeerRecord()
	rec.PeerID, _ = peer.IDFromPrivateKey(priv)
	rec.Seq = 1
	addr, err := multiaddr.NewMultiaddr("/ip4/127.0.0.1/tcp/4001")
	if err != nil {
		panic(err)
	}
	rec.Addrs = []multiaddr.Multiaddr{addr}
	env, err := record.Seal(rec, priv)
	if err != nil {
		panic(err)
	}
	envBytes, err := env.Marshal()
	if err != nil {
		panic(err)
	}
	// RFC 0002 signature input (the Envelope type keeps its signature private;
	// ConsumeEnvelope below validates our computation against it)
	var input []byte
	putField := func(b []byte) {
		n := len(b)
		for n >= 0x80 {
			input = append(input, byte(n)|0x80)
			n >>= 7
		}
		input = append(input, byte(n))
		input = append(input, b...)
	}
	putField([]byte(rec.Domain()))
	putField(env.PayloadType)
	putField(env.RawPayload)
	sig, err := priv.Sign(input)
	if err != nil {
		panic(err)
	}
	// sanity: consume it back through go-libp2p
	_, got, err := record.ConsumeEnvelope(envBytes, rec.Domain())
	if err != nil {
		panic(err)
	}
	gotRec, ok := got.(*peer.PeerRecord)
	if !ok || gotRec.Seq != 1 || len(gotRec.Addrs) != 1 {
		panic("envelope roundtrip failed")
	}
	tr := envelopeTrace{
		PubKeyHex:      h(pubRaw),
		PeerID:         rec.PeerID.String(),
		Domain:         rec.Domain(),
		PayloadTypeHex: h(env.PayloadType),
		PayloadHex:     h(env.RawPayload),
		SignatureHex:   h(sig),
		EnvelopeHex:    h(envBytes),
		Seq:            1,
	}
	for _, a := range rec.Addrs {
		tr.Addrs = append(tr.Addrs, a.String())
	}
	mustJSON(tr, path)
}

// ---------------------------------------------------------------- main

func main() {
	mode := flag.String("mode", "", "mss|noise|identify|envelope")
	out := flag.String("o", "", "output file")
	flag.Parse()
	switch *mode {
	case "mss":
		captureMSS(*out)
	case "noise":
		captureNoise(*out)
	case "identify":
		captureIdentify(*out)
	case "envelope":
		captureEnvelope(*out)
	default:
		fmt.Fprintln(os.Stderr, "usage: capture -mode mss|noise|identify|envelope [-o file]")
		os.Exit(2)
	}
}
