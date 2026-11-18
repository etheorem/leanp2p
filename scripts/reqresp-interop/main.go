// Command reqresp-interop is the go side of the req/resp interop check
// (scripts/reqresp-interop.sh). It runs a go-libp2p host with TCP, Noise,
// and yamux, and it frames every payload with prysm's own ssz_snappy
// encoder (beacon-chain/p2p/encoder, SszNetworkEncoder), at the commit
// VECTORS.lock pins. Test-only tooling (CLAUDE.md, "Dependencies").
//
//	reqresp-interop listen        serve the two methods and /test/done, print the port
//	reqresp-interop dial PORT     request both methods from the Lean host, check the answers
//
// The methods, from the consensus networking specs:
//
//   - Status v1 (phase0): an 84-byte request and one 84-byte success chunk,
//     no context bytes;
//   - BeaconBlocksByRange v2 (altair): a 24-byte request (start_slot, count,
//     step), then `count` success chunks, each with a 4-byte ForkDigest
//     context. A request with count 0 draws one InvalidRequest error chunk.
//
// The payloads are opaque test bytes, not real SSZ values: the framing is
// the subject. One block chunk is 70000 bytes, past the 65536 bytes of one
// snappy frame. The chunk layout (result byte, context, then the encoded
// payload) follows prysm's WriteBlockChunk
// (beacon-chain/sync/rpc_chunked_response.go) and createErrorResponse
// (beacon-chain/sync/error.go). The sync package itself pulls in the whole
// beacon node, so the four lines stand here.
//
// The responder waits closePause after its last chunk, then closes its
// write side, and a failed close fails the run. A requester that resets
// the stream at its last chunk fails that close: go-yamux answers a
// CloseWrite after a reset with the reset error. Lighthouse reports the
// same failed close as an IoError and scores it against the requester.
//
// The go-libp2p version is the one prysm's go.mod pins (v0.51.0), so the
// go side is the stack prysm ships.
package main

import (
	"bytes"
	"context"
	"encoding/binary"
	"fmt"
	"io"
	"os"
	"sync"
	"time"

	"github.com/OffchainLabs/prysm/v7/beacon-chain/p2p/encoder"
	"github.com/libp2p/go-libp2p"
	"github.com/libp2p/go-libp2p/core/crypto"
	"github.com/libp2p/go-libp2p/core/host"
	"github.com/libp2p/go-libp2p/core/network"
	"github.com/libp2p/go-libp2p/core/peer"
	"github.com/libp2p/go-libp2p/core/protocol"
	"github.com/libp2p/go-libp2p/p2p/muxer/yamux"
	"github.com/libp2p/go-libp2p/p2p/security/noise"
	"github.com/libp2p/go-libp2p/p2p/transport/tcp"
	ma "github.com/multiformats/go-multiaddr"
)

// The identity seeds: 32 bytes of 'P' for this side, 32 bytes of 'R'
// for the Lean host (Tests/Interop/ReqResp.lean).
var goSeed = bytes.Repeat([]byte{'P'}, 32)
var leanSeed = bytes.Repeat([]byte{'R'}, 32)

const statusID = protocol.ID("/eth2/beacon_chain/req/status/1/ssz_snappy")
const rangeID = protocol.ID("/eth2/beacon_chain/req/beacon_blocks_by_range/2/ssz_snappy")
const doneID = protocol.ID("/test/done")

// The sizes of the check: Status is 84 bytes, the range request 24, and
// the three block chunks carry these sizes.
const statusSize = 84
const rangeRequestSize = 24

var blockSizes = []int{100, 70000, 5}

// digest is the ForkDigest context of every block chunk.
var digest = []byte{1, 2, 3, 4}

// The response codes of phase0 "Responding side".
const (
	codeSuccess        = 0
	codeInvalidRequest = 1
	codeServerError    = 2
)

// errorMessageLimit is ErrorMessage.LIMIT of phase0 "Types".
const errorMessageLimit = 256

// closePause is the wait between the last chunk and the close. On
// loopback the close otherwise leaves before a reset from the requester
// can arrive, and the check would pass by luck.
const closePause = 300 * time.Millisecond

// payload is the deterministic byte pattern both sides build.
func payload(n, salt int) []byte {
	b := make([]byte, n)
	for k := range b {
		b[k] = byte((k*7 + 3 + salt) % 251)
	}
	return b
}

// The request and answer payloads of the check.
func statusRequest() []byte { return payload(statusSize, 9) }
func statusAnswer() []byte  { return payload(statusSize, 1) }
func block(i int) []byte    { return payload(blockSizes[i], 20+i) }

// rangeRequest is BeaconBlocksByRangeRequest: three little-endian
// uint64s, step 1.
func rangeRequest(count uint64) []byte {
	b := make([]byte, rangeRequestSize)
	binary.LittleEndian.PutUint64(b[0:8], 100)
	binary.LittleEndian.PutUint64(b[8:16], count)
	binary.LittleEndian.PutUint64(b[16:24], 1)
	return b
}

// raw is an opaque SSZ value for prysm's encoder: its bytes, and the
// largest size the reader takes (encoder.MaxSizer).
type raw struct {
	b   []byte
	max int
}

func (r *raw) MarshalSSZ() ([]byte, error)             { return r.b, nil }
func (r *raw) MarshalSSZTo(dst []byte) ([]byte, error) { return append(dst, r.b...), nil }
func (r *raw) SizeSSZ() int                            { return len(r.b) }
func (r *raw) UnmarshalSSZ(buf []byte) error           { r.b = append([]byte(nil), buf...); return nil }
func (r *raw) MaxSizeSSZ() int                         { return r.max }

var enc = encoder.SszNetworkEncoder{}

// writeChunk writes one response chunk: the result byte, the context, and
// the payload through prysm's encoder.
func writeChunk(w io.Writer, code byte, ctx []byte, p []byte) error {
	if _, err := w.Write([]byte{code}); err != nil {
		return err
	}
	if len(ctx) > 0 {
		if _, err := w.Write(ctx); err != nil {
			return err
		}
	}
	_, err := enc.EncodeWithMaxLength(w, &raw{b: p})
	return err
}

// finish ends a response: it waits closePause, then closes the write
// side, and it reports a failed close.
func finish(s network.Stream, what string, failed chan<- error) {
	time.Sleep(closePause)
	if err := s.CloseWrite(); err != nil {
		failed <- fmt.Errorf("%s: the close after the last chunk failed: %w", what, err)
	}
}

// chunk is one decoded response chunk.
type chunk struct {
	code    byte
	ctx     []byte
	payload []byte
}

// readChunk reads one response chunk: the result byte, the context on a
// success, and the payload through prysm's decoder. io.EOF before the
// result byte is the end of the response.
func readChunk(r io.Reader, ctxLen, maxLen int) (chunk, error) {
	var code [1]byte
	if _, err := io.ReadFull(r, code[:]); err != nil {
		return chunk{}, err
	}
	c := chunk{code: code[0]}
	max := maxLen
	if c.code == codeSuccess {
		if ctxLen > 0 {
			c.ctx = make([]byte, ctxLen)
			if _, err := io.ReadFull(r, c.ctx); err != nil {
				return chunk{}, fmt.Errorf("context: %w", err)
			}
		}
	} else {
		max = errorMessageLimit
	}
	v := &raw{max: max}
	if err := enc.DecodeWithMaxLength(r, v); err != nil {
		return chunk{}, fmt.Errorf("payload: %w", err)
	}
	c.payload = v.b
	return c, nil
}

// readRequest reads the request payload through prysm's decoder.
func readRequest(s network.Stream, size int) ([]byte, error) {
	v := &raw{max: size}
	if err := enc.DecodeWithMaxLength(s, v); err != nil {
		return nil, err
	}
	return v.b, nil
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

// newHost builds the go host: TCP, Noise, yamux, and nothing else.
func newHost(listen bool) (host.Host, error) {
	k, err := identity(goSeed)
	if err != nil {
		return nil, err
	}
	opts := []libp2p.Option{
		libp2p.Identity(k),
		libp2p.Transport(tcp.NewTCPTransport),
		libp2p.Security(noise.ID, noise.New),
		libp2p.Muxer(yamux.ID, yamux.DefaultTransport),
		libp2p.DisableRelay(),
		libp2p.ResourceManager(&network.NullResourceManager{}),
	}
	if listen {
		opts = append(opts, libp2p.ListenAddrStrings("/ip4/127.0.0.1/tcp/0"))
	} else {
		opts = append(opts, libp2p.NoListenAddrs)
	}
	return libp2p.New(opts...)
}

// serveStatus answers one Status request with one success chunk.
func serveStatus(failed chan<- error) network.StreamHandler {
	return func(s network.Stream) {
		defer s.Close()
		req, err := readRequest(s, statusSize)
		if err != nil {
			failed <- fmt.Errorf("status request: %w", err)
			return
		}
		if !bytes.Equal(req, statusRequest()) {
			writeChunk(s, codeServerError, nil, []byte("unexpected status request"))
			failed <- fmt.Errorf("status request differs")
			return
		}
		if err := writeChunk(s, codeSuccess, nil, statusAnswer()); err != nil {
			failed <- fmt.Errorf("status answer: %w", err)
			return
		}
		finish(s, "status", failed)
	}
}

// serveRange answers a BlocksByRange request: `count` block chunks, or
// one InvalidRequest chunk for a count of 0.
func serveRange(failed chan<- error) network.StreamHandler {
	return func(s network.Stream) {
		defer s.Close()
		req, err := readRequest(s, rangeRequestSize)
		if err != nil {
			failed <- fmt.Errorf("range request: %w", err)
			return
		}
		count := binary.LittleEndian.Uint64(req[8:16])
		if count == 0 {
			if err := writeChunk(s, codeInvalidRequest, nil, []byte("count is zero")); err != nil {
				failed <- fmt.Errorf("range error chunk: %w", err)
				return
			}
			finish(s, "range count 0", failed)
			return
		}
		if !bytes.Equal(req, rangeRequest(uint64(len(blockSizes)))) {
			failed <- fmt.Errorf("range request differs")
			return
		}
		for i := range blockSizes {
			if err := writeChunk(s, codeSuccess, digest, block(i)); err != nil {
				failed <- fmt.Errorf("block chunk %d: %w", i, err)
				return
			}
		}
		finish(s, "range", failed)
	}
}

// tracked runs a handler in the wait group, so listen can wait for every
// close before it decides.
func tracked(wg *sync.WaitGroup, h network.StreamHandler) network.StreamHandler {
	return func(s network.Stream) {
		wg.Add(1)
		defer wg.Done()
		h(s)
	}
}

func listen() error {
	h, err := newHost(true)
	if err != nil {
		return err
	}
	defer h.Close()
	failed := make(chan error, 8)
	done := make(chan struct{})
	// The dialer opens each request after the previous answer, and
	// /test/done after the last, so every Add comes before done closes.
	var wg sync.WaitGroup
	h.SetStreamHandler(statusID, tracked(&wg, serveStatus(failed)))
	h.SetStreamHandler(rangeID, tracked(&wg, serveRange(failed)))
	h.SetStreamHandler(doneID, func(s network.Stream) {
		defer close(done)
		if _, err := s.Write([]byte("bye")); err != nil {
			failed <- fmt.Errorf("done write: %w", err)
			return
		}
		// The dialer closes its host after "bye", which ends this read,
		// with EOF or a reset. Either is the end.
		io.ReadAll(s)
		s.Close()
	})
	port, err := h.Addrs()[0].ValueForProtocol(ma.P_TCP)
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
	wg.Wait()
	select {
	case err := <-failed:
		return err
	default:
		return nil
	}
}

// request opens a stream for `id`, writes the request payload through
// prysm's encoder, half-closes, and reads chunks until the end.
func request(ctx context.Context, h host.Host, p peer.ID, id protocol.ID, req []byte,
	ctxLen, maxLen int) ([]chunk, error) {
	s, err := h.NewStream(ctx, p, id)
	if err != nil {
		return nil, fmt.Errorf("new stream %s: %w", id, err)
	}
	defer s.Close()
	if _, err := enc.EncodeWithMaxLength(s, &raw{b: req}); err != nil {
		return nil, fmt.Errorf("request %s: %w", id, err)
	}
	if err := s.CloseWrite(); err != nil {
		return nil, fmt.Errorf("close write %s: %w", id, err)
	}
	var out []chunk
	for {
		c, err := readChunk(s, ctxLen, maxLen)
		if err == io.EOF {
			return out, nil
		}
		if err != nil {
			return nil, fmt.Errorf("chunk %d of %s: %w", len(out), id, err)
		}
		out = append(out, c)
	}
}

func dial(port string) error {
	want, err := leanID()
	if err != nil {
		return err
	}
	h, err := newHost(false)
	if err != nil {
		return err
	}
	defer h.Close()
	addr, err := ma.NewMultiaddr("/ip4/127.0.0.1/tcp/" + port)
	if err != nil {
		return err
	}
	ctx, cancel := context.WithTimeout(context.Background(), 60*time.Second)
	defer cancel()
	if err := h.Connect(ctx, peer.AddrInfo{ID: want, Addrs: []ma.Multiaddr{addr}}); err != nil {
		return fmt.Errorf("connect: %w", err)
	}
	// Status: one success chunk with the expected answer.
	cs, err := request(ctx, h, want, statusID, statusRequest(), 0, statusSize)
	if err != nil {
		return err
	}
	if len(cs) != 1 || cs[0].code != codeSuccess || !bytes.Equal(cs[0].payload, statusAnswer()) {
		return fmt.Errorf("status: got %d chunks, want one success with the answer", len(cs))
	}
	// BlocksByRange: three block chunks, each with the digest.
	cs, err = request(ctx, h, want, rangeID, rangeRequest(uint64(len(blockSizes))), len(digest), 1<<20)
	if err != nil {
		return err
	}
	if len(cs) != len(blockSizes) {
		return fmt.Errorf("range: got %d chunks, want %d", len(cs), len(blockSizes))
	}
	for i, c := range cs {
		if c.code != codeSuccess || !bytes.Equal(c.ctx, digest) || !bytes.Equal(c.payload, block(i)) {
			return fmt.Errorf("range: chunk %d differs (code %d, %d bytes)", i, c.code, len(c.payload))
		}
	}
	// A count of 0: one InvalidRequest chunk.
	cs, err = request(ctx, h, want, rangeID, rangeRequest(0), len(digest), 1<<20)
	if err != nil {
		return err
	}
	if len(cs) != 1 || cs[0].code != codeInvalidRequest {
		return fmt.Errorf("range count 0: want one InvalidRequest chunk, got %d chunks", len(cs))
	}
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
	return nil
}

func main() {
	var err error
	switch {
	case len(os.Args) == 2 && os.Args[1] == "listen":
		err = listen()
	case len(os.Args) == 3 && os.Args[1] == "dial":
		err = dial(os.Args[2])
	default:
		err = fmt.Errorf("usage: reqresp-interop listen | dial PORT")
	}
	if err != nil {
		fmt.Fprintln(os.Stderr, "go:", err)
		os.Exit(1)
	}
	fmt.Fprintln(os.Stderr, "go: ok")
}
