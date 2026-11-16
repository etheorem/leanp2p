// mss-capture records go-multistream's answer to a first message that is
// not the multistream header, and writes it as a test vector.
//
// The exchange is go-multistream's own TestInvalidProtocol
// (multistream_test.go, lines 294 to 318, at v0.6.1): a muxer negotiates
// on one end of a net.Pipe, and NewMultistream on the other end sends a
// protocol id with no header. The muxer sends its header, reads the
// first message, and fails with ErrIncorrectVersion.
//
// Usage: go run . [-o file]. With no -o, the JSON goes to stdout. The
// test vector comes from the repository root with
//
//	go -C scripts/mss-capture run . -o ../../Tests/vectors/mss-go-invalid.json
package main

import (
	"encoding/hex"
	"encoding/json"
	"errors"
	"flag"
	"fmt"
	"io"
	"net"
	"os"
	"sync"

	mss "github.com/multiformats/go-multistream"
)

// The id that the client sends in place of the header, as the go test.
const wrongID = "/THIS_IS_WRONG"

type rec struct {
	Dir string `json:"dir"` // "i2r" (initiator to responder) or "r2i"
	Hex string `json:"hex"`
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

// recorder is a net.Conn that logs every Write with its direction.
type recorder struct {
	net.Conn
	dir string
	log *logBuf
}

func (r *recorder) Write(b []byte) (int, error) {
	r.log.add(r.dir, b)
	return r.Conn.Write(b)
}

type provenance struct {
	Repo         string `json:"repo"`
	Commit       string `json:"commit"`
	Version      string `json:"version"`
	UpstreamTest string `json:"upstreamTest"`
	CapturedBy   string `json:"capturedBy"`
	ExtractedBy  string `json:"extractedBy"`
	Note         string `json:"note"`
}

type vector struct {
	Provenance     provenance `json:"_provenance"`
	InvalidTrace   []rec      `json:"invalidTrace"`
	ResponderError string     `json:"responderError"`
}

func main() {
	out := flag.String("o", "", "the output file; stdout when empty")
	flag.Parse()

	log := &logBuf{}
	c1, c2 := net.Pipe()
	ci := &recorder{Conn: c1, dir: "i2r", log: log}
	cr := &recorder{Conn: c2, dir: "r2i", log: log}

	mux := mss.NewMultistreamMuxer[string]()
	mux.AddHandler("/ipfs/kad/1.0.0", func(string, io.ReadWriteCloser) error { return nil })
	done := make(chan error, 1)
	go func() {
		_, _, err := mux.Negotiate(cr)
		cr.Close()
		done <- err
	}()

	// The first read runs the lazy handshake: the client writes its id
	// with no header, then reads the muxer's header and fails.
	ms := mss.NewMultistream[string](ci, wrongID)
	if _, err := ms.Read([]byte{0}); err == nil {
		fail("the client read should fail")
	}
	// The muxer ends first, as in the go test. A close before it reads
	// the first message would give it EOF in place of the wrong id.
	err := <-done
	ci.Close()
	if !errors.Is(err, mss.ErrIncorrectVersion) {
		fail(fmt.Sprintf("the muxer should fail with ErrIncorrectVersion, got %v", err))
	}

	v := vector{
		Provenance: provenance{
			Repo:         "https://github.com/multiformats/go-multistream",
			Commit:       "c4e1c126f1dad980e071b21b3bdf87e197953f74",
			Version:      "v0.6.1",
			UpstreamTest: "TestInvalidProtocol (multistream_test.go, lines 294 to 318)",
			CapturedBy:   "scripts/mss-capture (net.Pipe, host Go toolchain)",
			ExtractedBy:  "scripts/mss-capture",
			Note: "each entry is one Write. The two directions run at once, " +
				"so their relative order is not fixed. Each direction keeps its own order.",
		},
		InvalidTrace:   log.all(),
		ResponderError: err.Error(),
	}
	b, merr := json.MarshalIndent(v, "", " ")
	if merr != nil {
		fail(merr.Error())
	}
	b = append(b, '\n')
	if *out == "" {
		os.Stdout.Write(b)
		return
	}
	if werr := os.WriteFile(*out, b, 0o644); werr != nil {
		fail(werr.Error())
	}
}

func fail(msg string) {
	fmt.Fprintln(os.Stderr, "mss-capture:", msg)
	os.Exit(1)
}
