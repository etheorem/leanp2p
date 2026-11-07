// Command reqresp-fixtures writes Tests/fixtures/reqresp-snappy-go.json:
// ssz_snappy payloads as a consensus client writes them.
//
// The writer follows prysm's SszNetworkEncoder.EncodeWithMaxLength
// (beacon-chain/p2p/encoder/ssz.go): the protobuf varint of the raw
// length, then the bytes through snappy.NewBufferedWriter and Close.
// binary.PutUvarint writes the same bytes as proto.EncodeVarint for a
// uint64. The snappy module is the version prysm's go.mod pins.
//
// Run from the repo root:
//
//	cd scripts/reqresp-fixtures && go run . > ../../Tests/fixtures/reqresp-snappy-go.json
package main

import (
	"bytes"
	"encoding/binary"
	"encoding/hex"
	"encoding/json"
	"os"
	"runtime/debug"

	"github.com/golang/snappy"
)

type fixture struct {
	Name    string `json:"name"`
	Note    string `json:"note"`
	Payload string `json:"payload"`
	Wire    string `json:"wire"`
}

func encode(payload []byte) []byte {
	var out bytes.Buffer
	var prefix [binary.MaxVarintLen64]byte
	out.Write(prefix[:binary.PutUvarint(prefix[:], uint64(len(payload)))])
	w := snappy.NewBufferedWriter(&out)
	if _, err := w.Write(payload); err != nil {
		panic(err)
	}
	if err := w.Close(); err != nil {
		panic(err)
	}
	return out.Bytes()
}

// noise is a fixed linear congruential sequence, so a rerun gives the
// same bytes.
func noise(n int) []byte {
	out := make([]byte, n)
	x := uint32(1)
	for i := range out {
		x = x*1664525 + 1013904223
		out[i] = byte(x >> 24)
	}
	return out
}

func main() {
	repetitive := bytes.Repeat([]byte("ssz_snappy req/resp chunk "), 4000)
	cases := []struct {
		name, note string
		payload    []byte
	}{
		{"empty", "n = 0: the writer emits no frame, so the wire is the prefix alone", []byte{}},
		{"text", "one compressed or uncompressed chunk after the stream identifier", []byte("the req/resp payload of ssz_snappy")},
		{"repetitive", "104000 bytes: two data chunks, each a block with copy elements", repetitive},
		{"noise", "70000 incompressible bytes: uncompressed chunks", noise(70000)},
	}
	version := "unknown"
	if info, ok := debug.ReadBuildInfo(); ok {
		for _, d := range info.Deps {
			if d.Path == "github.com/golang/snappy" {
				version = d.Version
			}
		}
	}
	doc := map[string]any{
		"_provenance": map[string]string{
			"generatedBy": "scripts/reqresp-fixtures",
			"tool":        "github.com/golang/snappy " + version,
			"writer":      "prysm beacon-chain/p2p/encoder/ssz.go EncodeWithMaxLength: varint, then snappy.NewBufferedWriter",
		},
		"cases": func() []fixture {
			var fs []fixture
			for _, c := range cases {
				fs = append(fs, fixture{c.name, c.note, hex.EncodeToString(c.payload), hex.EncodeToString(encode(c.payload))})
			}
			return fs
		}(),
	}
	enc := json.NewEncoder(os.Stdout)
	enc.SetIndent("", " ")
	if err := enc.Encode(doc); err != nil {
		panic(err)
	}
}
