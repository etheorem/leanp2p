// Command go-fixtures writes the raw-block interoperability fixture.
//
// Invocation, from this directory:
//
//	go run . -o ../../../../Tests/fixtures/snappy-go-v0.0.4.json
//
// The repository root is not a Go module, so the command runs here.
//
// The tool calls snappy.Encode and snappy.Decode. Those functions use one
// raw Snappy block. It does not use a framed stream reader or writer.
// A second run with the same arguments writes the same bytes.
package main

import (
	"bytes"
	"encoding/hex"
	"encoding/json"
	"flag"
	"fmt"
	"os"
	"runtime/debug"

	"github.com/golang/snappy"
)

const (
	generatorPath = "packages/codec/snappy/tools/go-fixtures/main.go"
	modulePath    = "github.com/golang/snappy"
	moduleVersion = "v0.0.4"
	apiName       = "Encode/Decode"
	formatName    = "raw Snappy block, not framed stream"
	nativeRecord  = "native backend regression"
)

// nativeBlocks are raw blocks from the Lean binding Snappy.compress.
// The compressed hex is a regression record for that binding. Decode must
// return the input. A later compressor may emit different bytes.
var nativeBlocks = []struct {
	name       string
	input      []byte
	compressed string
}{
	{
		name:       "text",
		input:      []byte("hello hello hello hello"),
		compressed: "171468656c6c6f20420600",
	},
	{
		name:       "binary",
		input:      []byte{0x00, 0x01, 0x7f, 0x80, 0xfe, 0xff, 0x00, 0x10},
		compressed: "081c00017f80feff0010",
	},
}

type provenance struct {
	GeneratedBy string `json:"generatedBy"`
	Module      string `json:"module"`
	Version     string `json:"version"`
	API         string `json:"api"`
	Format      string `json:"format"`
}

type goCase struct {
	Name          string `json:"name"`
	InputHex      string `json:"inputHex"`
	CompressedHex string `json:"compressedHex"`
}

type nativeCase struct {
	Name          string `json:"name"`
	InputHex      string `json:"inputHex"`
	CompressedHex string `json:"compressedHex"`
	Record        string `json:"record"`
}

type fixture struct {
	Provenance   provenance   `json:"_provenance"`
	GoEncode     []goCase     `json:"goEncode"`
	NativeEncode []nativeCase `json:"nativeEncode"`
}

// pseudoRandom fills n bytes from a fixed xorshift32 state.
func pseudoRandom(n int) []byte {
	state := uint32(0xA5A5A5A5)
	out := make([]byte, n)
	for i := 0; i < n; i++ {
		state ^= state << 13
		state ^= state >> 17
		state ^= state << 5
		out[i] = byte(state)
	}
	return out
}

func goInputs() []goCase {
	inputs := []struct {
		name  string
		input []byte
	}{
		{name: "empty", input: []byte{}},
		{name: "one byte", input: []byte{0x42}},
		{name: "short text", input: []byte("snappy")},
		{name: "repetitive", input: bytes.Repeat([]byte{0x61}, 32)},
		{name: "binary", input: []byte{0x00, 0x01, 0x7f, 0x80, 0xfe, 0xff, 0x00, 0x10}},
		{name: "pseudo-random", input: pseudoRandom(64)},
	}
	cases := make([]goCase, 0, len(inputs))
	for _, item := range inputs {
		compressed := snappy.Encode(nil, item.input)
		decoded, err := snappy.Decode(nil, compressed)
		if err != nil {
			fmt.Fprintf(os.Stderr, "go encode %s: decode failed: %v\n", item.name, err)
			os.Exit(1)
		}
		if !bytes.Equal(decoded, item.input) {
			fmt.Fprintf(os.Stderr, "go encode %s: decoded bytes differ from the input\n", item.name)
			os.Exit(1)
		}
		cases = append(cases, goCase{
			Name:          item.name,
			InputHex:      hex.EncodeToString(item.input),
			CompressedHex: hex.EncodeToString(compressed),
		})
	}
	return cases
}

func nativeInputs() []nativeCase {
	cases := make([]nativeCase, 0, len(nativeBlocks))
	for _, item := range nativeBlocks {
		compressed, err := hex.DecodeString(item.compressed)
		if err != nil {
			fmt.Fprintf(os.Stderr, "native %s: compressed hex is malformed: %v\n", item.name, err)
			os.Exit(1)
		}
		decoded, err := snappy.Decode(nil, compressed)
		if err != nil {
			fmt.Fprintf(os.Stderr, "native %s: decode failed: %v\n", item.name, err)
			os.Exit(1)
		}
		if !bytes.Equal(decoded, item.input) {
			fmt.Fprintf(os.Stderr, "native %s: decoded bytes differ from the input\n", item.name)
			os.Exit(1)
		}
		cases = append(cases, nativeCase{
			Name:          item.name,
			InputHex:      hex.EncodeToString(item.input),
			CompressedHex: item.compressed,
			Record:        nativeRecord,
		})
	}
	return cases
}

// linkedSnappyVersion reads the module that this binary actually linked.
// The version written into the fixture is that version.
func linkedSnappyVersion() string {
	info, ok := debug.ReadBuildInfo()
	if !ok {
		fmt.Fprintln(os.Stderr, "build info is absent")
		os.Exit(1)
	}
	var found *debug.Module
	for _, dep := range info.Deps {
		if dep != nil && dep.Path == modulePath {
			found = dep
			break
		}
	}
	if found == nil {
		fmt.Fprintf(os.Stderr, "%s is not a linked dependency\n", modulePath)
		os.Exit(1)
	}
	if found.Replace != nil {
		fmt.Fprintf(os.Stderr, "%s has a replace directive for %s %s\n",
			modulePath, found.Replace.Path, found.Replace.Version)
		os.Exit(1)
	}
	if found.Version != moduleVersion {
		fmt.Fprintf(os.Stderr, "%s version is %s, expected %s\n",
			modulePath, found.Version, moduleVersion)
		os.Exit(1)
	}
	return found.Version
}

func main() {
	outPath := flag.String("o", "", "output JSON path")
	flag.Parse()
	if *outPath == "" {
		fmt.Fprintln(os.Stderr, "usage: go-fixtures -o Tests/fixtures/snappy-go-v0.0.4.json")
		os.Exit(2)
	}
	version := linkedSnappyVersion()
	body := fixture{
		Provenance: provenance{
			GeneratedBy: generatorPath,
			Module:      modulePath,
			Version:     version,
			API:         apiName,
			Format:      formatName,
		},
		GoEncode:     goInputs(),
		NativeEncode: nativeInputs(),
	}
	encoded, err := json.MarshalIndent(body, "", "  ")
	if err != nil {
		fmt.Fprintf(os.Stderr, "encode json: %v\n", err)
		os.Exit(1)
	}
	encoded = append(encoded, '\n')
	if err := os.WriteFile(*outPath, encoded, 0o644); err != nil {
		fmt.Fprintf(os.Stderr, "write %s: %v\n", *outPath, err)
		os.Exit(1)
	}
}
