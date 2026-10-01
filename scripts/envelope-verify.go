// envelope-verify.go — verify a leanp2p-produced signed envelope (RFC 0002)
// using go-libp2p's `record` package.
//
// Usage: go run envelope-verify.go < envelope_hex
// Reads hex-encoded envelope bytes from stdin, verifies the signature over
// the RFC 0002 input (varint(domain) ++ domain ++ varint(payloadType) ++
// payloadType ++ payload), and prints the decoded peer record fields.
//
// Requires the go module from vendor/go-libp2p (see go.mod).
package main

import (
	"bufio"
	"encoding/hex"
	"fmt"
	"os"

	"github.com/libp2p/go-libp2p/core/peer"
	"github.com/libp2p/go-libp2p/core/record"
)

func main() {
	scanner := bufio.NewScanner(os.Stdin)
	scanner.Scan()
	hexInput := scanner.Text()

	envBytes, err := hex.DecodeString(hexInput)
	if err != nil {
		fmt.Fprintf(os.Stderr, "hex decode: %v\n", err)
		os.Exit(1)
	}

	_, rec, err := record.ConsumeEnvelope(envBytes, peer.PeerRecordEnvelopeDomain)
	if err != nil {
		fmt.Fprintf(os.Stderr, "ConsumeEnvelope: %v\n", err)
		os.Exit(1)
	}

	pr, ok := rec.(*peer.PeerRecord)
	if !ok {
		fmt.Fprintf(os.Stderr, "unexpected record type %T\n", rec)
		os.Exit(1)
	}

	fmt.Printf("peer_id=%s\n", pr.PeerID)
	fmt.Printf("seq=%d\n", pr.Seq)
	for _, a := range pr.Addrs {
		fmt.Printf("addr=%s\n", a)
	}
	fmt.Println("OK")
}
