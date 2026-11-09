package main

import (
	"bytes"
	"encoding/hex"
	"encoding/json"
	"fmt"
	"os"

	"github.com/gogo/protobuf/proto"
	pb "github.com/libp2p/go-libp2p-pubsub/pb"
)

func strPtr(s string) *string    { return &s }
func boolPtr(b bool) *bool       { return &b }
func uint64Ptr(u uint64) *uint64 { return &u }

type CaseJSON struct {
	Name      string     `json:"name"`
	Hex       string     `json:"hex"`
	Fields    FieldsJSON `json:"fields"`
	Roundtrip bool       `json:"roundtrip"`
}

type FieldsJSON struct {
	Subscriptions []SubscriptionFields `json:"subscriptions,omitempty"`
	Publish       []PublishFields      `json:"publish,omitempty"`
	Control       *ControlFields       `json:"control,omitempty"`
}

type SubscriptionFields struct {
	Topicid   string `json:"topicid"`
	Subscribe bool   `json:"subscribe"`
}

type PublishFields struct {
	TopicStr      *string `json:"topic_str,omitempty"`
	TopicBytesHex *string `json:"topic_bytes_hex,omitempty"`
	DataHex       *string `json:"data_hex,omitempty"`
	SeqnoHex      *string `json:"seqno_hex,omitempty"`
	SignatureHex  *string `json:"signature_hex,omitempty"`
	KeyHex        *string `json:"key_hex,omitempty"`
}

type ControlFields struct {
	Graft []GraftFields `json:"graft,omitempty"`
	Prune []PruneFields `json:"prune,omitempty"`
	Ihave []IhaveFields `json:"ihave,omitempty"`
	Iwant []IwantFields `json:"iwant,omitempty"`
}

type GraftFields struct {
	TopicBytesHex string `json:"topic_bytes_hex"`
}

type PruneFields struct {
	TopicBytesHex string   `json:"topic_bytes_hex"`
	PeersHexList  []string `json:"peers_hex_list,omitempty"`
	Backoff       *uint64  `json:"backoff,omitempty"`
}

type IhaveFields struct {
	TopicBytesHex string   `json:"topic_bytes_hex"`
	MessageIDsHex []string `json:"message_ids_hex"`
}

type IwantFields struct {
	MessageIDsHex []string `json:"message_ids_hex"`
}

// Command go-rpc-fixtures writes Tests/fixtures/gossipsub-rpc-go.json.
//
// The gossipsub RPC bytes of this tree are pinned against the protobuf
// marshaler of the go implementation that the interop gate runs
// (vendor/test-plans/gossipsub-interop/go-libp2p/go.mod). Each case records the
// marshaled payload, the semantic values the program set, and a roundtrip flag
// that proto.Unmarshal and proto.Equal confirm before the file is written.
//
// Run from this directory with the Go toolchain the gate image carries:
//
//	go run . ../../../../../Tests/fixtures/gossipsub-rpc-go.json
func main() {
	var cases []CaseJSON

	topicTest := "test-topic"
	topicTestHex := hex.EncodeToString([]byte(topicTest))
	dataBasic := []byte{0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07}
	dataBasicHex := hex.EncodeToString(dataBasic)

	msgId1 := []byte{1, 0, 0, 0, 0, 0, 0, 0}
	msgId2 := []byte{2, 0, 0, 0, 0, 0, 0, 0}
	msgId1Hex := hex.EncodeToString(msgId1)
	msgId2Hex := hex.EncodeToString(msgId2)

	// 1. sub-opt-subscribe: two SubOpts, one true, one false, topics "test-topic" and "t"
	{
		rpc := &pb.RPC{
			Subscriptions: []*pb.RPC_SubOpts{
				{Topicid: strPtr("test-topic"), Subscribe: boolPtr(true)},
				{Topicid: strPtr("t"), Subscribe: boolPtr(false)},
			},
		}
		raw, err := proto.Marshal(rpc)
		if err != nil {
			panic(fmt.Sprintf("case 1 marshal failed: %v", err))
		}
		var decoded pb.RPC
		if err := proto.Unmarshal(raw, &decoded); err != nil {
			panic(fmt.Sprintf("case 1 unmarshal failed: %v", err))
		}
		rt := proto.Equal(rpc, &decoded)
		if !rt {
			panic("case 1 roundtrip failed")
		}
		cases = append(cases, CaseJSON{
			Name: "sub-opt-subscribe",
			Hex:  hex.EncodeToString(raw),
			Fields: FieldsJSON{
				Subscriptions: []SubscriptionFields{
					{Topicid: "test-topic", Subscribe: true},
					{Topicid: "t", Subscribe: false},
				},
			},
			Roundtrip: rt,
		})
	}

	// 2. publish-basic: one Message with data 8 bytes 00..07, topic "test-topic", from/seqno/signature/key absent
	var bPublishBasic []byte
	var fieldsPublishBasic PublishFields
	{
		rpc := &pb.RPC{
			Publish: []*pb.Message{
				{
					Topic: strPtr(topicTest),
					Data:  dataBasic,
				},
			},
		}
		raw, err := proto.Marshal(rpc)
		if err != nil {
			panic(fmt.Sprintf("case 2 marshal failed: %v", err))
		}
		bPublishBasic = raw
		var decoded pb.RPC
		if err := proto.Unmarshal(raw, &decoded); err != nil {
			panic(fmt.Sprintf("case 2 unmarshal failed: %v", err))
		}
		rt := proto.Equal(rpc, &decoded)
		if !rt {
			panic("case 2 roundtrip failed")
		}
		fieldsPublishBasic = PublishFields{
			TopicStr:      strPtr(topicTest),
			TopicBytesHex: strPtr(topicTestHex),
			DataHex:       strPtr(dataBasicHex),
		}
		cases = append(cases, CaseJSON{
			Name: "publish-basic",
			Hex:  hex.EncodeToString(raw),
			Fields: FieldsJSON{
				Publish: []PublishFields{fieldsPublishBasic},
			},
			Roundtrip: rt,
		})
	}

	// 3. publish-empty-data: one Message with data absent, topic "test-topic"
	{
		rpc := &pb.RPC{
			Publish: []*pb.Message{
				{
					Topic: strPtr(topicTest),
					Data:  nil,
				},
			},
		}
		raw, err := proto.Marshal(rpc)
		if err != nil {
			panic(fmt.Sprintf("case 3 marshal failed: %v", err))
		}
		var decoded pb.RPC
		if err := proto.Unmarshal(raw, &decoded); err != nil {
			panic(fmt.Sprintf("case 3 unmarshal failed: %v", err))
		}
		rt := proto.Equal(rpc, &decoded)
		if !rt {
			panic("case 3 roundtrip failed")
		}
		cases = append(cases, CaseJSON{
			Name: "publish-empty-data",
			Hex:  hex.EncodeToString(raw),
			Fields: FieldsJSON{
				Publish: []PublishFields{
					{
						TopicStr:      strPtr(topicTest),
						TopicBytesHex: strPtr(topicTestHex),
					},
				},
			},
			Roundtrip: rt,
		})
	}

	// 4. control-graft: control with one Graft for "test-topic"
	{
		rpc := &pb.RPC{
			Control: &pb.ControlMessage{
				Graft: []*pb.ControlGraft{
					{TopicID: strPtr(topicTest)},
				},
			},
		}
		raw, err := proto.Marshal(rpc)
		if err != nil {
			panic(fmt.Sprintf("case 4 marshal failed: %v", err))
		}
		var decoded pb.RPC
		if err := proto.Unmarshal(raw, &decoded); err != nil {
			panic(fmt.Sprintf("case 4 unmarshal failed: %v", err))
		}
		rt := proto.Equal(rpc, &decoded)
		if !rt {
			panic("case 4 roundtrip failed")
		}
		cases = append(cases, CaseJSON{
			Name: "control-graft",
			Hex:  hex.EncodeToString(raw),
			Fields: FieldsJSON{
				Control: &ControlFields{
					Graft: []GraftFields{
						{TopicBytesHex: topicTestHex},
					},
				},
			},
			Roundtrip: rt,
		})
	}

	// 5. control-prune: control with one Prune for "test-topic", backoff 60, one peer id bytes [1,2,3]
	{
		peerBytes := []byte{1, 2, 3}
		rpc := &pb.RPC{
			Control: &pb.ControlMessage{
				Prune: []*pb.ControlPrune{
					{
						TopicID: strPtr(topicTest),
						Backoff: uint64Ptr(60),
						Peers: []*pb.PeerInfo{
							{PeerID: peerBytes},
						},
					},
				},
			},
		}
		raw, err := proto.Marshal(rpc)
		if err != nil {
			panic(fmt.Sprintf("case 5 marshal failed: %v", err))
		}
		var decoded pb.RPC
		if err := proto.Unmarshal(raw, &decoded); err != nil {
			panic(fmt.Sprintf("case 5 unmarshal failed: %v", err))
		}
		rt := proto.Equal(rpc, &decoded)
		if !rt {
			panic("case 5 roundtrip failed")
		}
		cases = append(cases, CaseJSON{
			Name: "control-prune",
			Hex:  hex.EncodeToString(raw),
			Fields: FieldsJSON{
				Control: &ControlFields{
					Prune: []PruneFields{
						{
							TopicBytesHex: topicTestHex,
							Backoff:       uint64Ptr(60),
							PeersHexList:  []string{hex.EncodeToString(peerBytes)},
						},
					},
				},
			},
			Roundtrip: rt,
		})
	}

	// 6. control-ihave: control with one IHave for "test-topic" and two message ids of 8 bytes each
	{
		rpc := &pb.RPC{
			Control: &pb.ControlMessage{
				Ihave: []*pb.ControlIHave{
					{
						TopicID:    strPtr(topicTest),
						MessageIDs: []string{string(msgId1), string(msgId2)},
					},
				},
			},
		}
		raw, err := proto.Marshal(rpc)
		if err != nil {
			panic(fmt.Sprintf("case 6 marshal failed: %v", err))
		}
		var decoded pb.RPC
		if err := proto.Unmarshal(raw, &decoded); err != nil {
			panic(fmt.Sprintf("case 6 unmarshal failed: %v", err))
		}
		rt := proto.Equal(rpc, &decoded)
		if !rt {
			panic("case 6 roundtrip failed")
		}
		cases = append(cases, CaseJSON{
			Name: "control-ihave",
			Hex:  hex.EncodeToString(raw),
			Fields: FieldsJSON{
				Control: &ControlFields{
					Ihave: []IhaveFields{
						{
							TopicBytesHex: topicTestHex,
							MessageIDsHex: []string{msgId1Hex, msgId2Hex},
						},
					},
				},
			},
			Roundtrip: rt,
		})
	}

	// 7. control-iwant: control with one IWant holding the same two ids
	{
		rpc := &pb.RPC{
			Control: &pb.ControlMessage{
				Iwant: []*pb.ControlIWant{
					{
						MessageIDs: []string{string(msgId1), string(msgId2)},
					},
				},
			},
		}
		raw, err := proto.Marshal(rpc)
		if err != nil {
			panic(fmt.Sprintf("case 7 marshal failed: %v", err))
		}
		var decoded pb.RPC
		if err := proto.Unmarshal(raw, &decoded); err != nil {
			panic(fmt.Sprintf("case 7 unmarshal failed: %v", err))
		}
		rt := proto.Equal(rpc, &decoded)
		if !rt {
			panic("case 7 roundtrip failed")
		}
		cases = append(cases, CaseJSON{
			Name: "control-iwant",
			Hex:  hex.EncodeToString(raw),
			Fields: FieldsJSON{
				Control: &ControlFields{
					Iwant: []IwantFields{
						{
							MessageIDsHex: []string{msgId1Hex, msgId2Hex},
						},
					},
				},
			},
			Roundtrip: rt,
		})
	}

	// 8. mixed: subscriptions plus one message plus a control with one Graft, to pin field order
	{
		rpc := &pb.RPC{
			Subscriptions: []*pb.RPC_SubOpts{
				{Topicid: strPtr("test-topic"), Subscribe: boolPtr(true)},
				{Topicid: strPtr("t"), Subscribe: boolPtr(false)},
			},
			Publish: []*pb.Message{
				{
					Topic: strPtr(topicTest),
					Data:  dataBasic,
				},
			},
			Control: &pb.ControlMessage{
				Graft: []*pb.ControlGraft{
					{TopicID: strPtr(topicTest)},
				},
			},
		}
		raw, err := proto.Marshal(rpc)
		if err != nil {
			panic(fmt.Sprintf("case 8 marshal failed: %v", err))
		}
		var decoded pb.RPC
		if err := proto.Unmarshal(raw, &decoded); err != nil {
			panic(fmt.Sprintf("case 8 unmarshal failed: %v", err))
		}
		rt := proto.Equal(rpc, &decoded)
		if !rt {
			panic("case 8 roundtrip failed")
		}
		cases = append(cases, CaseJSON{
			Name: "mixed",
			Hex:  hex.EncodeToString(raw),
			Fields: FieldsJSON{
				Subscriptions: []SubscriptionFields{
					{Topicid: "test-topic", Subscribe: true},
					{Topicid: "t", Subscribe: false},
				},
				Publish: []PublishFields{fieldsPublishBasic},
				Control: &ControlFields{
					Graft: []GraftFields{
						{TopicBytesHex: topicTestHex},
					},
				},
			},
			Roundtrip: rt,
		})
	}

	// 9. unknown-fields: "publish-basic" hex with an extra appended field
	// Field number 9, wire type 2 (length-delimited), payload 4 bytes (0xde, 0xad, 0xbe, 0xef)
	// Tag = (9 << 3) | 2 = 74 = 0x4a, Length = 0x04
	{
		extraField := []byte{0x4a, 0x04, 0xde, 0xad, 0xbe, 0xef}
		raw := append(bytes.Clone(bPublishBasic), extraField...)

		var decoded1 pb.RPC
		if err := proto.Unmarshal(raw, &decoded1); err != nil {
			panic(fmt.Sprintf("case 9 unmarshal failed: %v", err))
		}
		var decoded2 pb.RPC
		if err := proto.Unmarshal(raw, &decoded2); err != nil {
			panic(fmt.Sprintf("case 9 second unmarshal failed: %v", err))
		}
		rt := proto.Equal(&decoded1, &decoded2)
		if !rt {
			panic("case 9 roundtrip failed")
		}
		// Confirm re-marshaling produces exact original bytes including unknown field
		reEncoded, err := proto.Marshal(&decoded1)
		if err != nil || !bytes.Equal(reEncoded, raw) {
			panic("case 9 re-encoding did not match raw bytes")
		}

		cases = append(cases, CaseJSON{
			Name: "unknown-fields",
			Hex:  hex.EncodeToString(raw),
			Fields: FieldsJSON{
				Publish: []PublishFields{fieldsPublishBasic},
			},
			Roundtrip: rt,
		})
	}

	// Verify all roundtrips
	for _, c := range cases {
		if !c.Roundtrip {
			fmt.Fprintf(os.Stderr, "ERROR: case %s roundtrip failed\n", c.Name)
			os.Exit(1)
		}
	}

	outPath := "../../../../../Tests/fixtures/gossipsub-rpc-go.json"
	if len(os.Args) > 1 {
		outPath = os.Args[1]
	}

	provenance := map[string]string{
		"generatedBy": "packages/libp2p/protocols/tools/go-rpc-fixtures/main.go",
		"module":      "github.com/libp2p/go-libp2p-pubsub, pb package",
		"version":     "v0.15.1-0.20260305223556-a01777894f4c",
		"api":         "proto.Marshal of pb.RPC values, then proto.Unmarshal and proto.Equal for the roundtrip field",
		"format":      "the RPC payload of one gossipsub frame, as lowercase hex; the uvarint prefix is Streams.Framing",
		"source":      "vendor/test-plans/gossipsub-interop/go-libp2p/go.mod:8 pins the module version",
	}
	out := struct {
		Provenance map[string]string `json:"_provenance"`
		Cases      []CaseJSON        `json:"cases"`
	}{provenance, cases}
	buf, err := json.MarshalIndent(out, "", "  ")
	if err != nil {
		panic(err)
	}
	buf = append(buf, '\n')

	if err := os.WriteFile(outPath, buf, 0644); err != nil {
		panic(err)
	}
	fmt.Printf("Generated %d cases to %s\n", len(cases), outPath)
}
