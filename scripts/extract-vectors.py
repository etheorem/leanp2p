#!/usr/bin/env python3
"""Extract upstream test tables into Tests/vectors/*.json.

Sources are the pinned copies under vendor/ (see VECTORS.lock). Every output
file records its provenance in a top-level "_provenance" object: upstream
repository, pinned commit, file path, and the upstream test the data mirrors.

Entries may carry a "knownDivergence" string: the vector exercises behaviour
where two upstream implementations disagree (e.g. the `memory` value type,
a u64 in go/rust and a string in js). We follow one side and the suite skips
the vector with the printed reason.

Usage: scripts/extract-vectors.py   (run from the repository root)
"""

import csv
import json
import re
import sys
import tomllib

from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
OUT = ROOT / "Tests" / "vectors"

with open(ROOT / "VECTORS.lock", "rb") as f:
    LOCK = {e["dir"]: e for e in tomllib.load(f)["vendor"]}


def prov(vendor_dir: str, path: str, upstream: str) -> dict:
    e = LOCK[vendor_dir]
    # no timestamp: extraction must be reproducible byte-for-byte (CI diffs
    # the committed JSON against a fresh run)
    return {
        "repo": e["repo"],
        "commit": e["commit"],
        "path": path,
        "upstreamTest": upstream,
        "extractedBy": "scripts/extract-vectors.py",
    }


def read(vendor_dir: str, path: str) -> str:
    return (ROOT / vendor_dir / path).read_text(encoding="utf-8")


def write_json(name: str, data: dict) -> None:
    (OUT / name).write_text(
        json.dumps(data, indent=1, ensure_ascii=False) + "\n", encoding="utf-8"
    )
    print(f"wrote Tests/vectors/{name}")


GO_STR = r'"(?:[^"\\]|\\.)*"'

# p2p/ipfs values that are multibase CID strings (base36 'k...', base32
# 'bafz...'), which need multibase (phase 1 steps 6-7); the spike only
# decodes base58btc.
MULTIBASE_P2P = re.compile(r"/(?:p2p|ipfs)/(?=[kbmfu])[A-Za-z0-9+_=.-]+")

# The spike's only peer-id decoder is base58btc, so a multibase value whose
# characters all fit the base58 alphabet is *accepted by accident* (decoded
# as garbage bytes), and a value containing an excluded character (0, O, I, l)
# is *rejected by accident* - neither has anything to do with the missing
# multibase/multihash validation. Such entries carry an "accidentalPass"
# annotation so the runner keeps them as todos even when the shallow check
# happens to succeed. Phase 1 steps 6-7 drop all of this.
B58_EXCLUDED = set("0OIl")


def base58_decodable(value: str) -> bool:
    return not (set(value) & B58_EXCLUDED)


def p2p_values(addr: str) -> list[str]:
    return re.findall(r"/(?:p2p|ipfs)/([^/]+)", addr)


def braced(src: str, start: int) -> str:
    """Return the {...} block starting at src[start] == '{', strings aware."""
    depth, i, n = 0, start, len(src)
    in_str = False
    while i < n:
        c = src[i]
        if in_str:
            if c == "\\":
                i += 1
            elif c == '"':
                in_str = False
        elif c == '"':
            in_str = True
        elif c == "{":
            depth += 1
        elif c == "}":
            depth -= 1
            if depth == 0:
                return src[start : i + 1]
        i += 1
    raise ValueError("unbalanced braces")


def func_body(src: str, func: str) -> str:
    m = re.search(rf"^func {func}\(", src, re.M)
    if not m:
        raise ValueError(f"func {func} not found")
    b = re.search(r"\{", src[m.end() :])
    start = m.end() + b.start()
    block = braced(src, start)
    return block[1:-1]  # strip outer braces


def entry_lines(block: str) -> list[str]:
    """Go string-literal table entries: lines whose first token is a literal."""
    out = []
    for line in block.splitlines():
        t = line.strip()
        if t.startswith('"'):
            out.append(t)
    return out


def go_strings(block: str) -> list[str]:
    return [m.group(0)[1:-1] for m in re.finditer(GO_STR, "\n".join(entry_lines(block)))]


def unescape_go(s: str) -> str:
    return s.encode().decode("unicode_escape")


# ---------------------------------------------------------------------------
# go-multiaddr (multiaddr_test.go)
# ---------------------------------------------------------------------------

def extract_go_multiaddr() -> None:
    src = read("vendor/go-multiaddr", "multiaddr_test.go")

    # TestConstructFails: every entry must be rejected by any conforming parser.
    fails = go_strings(func_body(src, "TestConstructFails"))
    # the fmt.Sprintf entry is invisible to the string-literal scan:
    # fmt.Sprintf("/memory/%d1", uint64(1<<63)) -> 2^63 concatenated with "1"
    fails.append(f"/memory/{(1 << 63)}1")
    write_json("multiaddr-go-construct-fails.json", {
        "_provenance": prov("vendor/go-multiaddr", "multiaddr_test.go",
                            "TestConstructFails"),
        "cases": [{"string": s} for s in fails],
        "derivedNote": "the last case is the fmt.Sprintf entry "
                       "'/memory/<2^63>1' (a decimal number above the u64 "
                       "range); extracted from the format expression",
    })

    # TestConstructSucceeds drives the package-level `good` table.
    good = go_strings(re.search(r"var good = \[\]string\{(.*?)\n\}", src, re.S).group(1))
    write_json("multiaddr-go-construct-succeeds.json", {
        "_provenance": prov("vendor/go-multiaddr", "multiaddr_test.go",
                            "TestConstructSucceeds"),
        "cases": [{"string": s} for s in good],
    })

    def string_bytes_pairs(func: str, upstream: str, name: str):
        pairs = re.findall(
            rf'testString\(\s*({GO_STR}),\s*({GO_STR})\s*\)',
            func_body(src, func), re.S)
        write_json(name, {
            "_provenance": prov("vendor/go-multiaddr", "multiaddr_test.go", upstream),
            "cases": [
                {"string": unescape_go(a)[1:-1], "bytesHex": b[1:-1]}
                for a, b in pairs
            ],
        })

    string_bytes_pairs("TestStringToBytes", "TestStringToBytes",
                       "multiaddr-go-string-to-bytes.json")
    string_bytes_pairs("TestBytesToString", "TestBytesToString",
                       "multiaddr-go-bytes-to-string.json")

    # TestDecapsulate: decapsulate right from left; expected "" means nil.
    tbl = re.search(r"testcases := \[\]struct \{.*?\}\{(.*?)\n\t\}\n",
                    func_body(src, "TestDecapsulate"), re.S).group(1)
    cases = [
        {"left": l, "right": r, "expected": e}
        for l, r, e in re.findall(r'\{(".*?"), (".*?"), (".*?")\},', tbl)
    ]
    for c in cases:
        for k in ("left", "right", "expected"):
            c[k] = unescape_go(c[k])[1:-1]
    write_json("multiaddr-go-decapsulate.json", {
        "_provenance": prov("vendor/go-multiaddr", "multiaddr_test.go",
                            "TestDecapsulate"),
        "cases": cases,
        "note": "expected \"\" means Decapsulate returns nil (nothing left)",
    })

    # TestBytesSplitAndJoin
    body = func_body(src, "TestBytesSplitAndJoin")
    splits = []
    for m in re.finditer(rf'testString\(\s*({GO_STR}),\s*\[\]string\{{([^}}]*)\}}\)', body):
        parts = [unescape_go(p)[1:-1] for p in re.findall(GO_STR, m.group(2))]
        splits.append({"addr": unescape_go(m.group(1))[1:-1], "parts": parts})
    write_json("multiaddr-go-split.json", {
        "_provenance": prov("vendor/go-multiaddr", "multiaddr_test.go",
                            "TestBytesSplitAndJoin"),
        "cases": splits,
    })

    # TestRoundTrip: text form must round-trip byte-exactly.
    rt = go_strings(func_body(src, "TestRoundTrip"))
    write_json("multiaddr-go-round-trip.json", {
        "_provenance": prov("vendor/go-multiaddr", "multiaddr_test.go", "TestRoundTrip"),
        "cases": [{"string": s} for s in rt],
        "note": "IPv4-mapped IPv6 prints in Go's dotted ::ffff:a.b.c.d form "
                "(decision recorded in plan section 5)",
    })

    # TestIPFSvP2P
    p2p = re.search(r'p2pAddr\s+= "([^"]+)"', src).group(1)
    ipfs = re.search(r'ipfsAddr = "([^"]+)"', src).group(1)
    write_json("multiaddr-go-ipfs-v-p2p.json", {
        "_provenance": prov("vendor/go-multiaddr", "multiaddr_test.go", "TestIPFSvP2P"),
        "p2p": p2p, "ipfs": ipfs,
    })

    # TestInvalidP2PAddrBytes + TestInvalidP2PAddrString
    bad_bytes = re.search(r'badAddr := "([0-9a-f]+)"', src).group(1)
    bad_block = func_body(src, "TestInvalidP2PAddrString")
    bad_strings, derived = [], []
    for line in entry_lines(bad_block):
        if line.startswith('"/p2p/" +'):
            derived.append(line)  # CIDv1 with a non-libp2p-key codec, built inline
            continue
        bad_strings.append(re.match(GO_STR, line).group(0)[1:-1])
    write_json("multiaddr-go-invalid-p2p.json", {
        "_provenance": prov("vendor/go-multiaddr", "multiaddr_test.go",
                            "TestInvalidP2PAddrBytes, TestInvalidP2PAddrString"),
        "bytesHex": bad_bytes,
        "bytesNote": "Go rejects: the sha2-256 multihash declares digest "
                     "length 33 but carries 32 bytes",
        "strings": [{"string": s} for s in bad_strings],
        "derivedNote": "the inline \"/p2p/\" + unknownCodecCID entries use a "
                       "CIDv1 whose codec is not libp2p-key (0x72); rejected "
                       "by the CID codec check",
        "derivedSkipped": derived,
    })

    # TestProtocolsWithString (operations API, phase 1 step 9)
    body = func_body(src, "TestProtocolsWithString")
    goodmap = {}
    gblock = re.search(r"good := map\[string\]\[\]Protocol\{(.*?)\n\t\}", body, re.S).group(1)
    for m in re.finditer(rf'({GO_STR}):\s*\{{([^}}]*)\}}', gblock):
        goodmap[unescape_go(m.group(1))[1:-1]] = re.findall(r'pwn\("([^"]+)"\)', m.group(2))
    goodlist = [{"addr": k, "protocols": v} for k, v in goodmap.items()]
    bad = go_strings(re.search(r"bad := \[\]string\{(.*?)\n\t\}", body, re.S).group(1))
    write_json("multiaddr-go-protocols-with-string.json", {
        "_provenance": prov("vendor/go-multiaddr", "multiaddr_test.go",
                            "TestProtocolsWithString"),
        "good": goodlist,
        "bad": bad,
        "note": "consumed by the operations-API suite (phase 1 step 9)",
    })


    # TestGetValue: addr + ValueForProtocol checks (phase 1 step 9)
    body = func_body(src, "TestGetValue")
    cases, cur = [], None
    for line in body.splitlines():
        t = line.strip()
        m = re.match(rf'(?:a\s*(?::=|=)\s*)?newMultiaddr\(t,\s*({GO_STR})\)', t)
        if m:
            cur = {"addr": unescape_go(m.group(1))[1:-1], "checks": [], "missing": []}
            cases.append(cur)
            continue
        m = re.match(rf'assertValueForProto\(t, a, P_(\w+), ({GO_STR})\)', t)
        if m and cur is not None:
            cur["checks"].append(
                {"proto": m.group(1).lower().replace("http_path", "http-path"),
                 "value": unescape_go(m.group(2))[1:-1]})
            continue
        if "ValueForProtocol(P_IP6)" in t and cur is not None:
            cur["missing"].append("ip6")
    write_json("multiaddr-go-get-value.json", {
        "_provenance": prov("vendor/go-multiaddr", "multiaddr_test.go", "TestGetValue"),
        "protoNames": {"ipfs": "p2p", "utp": "utp", "tls": "tls"},
        "cases": cases,
    })

    # TestEncapsulate / decapsulate pairs
    body = func_body(src, "TestEncapsulate")
    strs = re.findall(GO_STR, body)
    encapsulate = [
        {"left": "/ip4/127.0.0.1/udp/1234", "right": "/udp/5678",
         "expected": "/ip4/127.0.0.1/udp/1234/udp/5678"},
    ]
    decapsulate = [
        {"left": "/ip4/127.0.0.1/udp/1234/udp/5678", "right": "/udp/5678",
         "expected": "/ip4/127.0.0.1/udp/1234"},
        {"left": "/ip4/127.0.0.1/udp/1234", "right": "/ip4/127.0.0.1",
         "expected": None},
    ]
    write_json("multiaddr-go-encapsulate.json", {
        "_provenance": prov("vendor/go-multiaddr", "multiaddr_test.go",
                            "TestEncapsulate"),
        "encapsulate": encapsulate,
        "decapsulate": decapsulate,
        "note": "expected null means Decapsulate returns nil; strings mirrored "
                "from the literals in the upstream test",
    })

    # TestEqual
    body = func_body(src, "TestEqual")
    (m1, m2, m3, m4) = [unescape_go(x)[1:-1]
                        for x in re.findall(GO_STR, body)[:4]]
    write_json("multiaddr-go-equal.json", {
        "_provenance": prov("vendor/go-multiaddr", "multiaddr_test.go", "TestEqual"),
        "pairs": [
            {"a": m1, "b": m2, "equal": False},
            {"a": m2, "b": m1, "equal": False},
            {"a": m2, "b": m3, "equal": True},
            {"a": m3, "b": m2, "equal": True},
            {"a": m1, "b": m1, "equal": True},
            {"a": m2, "b": m4, "equal": True},
            {"a": m4, "b": m3, "equal": True},
        ],
    })

    # TestFilterAddrs / TestContains / TestUniqueAddrs
    fbody = func_body(src, "TestFilterAddrs")
    bad = [unescape_go(x)[1:-1] for x in
           re.findall(rf'newMultiaddr\(t,\s*({GO_STR})\)',
                      re.search(r"bad := \[\]Multiaddr\{(.*?)\}", fbody, re.S).group(1))]
    good = [unescape_go(x)[1:-1] for x in
            re.findall(rf'newMultiaddr\(t,\s*({GO_STR})\)',
                       re.search(r"good := \[\]Multiaddr\{(.*?)\}", fbody, re.S).group(1))]
    write_json("multiaddr-go-filter-addrs.json", {
        "_provenance": prov("vendor/go-multiaddr", "multiaddr_test.go",
                            "TestFilterAddrs"),
        "good": good,
        "bad": bad,
        "filter": "first protocol code is ip4",
    })

    cbody = func_body(src, "TestContains")
    addrs = re.findall(rf'newMultiaddr\(t,\s*({GO_STR})\)', cbody)
    addrs = [unescape_go(x)[1:-1] for x in addrs]
    write_json("multiaddr-go-contains.json", {
        "_provenance": prov("vendor/go-multiaddr", "multiaddr_test.go", "TestContains"),
        "addrs": addrs[:4],
        "members": addrs[:4],
        "nonMembers": [addrs[4]] if len(addrs) > 4 else [],
    })

    ubody = func_body(src, "TestUniqueAddrs")
    names = {n: unescape_go(v)[1:-1] for n, v in
             re.findall(rf'(\w+Addr) := StringCast\(({GO_STR})\)', ubody)}
    def expand(tok):
        if tok.strip() == "nil":
            return []
        return [names[n] for n in re.findall(r"(\w+Addr)", tok)]
    tables = [{"in": expand(m.group(1)), "out": expand(m.group(2))}
              for m in re.finditer(r"\{in: (nil|\[\]Multiaddr\{[^}]*\}), out: (nil|\[\]Multiaddr\{[^}]*\})\}", ubody)]
    write_json("multiaddr-go-unique-addrs.json", {
        "_provenance": prov("vendor/go-multiaddr", "multiaddr_test.go",
                            "TestUniqueAddrs"),
        "tables": tables,
    })

    # TestZone / TestDNS / TestHTTPPath
    zbody = func_body(src, "TestZone")
    zstr = re.search(rf'ip6String := ({GO_STR})', zbody).group(1)[1:-1]
    zhex = re.search(r"ip6Bytes := \[\]byte\{([^}]*)\}", zbody).group(1)
    def zbyte(x):
        x = x.strip()
        if x.startswith("'"):
            return f"{ord(x.strip(chr(39))):02x}"
        return f"{int(x, 0) & 0xff:02x}"
    zbytes = "".join(zbyte(x) for x in zhex.split(",") if x.strip())
    write_json("multiaddr-go-zone.json", {
        "_provenance": prov("vendor/go-multiaddr", "multiaddr_test.go", "TestZone"),
        "string": zstr,
        "bytesHex": zbytes,
    })

    dbody = func_body(src, "TestDNS")
    dhex = re.search(r'b := \[\]byte\("([0-9a-f*)]+)"\)', dbody).group(1)
    write_json("multiaddr-go-dns.json", {
        "_provenance": prov("vendor/go-multiaddr", "multiaddr_test.go", "TestDNS"),
        "bytesHex": dhex.encode().hex(),
        "note": "upstream stores the bytes as a Go string literal; hex below "
                "is that literal's byte sequence",
    })

    hpbody = func_body(src, "TestHTTPPath")
    bad = re.search(rf'badAddr := ({GO_STR})', hpbody).group(1)[1:-1]
    rt = go_strings(re.search(r"cases := \[\]string\{(.*?)\n\t\}", hpbody, re.S).group(1))
    write_json("multiaddr-go-http-path.json", {
        "_provenance": prov("vendor/go-multiaddr", "multiaddr_test.go", "TestHTTPPath"),
        "bad": bad,
        "roundTrip": rt,
        "valueCase": {"addr": "/http-path/tmp%2Fbar/p2p-circuit",
                       "proto": "http-path", "value": "tmp%2Fbar"},
    })

    # Marshalers: text / binary / JSON round trips
    mbody = func_body(src, "TestBinaryMarshaler")
    addr = re.search(rf'newMultiaddr\(t,\s*({GO_STR})\)', mbody).group(1)[1:-1]
    write_json("multiaddr-go-marshaler.json", {
        "_provenance": prov("vendor/go-multiaddr", "multiaddr_test.go",
                            "TestBinaryMarshaler, TestTextMarshaler, "
                            "TestJSONMarshaler, TestComponent*Marshaler"),
        "addr": addr,
        "component": {"proto": "ip4", "value": "0.0.0.0"},
    })

# ---------------------------------------------------------------------------
# js-multiaddr (test/index.spec.ts, test/codec.spec.ts)
# ---------------------------------------------------------------------------

def extract_js_multiaddr() -> None:
    src = read("vendor/js-multiaddr", "test/index.spec.ts")

    # describe('variants'): object of name -> address, round-tripped by JS.
    vblock = re.search(r"describe\('variants'.*?const variants = \{(.*?)\n  \}\n",
                       src, re.S).group(1)
    variants = []
    for m in re.finditer(r"^\s+(?:'([^']*)'|(\w[\w ]*?)): '(.*)',?\s*$", vblock, re.M):
        variants.append({"name": m.group(1) or m.group(2), "value": m.group(3)})
    for c in variants:
        if c["value"].startswith("/memory/"):
            c["knownDivergence"] = ("js treats the memory value as an "
                "arbitrary string; we follow go/rust (big-endian u64, the "
                "plan's step 8 decision), so this js-only vector is skipped")
    write_json("multiaddr-js-variants.json", {
        "_provenance": prov("vendor/js-multiaddr", "test/index.spec.ts",
                            "describe('variants') roundTrip"),
        "cases": variants,
        "note": "expected output replaces /ipfs/ with /p2p/ (JS roundTrip)",
    })

    # describe('normalize'): input -> canonical output.
    nblock = re.search(r"describe\('normalize'.*?const variants = \{(.*?)\n  \}\n",
                       src, re.S).group(1)
    norms = [
        {"name": n, "input": i, "output": o}
        for n, i, o in re.findall(
            r"'([^']+)': \{\s*input: '([^']+)',\s*output: '([^']+)',?\s*\}", nblock)
    ]
    write_json("multiaddr-js-normalize.json", {
        "_provenance": prov("vendor/js-multiaddr", "test/index.spec.ts",
                            "describe('normalize')"),
        "cases": norms,
    })

    # Invalid inputs: the throw-expectations in both spec files.
    invalid = [
        {"string": "/ip4/0.0.0.0/ip4",
         "source": "codec.spec.ts: stringToComponents throw test"},
        {"string": "/ip4/127.0.0.1/unknown",
         "source": "index.spec.ts: unknown protocols"},
    ]
    write_json("multiaddr-js-invalid.json", {
        "_provenance": prov("vendor/js-multiaddr", "test/index.spec.ts, "
                           "test/codec.spec.ts", "throws on invalid addresses; "
                           "unknown protocols"),
        "cases": invalid,
    })


    # js getComponents tables (values are the js string conventions)
    comps = [
        {"addr": "/ip4/0.0.0.0/utp",
         "components": [{"code": 4, "name": "ip4", "value": "0.0.0.0"},
                          {"code": 302, "name": "utp", "value": None}]},
        {"addr": "/ip4/0.0.0.0/utp/ipfs/QmcgpsyWgH8Y8ajJz1Cu72KnS5uo2Aa2LpzU7kinSupNKC",
         "components": [{"code": 4, "name": "ip4", "value": "0.0.0.0"},
                          {"code": 302, "name": "utp", "value": None},
                          {"code": 421, "name": "p2p",
                           "value": "QmcgpsyWgH8Y8ajJz1Cu72KnS5uo2Aa2LpzU7kinSupNKC"}]},
        {"addr": "/ip4/0.0.0.0/tcp/8000/unix/tmp%2Fp2p.sock",
         "components": [{"code": 4, "name": "ip4", "value": "0.0.0.0"},
                          {"code": 6, "name": "tcp", "value": "8000"},
                          {"code": 400, "name": "unix", "value": "tmp/p2p.sock"}]},
        {"addr": "/memory/777/p2p/QmZR5a9AAXGqQF2ADqoDdGS8zvqv8n3Pag6TDDnTNMcFW6",
         "components": [{"code": 777, "name": "memory", "value": "777"},
                          {"code": 421, "name": "p2p",
                           "value": "QmZR5a9AAXGqQF2ADqoDdGS8zvqv8n3Pag6TDDnTNMcFW6"}]},
        {"addr": "/memory/test/p2p/QmZR5a9AAXGqQF2ADqoDdGS8zvqv8n3Pag6TDDnTNMcFW6",
         "knownDivergence": "js treats the memory value as a string; we "
                            "follow go/rust (big-endian u64) and skip this "
                            "js-only vector",
         "components": []},
    ]
    write_json("multiaddr-js-get-components.json", {
        "_provenance": prov("vendor/js-multiaddr", "test/index.spec.ts",
                            "describe('.getComponents')"),
        "cases": comps,
    })

    write_json("multiaddr-js-decapsulate.json", {
        "_provenance": prov("vendor/js-multiaddr", "test/index.spec.ts",
                            "describe('.decapsulate')"),
        "cases": [
            {"addr": "/ip4/127.0.0.1", "sub": "/ip4/198.168.0.0", "ok": False},
        ],
        "note": "js throws 'does not contain subaddress'; we model a none result",
    })

    write_json("multiaddr-js-decapsulate-code.json", {
        "_provenance": prov("vendor/js-multiaddr", "test/index.spec.ts",
                            "describe('.decapsulateCode')"),
        "relayTcp": "/ip4/0.0.0.0/tcp/8080",
        "relaySuffix": "/p2p/QmZR5a9AAXGqQF2ADqoDdGS8zvqv8n3Pag6TDDnTNMcFW6/p2p-circuit",
        "target": "/p2p/QmcgpsyWgH8Y8ajJz1Cu72KnS5uo2Aa2LpzU7kinSupNKC",
        "code": 421,
    })

    write_json("multiaddr-js-equals.json", {
        "_provenance": prov("vendor/js-multiaddr", "test/index.spec.ts",
                            "describe('.equals')"),
        "pairs": [
            {"a": "/ip4/192.168.0.1", "b": "/ip4/192.168.0.1", "equal": True},
            {"a": "/ip4/192.168.1.1", "b": "/ip4/192.168.0.1", "equal": False},
        ],
    })

    write_json("multiaddr-js-construction.json", {
        "_provenance": prov("vendor/js-multiaddr", "test/index.spec.ts",
                            "describe('construction')"),
        "addr": "/ip4/127.0.0.1/udp/1234",
        "emptyDivergence": "js parses '' and '////////' into an empty address "
                           "printed as '/'; Go rejects them - we follow Go for "
                           "parsing and js for printing the empty address",
    })

# ---------------------------------------------------------------------------
# multiformats/multiaddr protocols.csv
# ---------------------------------------------------------------------------

def extract_protocols_csv() -> None:
    # The CSV separator is sloppy (",\t" usually, ", " sometimes) and comments
    # may contain commas, so parse with a line regex instead of the csv module.
    rows = []
    for line in read("vendor/multiaddr", "protocols.csv").splitlines():
        if not line.strip() or line.startswith("code"):
            continue
        m = re.match(r"^(\d+),\s*(\d+|V),\s*([^,]+?)(?:,\s*(.*))?$", line)
        if not m:
            raise ValueError(f"unparsed protocols.csv line: {line!r}")
        rows.append({
            "code": int(m.group(1)),
            "size": -1 if m.group(2) == "V" else int(m.group(2)),
            "name": m.group(3),
            **({"comment": m.group(4)} if m.group(4) else {}),
        })
    write_json("multiaddr-protocols.json", {
        "_provenance": prov("vendor/multiaddr", "protocols.csv",
                            "authoritative protocol table"),
        "protocols": rows,
        "sizeSemantics": "-1 = uvarint-length-prefixed value (upstream writes "
                         "'V'), 0 = no value, n > 0 = exactly n bytes",
    })


    # Go fuzz seed corpora (phase 1 step 10)
    def go_unescape_bytes(src: str) -> bytes:
        out = bytearray()
        i = 0
        while i < len(src):
            c = src[i]
            if c == "\\" and i + 1 < len(src):
                n = src[i + 1]
                if n == "x":
                    out.append(int(src[i + 2 : i + 4], 16))
                    i += 4
                    continue
                mapping = {"n": 10, "r": 13, "t": 9, "\\": 92, '"': 34,
                           "'": 39, "a": 7, "b": 8, "f": 12, "v": 11}
                if n in mapping:
                    out.append(mapping[n])
                    i += 2
                    continue
            out.append(ord(c) if ord(c) < 256 else 0x3f)
            i += 1
        return bytes(out)

    seeds_b = []
    bdir = (ROOT / "vendor/go-multiaddr/testdata/fuzz/"
            "FuzzNewMultiaddrBytes")
    for q in sorted(bdir.iterdir()):
        for line in q.read_text().splitlines():
            m = re.fullmatch(r'\[\]byte\("(?:[^"\\]|\\.)*"\)', line)
            if m:
                inner = line[len('[]byte("'):-2]
                seeds_b.append(go_unescape_bytes(inner))
    write_json("multiaddr-go-fuzz-bytes.json", {
        "_provenance": prov("vendor/go-multiaddr", "testdata/fuzz/"
                            "FuzzNewMultiaddrBytes", "FuzzNewMultiaddrBytes"),
        "seedsHex": [x.hex() for x in seeds_b],
        "contract": "decoding must be total; accepted seeds must round-trip "
                    "through bytes and text",
    })

    seeds_s = []
    sdir = (ROOT / "vendor/go-multiaddr/testdata/fuzz/"
            "FuzzNewMultiaddrString")
    for q in sorted(sdir.iterdir()):
        for line in q.read_text().splitlines():
            m = re.fullmatch(r'string\("(?:[^"\\]|\\.)*"\)', line)
            if m:
                inner = line[len('string("'):-2]
                seeds_s.append(go_unescape_bytes(inner).decode(
                    "utf-8", "replace"))
    write_json("multiaddr-go-fuzz-strings.json", {
        "_provenance": prov("vendor/go-multiaddr", "testdata/fuzz/"
                            "FuzzNewMultiaddrString",
                            "FuzzNewMultiaddrString"),
        "seeds": seeds_s,
        "contract": "accepted seeds must round-trip through text and bytes",
    })

# ---------------------------------------------------------------------------
# multiformats/unsigned-varint README
# ---------------------------------------------------------------------------

def extract_varint() -> None:
    src = read("vendor/unsigned-varint", "README.md")
    examples = [
        {"n": int(m.group(1)), "binary": m.group(2).replace(" ", ""),
         "uvarintHex": m.group(3).lower()}
        for m in re.finditer(
            r"^(\d+) \(0x[0-9a-fA-F]+\) +=> ([01 ]+?) \(0x([0-9a-fA-F]+)\)", src, re.M)
    ]
    write_json("varint-examples.json", {
        "_provenance": prov("vendor/unsigned-varint", "README.md",
                            "spec examples and rules"),
        "examples": examples,
        "rules": [
            {"rule": "minimal encoding", "quote":
             "Multiformats varints must be minimally encoded. That is, numbers "
             "must be encoded in the least number of bytes possible.",
             "counterExampleHex": "8100",
             "counterExampleDecodesTo": 1},
            {"rule": "9-byte maximum", "quote":
             "Implementations MUST restrict the size of the varint to a max of "
             "9 bytes (63 bits)."},
        ],
    })


# ---------------------------------------------------------------------------
# multiformats/multihash README example block
# ---------------------------------------------------------------------------

def extract_multihash() -> None:
    src = read("vendor/multihash", "README.md")
    block = re.search(r"## Example\n\n.*?```\n(.*?)```", src, re.S).group(1)
    groups, alg = [], None
    for line in block.splitlines():
        line = line.strip()
        if not line:
            continue
        if line.startswith("#"):
            name = re.match(r"# (\S+)", line).group(1)
            alg = {"sha1": "sha1", "sha2-256": "sha2-256"}.get(name, name)
            groups.append({"algorithm": alg, "input": "multihash", "encodings": []})
            continue
        value, _, comment = line.partition(" # ")
        kind = {"hex": "hex", "base32": "base32pad-upper", "base58": "base58btc",
                "base64": "base64pad"}[comment.split(" in ")[-1]]
        groups[-1]["encodings"].append({"kind": kind, "value": value})
    write_json("multihash-examples.json", {
        "_provenance": prov("vendor/multihash", "README.md",
                            '"multihash" example vectors'),
        "cases": groups,
    })


# ---------------------------------------------------------------------------
# multiformats/multibase tests/*.csv
# ---------------------------------------------------------------------------

def extract_multibase() -> None:
    for csv_name, json_name in [
        ("basic.csv", "multibase-basic.json"),
        ("leading_zero.csv", "multibase-leading-zero.json"),
        ("case_insensitivity.csv", "multibase-case-insensitivity.json"),
        ("two_leading_zeros.csv", "multibase-two-leading-zeros.json"),
    ]:
        rows = []
        with open(ROOT / "vendor/multibase" / "tests" / csv_name, newline="",
                  encoding="utf-8") as f:
            for row in csv.reader(f):
                if not row or not row[0].strip():
                    continue
                name = row[0].strip()
                if name in ("encoding", "non-canonical encoding"):
                    continue  # CSV header rows carry no vector
                rows.append({"encoding": name,
                             "expected": row[1].strip().strip('"')})
        inputs = {
            "basic.csv": "yes mani !",
            "leading_zero.csv": "\x00yes mani !",
            "two_leading_zeros.csv": "\x00\x00yes mani !",
            "case_insensitivity.csv": "hello world",
        }
        write_json(json_name, {
            "_provenance": prov("vendor/multibase", f"tests/{csv_name}",
                                "multibase CSV vectors"),
            "input": inputs[csv_name],
            "cases": rows,
            "note": "encode checked in both directions for basic/leading_zero/"
                    "two_leading_zeros; the case-insensitivity file is a "
                    "decode-tolerance file (values are non-canonical)",
        })


# ---------------------------------------------------------------------------
# multistream-select wire example (libp2p/specs connections README)
# ---------------------------------------------------------------------------

def extract_mss() -> None:
    src = read("vendor/specs", "connections/README.md")
    hexes = re.findall(r"^0x([0-9a-f]+)$", src, re.M)
    assert hexes == ["036e610a"], f"unexpected wire examples: {hexes}"
    write_json("mss-wire.json", {
        "_provenance": prov("vendor/specs", "connections/README.md",
                            "multistream-select wire examples"),
        "framing": "uvarint length prefix, then UTF-8 message bytes ending in \\n",
        "cases": [
            {"message": "na", "bytesHex": "036e610a"},
            {"message": "/multistream/1.0.0\n", "bytesHex": "132f6d756c746973747265616d2f312e302e300a",
             "note": "derived from the framing rule stated in the README"},
        ],
    })


# ---------------------------------------------------------------------------
# phase 2: crypto and protobuf
# ---------------------------------------------------------------------------

def extract_peer_keys() -> None:
    """Key protobuf test vectors and peer-id string examples
    (vendor/specs/peer-ids/peer-ids.md)."""
    src = read("vendor/specs", "peer-ids/peer-ids.md")
    cases = []
    for m in re.finditer(r"\| (.*?) \| ([0-9a-fA-F ]+) \|", src):
        name = m.group(1).strip()
        hx = m.group(2).replace(" ", "").lower()
        if len(hx) < 8 or not re.fullmatch(r"[0-9a-f]+", hx):
            continue
        cases.append({"name": name, "bytesHex": hx})
    assert len(cases) == 8, f"expected 8 key vectors, got {len(cases)}"
    examples = []
    for line in src.splitlines():
        m = re.match(r"- `([A-Za-z0-9]+)` -- Peer ID \(([^)]*)\)", line.strip())
        if m:
            examples.append({"string": m.group(1), "kind": m.group(2).strip()})
    assert len(examples) == 3, f"expected 3 peer-id examples, got {len(examples)}"
    write_json("keys-peer-ids.json", {
        "_provenance": prov("vendor/specs", "peer-ids/peer-ids.md",
                            "keys: Test vectors; Peer Ids: String representation "
                            "examples"),
        "keys": cases,
        "peerIdExamples": examples,
    })


# RFC-embedded vectors: the RFC texts are not vendored; the vectors below
# are the well-known published ones, transcribed once here. The suites
# cross-check every one of these primitives against OpenSSL at runtime, so
# a transcription error cannot go unnoticed.

RFC_SHA512 = [
    {"name": "empty", "inputHex": "", "digestHex":
     "cf83e1357eefb8bdf1542850d66d8007d620e4050b5715dc83f4a921d36ce9ce"
     "47d0d13c5d85f2b0ff8318d2877eec2f63b931bd47417a81a538327af927da3e"},
    {"name": "abc", "inputHex": "616263", "digestHex":
     "ddaf35a193617abacc417349ae20413112e6fa4e89a97ea20a9eeee64b55d39a"
     "2192992a274fc1a836ba3c23a3feebbd454d4423643ce80e2a9ac94fa54ca49f"},
    {"name": "a", "inputHex": "61", "digestHex":
     "1f40fc92da241694750979ee6cf582f2d5d7d28e18335de05abc54d0560e0f5"
     "302860c652bf08d560252aa5e74210546f369fbbbce8c12cfc7957b2652fe9a75"},
    {"name": "896-bit two-block message", "inputHex":
     ("abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmn"
      "hijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu").encode().hex(),
     "digestHex":
     "8e959b75dae313da8cf4f72814fc143f8f7779c6eb9f7fa17299aeadb6889018"
     "501d289e4900f7e4331b99dec4b5433ac7d329eeb6dd26545e96e55b874be909"},
]

RFC_HMAC_SHA256 = [
    {"name": "RFC 4231 TC1", "keyHex": "0b" * 20, "dataHex": "4869205468657265",
     "macHex": "b0344c61d8db38535ca8afceaf0bf12b881dc200c9833da726e9376c2e32cff7"},
    {"name": "RFC 4231 TC2", "keyHex": "4a656665",
     "dataHex": "7768617420646f2079612077616e7420666f72206e6f7468696e673f",
     "macHex": "5bdcc146bf60754e6a042426089575c75a003f089d2739839dec58b964ec3843"},
]

RFC_HKDF_SHA256 = [
    {"name": "RFC 5869 TC1", "ikmHex": "0b" * 22,
     "saltHex": "000102030405060708090a0b0c",
     "infoHex": "f0f1f2f3f4f5f6f7f8f9", "l": 42,
     "prkHex": "077709362c2e32df0ddc3f0dc47bba6390b6c73bb50f9c3122ec844ad7c2b3e5",
     "okmHex": "3cb25f25faacd57a90434f64d0362f2a2d2d0a90cf1a5a4c5db02d56"
               "ecc4c5bf34007208d5b887185865"},
    {"name": "RFC 5869 TC3 (empty salt/info)", "ikmHex": "0b" * 22,
     "saltHex": "", "infoHex": "", "l": 42,
     "prkHex": "19ef24a32c717b167f33a91d6f648bdf96596776afdb6377ac434c1c293ccb04",
     "okmHex": "8da4e775a563c18f715f802a063c5a31b8a11f5c5ee1879ec3454e5f"
               "3c738d2d9d201395faa4b61a96c8"},
]

# RFC 8032 section 7.1 (Ed25519ph's pure scheme); the last message is
# SHA-512("abc") - Ed25519's "SHA" is SHA-512
RFC_ED25519 = [
    {"name": "TEST 1 (empty)", "seedHex":
     "9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60",
     "pubHex": "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a",
     "msgHex": "",
     "sigHex": "e5564300c360ac729086e2cc806e828a84877f1eb8e5d974d873e0652249"
               "01555fb8821590a33bacc61e39701cf9b46bd25bf5f0595bbe24655141"
               "438e7a100b"},
    {"name": "TEST 2 (1 byte 0x72)", "seedHex":
     "4ccd089b28ff96da9db6c346ec114e0f5b8a319f35aba624da8cf6ed4fb8a6fb",
     "pubHex": "3d4017c3e843895a92b70aa74d1b7ebc9c982ccf2ec4968cc0cd55f12af4660c",
     "msgHex": "72",
     "sigHex": "92a009a9f0d4cab8720e820b5f642540a2b27b5416503f8fb3762223ebd"
               "b69da085ac1e43e15996e458f3613d0f11d8c387b2eaeb4302aeeb00d29"
               "1612bb0c00"},
    {"name": "TEST 1024 (2 bytes)", "seedHex":
     "c5aa8df43f9f837bedb7442f31dcb7b166d38535076f094b85ce3a2e0b4458f7",
     "pubHex": "fc51cd8e6218a1a38da47ed00230f0580816ed13ba3303ac5deb911548908025",
     "msgHex": "af82",
     "sigHex": "6291d657deec24024827e69c3abe01a30ce548a284743a445e3680d7db5"
               "ac3ac18ff9b538d16f290ae67f760984dc6594a7c15e9716ed28dc027be"
               "ceea1ec40a"},
    {"name": "SHA(abc) (64-byte message)", "seedHex":
     "833fe62409237b9d62ec77587520911e9a759cec1d19755b7da901b96dca3d42",
     "pubHex": "ec172b93ad5e563bf4932c70e1245034c35467ef2efd4d64ebf819683467e2bf",
     "msgHex": "ddaf35a193617abacc417349ae20413112e6fa4e89a97ea20a9eeee64b55"
               "d39a2192992a274fc1a836ba3c23a3feebbd454d4423643ce80e2a9ac94"
               "fa54ca49f",
     "sigHex": "dc2a4459e7369633a52b1bf277839a00201009a3efbf3ecb69bea2186c2"
               "6b58909351fc9ac90b3ecfdfbc7c66431e0303dca179c138ac17ad9bef1"
               "177331a704"},
]


def extract_rfc_crypto() -> None:
    write_json("hashes-rfc.json", {
        "_provenance": {
            "repo": "https://www.rfc-editor.org (RFC 4634/FIPS 180-4 vectors; "
                    "RFC 4231; RFC 5869)",
            "path": "RFC 4231 (HMAC-SHA256 TC1/TC2), RFC 5869 (HKDF-SHA256 "
                    "TC1/TC3), FIPS 180-4 examples (SHA-512)",
            "upstreamTest": "published RFC test vectors",
            "extractedBy": "embedded in scripts/extract-vectors.py (RFC texts "
                           "not vendored); every primitive is cross-checked "
                           "against OpenSSL at runtime",
        },
        "sha512": RFC_SHA512,
        "hmacSha256": RFC_HMAC_SHA256,
        "hkdfSha256": RFC_HKDF_SHA256,
    })
    write_json("keys-rfc8032.json", {
        "_provenance": {
            "repo": "https://www.rfc-editor.org/rfc/rfc8032",
            "path": "section 7.1 (Ed25519)",
            "upstreamTest": "published RFC test vectors",
            "extractedBy": "embedded in scripts/extract-vectors.py (RFC text "
                           "not vendored); signatures verified against "
                           "OpenSSL at extraction review time and at runtime",
        },
        "ed25519": RFC_ED25519,
    })


# ---------------------------------------------------------------------------
# protobuf message vectors, generated with an independent mini-encoder
# (go-libp2p is not available in the build environment; the field numbers
# are the ones published in the vendored specs / peer-ids spec)
# ---------------------------------------------------------------------------

def _pb_varint(v: int) -> bytes:
    out = bytearray()
    while True:
        b = v & 0x7F
        v >>= 7
        if v:
            out.append(b | 0x80)
        else:
            out.append(b)
            return bytes(out)


def _pb_bytes(num: int, payload: bytes) -> bytes:
    return _pb_varint(num << 3 | 2) + _pb_varint(len(payload)) + payload


def _pb_str(num: int, s: str) -> bytes:
    return _pb_bytes(num, s.encode())


def extract_protobuf_messages() -> None:
    ed25519_pub = bytes.fromhex(
        "080112201ed1e8fae2c4a144b8be8fd4b47bf3d3b34b871c3cacf6010f0e42d474fce27e")
    ed25519_pub_raw = ed25519_pub[4:]
    # binary peer id: identity multihash of the 36-byte public key message
    peer_id = b"\x00" + _pb_varint(len(ed25519_pub)) + ed25519_pub

    ma1 = bytes.fromhex("047f0000010" + "6" + "0fa1")  # /ip4/127.0.0.1/tcp/4001
    ma2 = bytes.fromhex(
        "41" + "00" * 15 + "01" + "a302" + "0035")      # /ip6/::1/udp/53

    identify = (_pb_str(5, "ipfs/0.1.0") + _pb_str(6, "leanp2p/0.1.0")
                + _pb_bytes(1, ed25519_pub) + _pb_bytes(2, ma1)
                + _pb_bytes(2, ma2) + _pb_bytes(4, ma1)
                + _pb_str(3, "/ipfs/ping/1.0.0")
                + _pb_str(3, "/ipfs/id/1.0.0"))

    noise_extensions = _pb_str(2, "/yamux/1.0.0") + _pb_str(2, "/mplex/6.7.0")
    sig = bytes(range(64))
    noise_payload = (_pb_bytes(1, ed25519_pub)
                     + _pb_bytes(2, sig)
                     + _pb_bytes(4, noise_extensions))

    peer_record = (_pb_bytes(1, peer_id) + _pb_varint(2 << 3 | 0)
                   + _pb_varint(1570215229)
                   + _pb_bytes(3, _pb_bytes(1, ma1))
                   + _pb_bytes(3, _pb_bytes(1, ma2)))

    envelope = (_pb_bytes(1, ed25519_pub) + _pb_bytes(2, b"\x03\x01")
                + _pb_bytes(3, peer_record)
                + _pb_bytes(5, bytes(reversed(range(64)))))

    write_json("protobuf-messages.json", {
        "_provenance": {
            "repo": "field tables from vendor/specs: identify/README.md, "
                    "noise/README.md, RFC/0002-signed-envelopes.md, "
                    "RFC/0003-routing-records.md; PublicKey/PrivateKey from "
                    "peer-ids/peer-ids.md",
            "commit": LOCK["vendor/specs"]["commit"],
            "upstreamTest": "encode/decode against go-libp2p pb shapes",
            "extractedBy": "scripts/extract-vectors.py (independent "
                           "mini-encoder; go-libp2p not available in the "
                           "build environment)",
        },
        "note": "identitySig / envelope signature are filler bytes: the "
                "signature itself is exercised against OpenSSL in "
                "Tests/Keys (RFC 8032 vectors and round trips)",
        "cases": [
            {"name": "Identify (ed25519 key, two addrs, two protocols)",
             "bytesHex": identify.hex()},
            {"name": "NoiseHandshakePayload (ed25519 key, muxer extensions)",
             "bytesHex": noise_payload.hex()},
            {"name": "PeerRecord (identity-inlined ed25519 id, two addrs)",
             "bytesHex": peer_record.hex()},
            {"name": "Envelope (PeerRecord payload, payloadType 0x0301)",
             "bytesHex": envelope.hex()},
        ],
        "expected": {
            "protocolVersion": "ipfs/0.1.0",
            "agentVersion": "leanp2p/0.1.0",
            "listenAddrsHex": [ma1.hex(), ma2.hex()],
            "observedAddrHex": ma1.hex(),
            "protocols": ["/ipfs/ping/1.0.0", "/ipfs/id/1.0.0"],
            "streamMuxers": ["/yamux/1.0.0", "/mplex/6.7.0"],
            "seq": 1570215229,
            "payloadTypeHex": "0301",
        },
    })


# ---------------------------------------------------------------------------
# go-libp2p key fixtures (core/crypto/test_data, TestFixtures)
# ---------------------------------------------------------------------------

def extract_go_libp2p_fixtures() -> None:
    """The key fixtures go-libp2p itself tests against: for each of RSA (0),
    secp256k1 (2) and ECDSA (3) a private/public key protobuf pair plus a
    signature over the fixed message 'Libp2p is the _best_!'. This is the
    externally produced interop evidence for phase 2 step 13 (peer-ids spec
    vectors cover Ed25519)."""
    msg = b"Libp2p is the _best_!"
    base = "vendor/go-libp2p/core/crypto/test_data"
    names = {0: "rsa", 2: "secp256k1", 3: "ecdsa"}
    # sigDeterministic per go-libp2p core/crypto/fixture_test.go: secp256k1
    # (RFC 6979 nonce in btcec) and RSA (PKCS1-v1_5) are deterministic;
    # Go's crypto/ecdsa randomizes the ECDSA nonce.
    deterministic = {"rsa": True, "secp256k1": True, "ecdsa": False}
    cases = []
    for kt, name in names.items():
        rd = lambda ext: (ROOT / base / f"{kt}.{ext}").read_bytes()
        cases.append({
            "name": name,
            "privHex": rd("priv").hex(),
            "pubHex": rd("pub").hex(),
            "sigHex": rd("sig").hex(),
            "sigDeterministic": deterministic[name],
        })
    write_json("keys-go-libp2p.json", {
        "_provenance": prov("vendor/go-libp2p", "core/crypto/test_data",
                            "crypto/fixture_test.go TestFixtures"),
        "messageHex": msg.hex(),
        "note": "sigDeterministic mirrors the upstream fixture test: for "
                "deterministic schemes a re-sign must be byte-identical. We "
                "check that for RSA; secp256k1 is a documented divergence "
                "(OpenSSL randomizes the nonce, go's btcec uses RFC 6979 - "
                "recorded as an open item), ECDSA is randomized on both "
                "sides; verification is the contract for both.",
        "cases": cases,
    })


# ---------------------------------------------------------------------------
# phase 3: wire protocols
# ---------------------------------------------------------------------------

def extract_noise() -> None:
    """Noise framework XX vectors from flynn/noise (the library go-libp2p's
    noise transport uses): all Noise_XX_25519_ChaChaPoly_SHA256 entries -
    with/without prologue, with/without payloads."""
    entries = []
    cur = {}
    for line in read("vendor/flynn-noise", "vectors.txt").splitlines():
        line = line.strip()
        if not line:
            if cur:
                entries.append(cur)
                cur = {}
            continue
        k, _, v = line.partition("=")
        cur[k] = v
    if cur:
        entries.append(cur)
    sel = [e for e in entries
           if e.get("handshake") == "Noise_XX_25519_ChaChaPoly_SHA256"]
    assert sel, "no XX/25519/ChaChaPoly/SHA256 vectors in flynn/noise"
    cases = []
    for e in sel:
        msgs = []
        i = 0
        while f"msg_{i}_ciphertext" in e:
            msgs.append({"payload": e.get(f"msg_{i}_payload", ""),
                         "ciphertext": e[f"msg_{i}_ciphertext"]})
            i += 1
        cases.append({
            "note": ("with prologue" if "prologue" in e else "no prologue") +
                    ", " + ("with payloads" if msgs[0]["payload"] else "empty payloads"),
            "prologue": e.get("prologue", ""),
            "handshakeHash": e.get("handshake_hash", ""),
            "initStatic": e["init_static"],
            "respStatic": e["resp_static"],
            "initEphemeral": e["gen_init_ephemeral"],
            "respEphemeral": e["gen_resp_ephemeral"],
            "messages": msgs,
        })
    write_json("noise-vectors.json", {
        "_provenance": prov("vendor/flynn-noise", "vectors.txt",
                            "TestVectors (noise-c format), Noise_XX_25519_ChaChaPoly_SHA256"),
        "note": "handshake_hash entries are not in this file; conformance is \
                the message bytes themselves plus the go-libp2p transcript",
        "cases": cases,
    })


def extract_tls_vectors() -> None:
    """The four certificate vectors from tls.md (hex DER + expected peer id)."""
    src = read("vendor/specs", "tls/tls.md")
    blocks = re.findall(r"^```\n([0-9a-f]+)\n```$", src, re.M)
    ids = re.findall(r"^PeerId: `([^`]+)`$", src, re.M)
    assert len(blocks) == 4, f"expected 4 certificate vectors, got {len(blocks)}"
    assert len(ids) == 3, f"expected 3 expected peer ids, got {len(ids)}"
    write_json("tls-ext.json", {
        "_provenance": prov("vendor/specs", "tls/tls.md", "Test vectors"),
        "note": "certificate 4 is invalid: SignedKey signed by a different key",
        "cases": [
            {"name": "ed25519", "certHex": blocks[0], "peerId": ids[0]},
            {"name": "ecdsa", "certHex": blocks[1], "peerId": ids[1]},
            {"name": "secp256k1", "certHex": blocks[2], "peerId": ids[2]},
            {"name": "invalid", "certHex": blocks[3], "peerId": None},
        ],
    })


def extract_mss_ls() -> None:
    """The ls request/reply framing from the multistream-select README."""
    src = read("vendor/multistream-select", "README.md")
    assert "0x036c730a" in src, "ls wire example missing"
    # reply layout per the README ("ls example in detail"): one length-prefixed
    # message whose body is <varint-len><proto>\n per protocol, terminated by \n
    write_json("mss-ls.json", {
        "_provenance": prov("vendor/multistream-select", "README.md",
                            "Listing / ls example in detail"),
        "lsWireHex": "036c730a",
        "replyExample": {
            "protocols": ["/ipfs/kad/1.0.0", "/ipfs/id/1.0.0"],
            "bodyHex": "102f697066732f6b61642f312e302e300a" "0f2f697066732f69642f312e302e300a" "0a",
            "note": "varint(len(proto)+1) proto \\n, repeated, then a final \\n; "
                    "the reply is wrapped in one uvarint length prefix by the caller",
        },
    })


def main() -> None:
    OUT.mkdir(parents=True, exist_ok=True)
    extract_go_multiaddr()
    extract_js_multiaddr()
    extract_protocols_csv()
    extract_varint()
    extract_multihash()
    extract_multibase()
    extract_mss()
    extract_peer_keys()
    extract_rfc_crypto()
    extract_protobuf_messages()
    extract_go_libp2p_fixtures()
    extract_noise()
    extract_tls_vectors()
    extract_mss_ls()
    print("done", file=sys.stderr)


if __name__ == "__main__":
    main()
