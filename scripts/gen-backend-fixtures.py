#!/usr/bin/env python3
"""Generate the crypto/backend strictness fixtures (W3.2, sub-unit 1b).

The backend plan's vector stance: a family with no captured vector
closes through "a generated fixture whose provenance the file records"
(packages/crypto/backend/docs/PLAN.md). The TLS spec's four certificates
hold no expired one and no unknown critical extension, and no captured
file holds an RSA key outside 2048 to 8192 bits, so this script makes
them with the openssl CLI.

The keys are random, so a rerun gives new bytes. The output therefore
lives in Tests/fixtures/, outside the provenance-gated Tests/vectors/
corpus, and the file records the tool, its version, and the date.

Each certificate breaks one rule and keeps every other one: a P-256
self-signed certificate with the required extension, valid far into the
future, except where its case says otherwise. A minimal openssl config
keeps the default extensions out, so each case adds only what it tests;
`knownCritical` adds a critical `basicConstraints` on purpose. Two
cases need a weak self-signature (SHA-1, a 1024-bit RSA key), one needs
a duplicate extension, which openssl refuses to write, so the script
splices a second copy into the DER, and one SEC1 P-256 key stores its
public point compressed.

Usage: scripts/gen-backend-fixtures.py   (writes Tests/fixtures/backend-strictness.json)
"""

import datetime
import json
import pathlib
import subprocess
import tempfile

ROOT = pathlib.Path(__file__).resolve().parent.parent
OUT = ROOT / "Tests" / "fixtures" / "backend-strictness.json"

# The OID of the TLS spec's key extension (tls.md); any OID would do, and
# this one matches the certificates the fixtures stand beside.
REQUIRED_OID = "1.3.6.1.4.1.53594.1.1"
# An OID under the IANA example arc (RFC 7229), which no verifier knows.
UNKNOWN_OID = "1.3.6.1.4.1.32473.1.1"
# The extension value: the DER OCTET STRING 01 02 03.
EXT_VALUE = "0403010203"
MESSAGE = b"leanp2p backend strictness fixture"

CONFIG = """\
[req]
distinguished_name = dn
x509_extensions = ext
prompt = no
[dn]
O = leanp2p fixture
[ext]
subjectKeyIdentifier = none
authorityKeyIdentifier = none
"""


def run(*args: str, cwd: pathlib.Path) -> bytes:
    return subprocess.run(args, cwd=cwd, check=True, capture_output=True).stdout


def posix(stamp: str) -> int:
    """Seconds since the epoch of a YYYYMMDDHHMMSSZ stamp."""
    t = datetime.datetime.strptime(stamp, "%Y%m%d%H%M%SZ")
    return int(t.replace(tzinfo=datetime.timezone.utc).timestamp())


def rsa_case(bits: int, d: pathlib.Path) -> dict:
    run("openssl", "genpkey", "-algorithm", "RSA", "-pkeyopt", f"rsa_keygen_bits:{bits}",
        "-out", f"rsa{bits}.pem", cwd=d)
    priv = run("openssl", "rsa", "-in", f"rsa{bits}.pem", "-traditional", "-outform", "DER", cwd=d)
    spki = run("openssl", "pkey", "-in", f"rsa{bits}.pem", "-pubout", "-outform", "DER", cwd=d)
    sig = run("openssl", "dgst", "-sha256", "-sign", f"rsa{bits}.pem", "msg", cwd=d)
    return {"bits": bits, "privHex": priv.hex(), "spkiHex": spki.hex(), "sigHex": sig.hex()}


def ec_case(curve: str, d: pathlib.Path) -> dict:
    run("openssl", "genpkey", "-algorithm", "EC", "-pkeyopt", f"ec_paramgen_curve:{curve}",
        "-out", f"{curve}.pem", cwd=d)
    spki = run("openssl", "pkey", "-in", f"{curve}.pem", "-pubout", "-outform", "DER", cwd=d)
    sig = run("openssl", "dgst", "-sha256", "-sign", f"{curve}.pem", "msg", cwd=d)
    return {"curve": curve, "spkiHex": spki.hex(), "sigHex": sig.hex()}


def der_header(tag: int, length: int) -> bytes:
    """A DER tag and length (X.690 §8.1.3): the short form below 128,
    else the minimal long form."""
    if length < 0x80:
        return bytes([tag, length])
    body = length.to_bytes((length.bit_length() + 7) // 8, "big")
    return bytes([tag, 0x80 | len(body)]) + body


def der_read(b: bytes, i: int) -> tuple[int, int, int]:
    """The tag, the contents start, and the contents end of the element at i."""
    first = b[i + 1]
    if first < 0x80:
        return b[i], i + 2, i + 2 + first
    n = first & 0x7F
    length = int.from_bytes(b[i + 2:i + 2 + n], "big")
    return b[i], i + 2 + n, i + 2 + n + length


def der_duplicate(b: bytes, i: int, target: bytes) -> bytes:
    """The element at i, rebuilt with a second copy of `target` right after
    its first copy, and every enclosing length fixed. The signature no
    longer matches, which the inspect rule this fixture tests ignores."""
    tag, start, end = der_read(b, i)
    at = b.find(target, start, end)
    if at < 0:
        return b[i:end]
    parts, j = [], start
    while j < end:
        _, _, child_end = der_read(b, j)
        if b[j:child_end] == target:
            parts += [target, target]
        elif j <= at < child_end:
            parts.append(der_duplicate(b, j, target))
        else:
            parts.append(b[j:child_end])
        j = child_end
    body = b"".join(parts)
    return der_header(tag, len(body)) + body


def certificate(name: str, d: pathlib.Path, not_before: str, not_after: str,
                exts: list[str], expect: str, why: str,
                key: str = "cert.pem", extra: tuple[str, ...] = ()) -> dict:
    args = ["openssl", "req", "-x509", "-new", "-config", "req.cnf", "-key", key,
            "-not_before", not_before, "-not_after", not_after, "-outform", "DER",
            "-out", f"{name}.der", *extra]
    for e in exts:
        args += ["-addext", e]
    run(*args, cwd=d)
    return {
        "name": name,
        "certHex": (d / f"{name}.der").read_bytes().hex(),
        "notBefore": posix(not_before),
        "notAfter": posix(not_after),
        "expect": expect,
        "why": why,
    }


def main() -> None:
    with tempfile.TemporaryDirectory() as tmp:
        d = pathlib.Path(tmp)
        (d / "msg").write_bytes(MESSAGE)
        (d / "req.cnf").write_text(CONFIG)
        run("openssl", "genpkey", "-algorithm", "EC", "-pkeyopt", "ec_paramgen_curve:P-256",
            "-out", "cert.pem", cwd=d)
        required = f"{REQUIRED_OID}=DER:{EXT_VALUE}"
        far = ("20240101000000Z", "40960101000000Z")
        certs = [
            certificate("valid", d, *far, [required], "accept",
                        "the baseline: every rule holds"),
            certificate("requiredCritical", d, *far, [f"{REQUIRED_OID}=critical,DER:{EXT_VALUE}"],
                        "accept", "the required extension may be critical"),
            certificate("unknownNonCritical", d, *far, [required, f"{UNKNOWN_OID}=DER:0500"],
                        "accept", "an unknown non-critical extension is ignored"),
            certificate("unknownCritical", d, *far, [required, f"{UNKNOWN_OID}=critical,DER:0500"],
                        "reject", "an unknown critical extension"),
            certificate("missingExtension", d, *far, [], "reject",
                        "the required extension is missing"),
            certificate("expired", d, "20000101000000Z", "20010101000000Z", [required],
                        "expired", "parses, but NotAfter lies in the past"),
            certificate("knownCritical", d, *far, [required, "basicConstraints=critical,CA:FALSE"],
                        "accept", "a critical extension the endpoint understands"),
            certificate("sha1Signature", d, *far, [required], "badSelfSignature",
                        "a SHA-1 signature, which Go rejects", extra=("-sha1",)),
        ]
        # An RSA key outside the §4.6 range, under a SHA-256 signature.
        run("openssl", "genpkey", "-algorithm", "RSA", "-pkeyopt", "rsa_keygen_bits:1024",
            "-out", "rsa1024cert.pem", cwd=d)
        certs.append(certificate("rsa1024Key", d, *far, [required], "badSelfSignature",
                                 "an RSA subject key below 2048 bits", key="rsa1024cert.pem"))
        # A duplicate extension: openssl refuses to write one, so the DER
        # gets a second copy of the unknown non-critical extension.
        base = bytes.fromhex(next(c for c in certs if c["name"] == "unknownNonCritical")["certHex"])
        oid = bytes.fromhex("060a2b0601040181fd590101")  # UNKNOWN_OID, 32473 = 0x81 0xfd 0x59
        ext = der_header(0x30, len(oid) + 4) + oid + bytes.fromhex("04020500")
        assert base.count(ext) == 1, "the unknown extension is not where the splice expects it"
        dup = der_duplicate(base, 0, ext)
        assert dup.count(ext) == 2
        certs.append({**next(c for c in certs if c["name"] == "unknownNonCritical"),
                      "name": "duplicateExtension", "certHex": dup.hex(), "expect": "reject",
                      "why": "an extension that appears twice (RFC 5280 §4.2)"})
        # A SEC1 P-256 key whose public point is stored compressed.
        compressed = run("openssl", "ec", "-in", "cert.pem", "-conv_form", "compressed",
                         "-outform", "DER", cwd=d)
        rsa = [rsa_case(1024, d), rsa_case(9216, d)]
        secp = ec_case("secp256k1", d)
        version = run("openssl", "version", cwd=d).decode().strip()
    OUT.parent.mkdir(exist_ok=True)
    OUT.write_text(json.dumps({
        "_provenance": {
            "generatedBy": "scripts/gen-backend-fixtures.py",
            "tool": version,
            "generated": datetime.date.today().isoformat(),
            "note": "random keys: a rerun gives new bytes; the cases, not the bytes, "
                    "are the contract",
        },
        "requiredOid": REQUIRED_OID,
        "extensionValueHex": EXT_VALUE,
        "messageHex": MESSAGE.hex(),
        "certificates": certs,
        "rsaOutOfRange": rsa,
        "secp256k1Spki": secp,
        "p256CompressedSec1Hex": compressed.hex(),
    }, indent=1) + "\n")


if __name__ == "__main__":
    main()
