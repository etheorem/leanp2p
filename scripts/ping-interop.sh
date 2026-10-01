#!/usr/bin/env bash
# ping-interop.sh — the VECTOR_TEST_PLAN.md phase 4 step 24 evidence:
# a Lean node and a go-libp2p node ping each other on loopback, both
# directions.
#
# Docker is only used to build the go node (go-libp2p v0.50.0, CGO off =>
# static binary); both nodes then run on the host and talk over 127.0.0.1.
# The stack is tcp + /noise + yamux on both sides; the muxer is selected
# from the Noise handshake extension (go upgrader semantics), no
# multistream muxer negotiation.
#
# Requires: docker (golang image, network for the module download),
# lake (toolchain from lean-toolchain), OpenSSL dev libs.
set -euo pipefail
cd "$(dirname "$0")/.."

GO_PORT=${GO_PORT:-45001}
LEAN_PORT=${LEAN_PORT:-45002}
WORK=$(mktemp -d)
GPID=""; LPID=""
cleanup () {
  [ -n "$GPID" ] && kill "$GPID" 2>/dev/null || true
  [ -n "$LPID" ] && kill "$LPID" 2>/dev/null || true
  rm -rf "$WORK"
}
trap cleanup EXIT

echo "== building the go node (docker, go-libp2p v0.50.0) =="
docker run --rm -v "$PWD/scripts:/src" golang:alpine sh -c '
  set -e
  mkdir /work && cd /work
  go mod init leanping >/dev/null 2>&1
  GOFLAGS=-mod=mod go get github.com/libp2p/go-libp2p@v0.50.0 >/dev/null 2>&1
  cp /src/pingd.go .
  CGO_ENABLED=0 go build -o /src/pingd pingd.go
  echo "go node built"'
test -x scripts/pingd

echo "== building the lean node =="
lake build pingnode >/dev/null
echo "lean node built"

echo
echo "== go node serves on 127.0.0.1:$GO_PORT =="
tail -f /dev/null | ./scripts/pingd -mode serve -port "$GO_PORT" \
  >"$WORK/go.out" 2>"$WORK/go.err" &
GPID=$!

echo "== lean node serves on 127.0.0.1:$LEAN_PORT =="
tail -f /dev/null | ./.lake/build/bin/pingnode serve "$LEAN_PORT" \
  >"$WORK/lean.out" 2>"$WORK/lean.err" &
LPID=$!

wait_for_addr () { # file
  for _ in $(seq 1 60); do
    if grep -q '^ADDR ' "$1" 2>/dev/null; then return 0; fi
    sleep 0.5
  done
  echo "timeout waiting for ADDR in $1" >&2
  cat "$1" >&2; cat "$1.err" 2>/dev/null >&2 || true
  return 1
}

wait_for_addr "$WORK/go.out"
wait_for_addr "$WORK/lean.out"

GO_LINE=$(grep '^ADDR ' "$WORK/go.out" | head -1)
LEAN_LINE=$(grep '^ADDR ' "$WORK/lean.out" | head -1)
# the go node prints a bare listen addr; the lean node's Host.addrs already
# includes the /p2p/<id> suffix
GO_ADDR="/ip4/127.0.0.1/tcp/$GO_PORT/p2p/$(echo "$GO_LINE" | awk '{print $3}')"
LEAN_ADDR="$(echo "$LEAN_LINE" | awk '{print $2}')"
echo "go node:   $(echo "$GO_LINE" | awk '{print $2, $3}')"
echo "lean node: $(echo "$LEAN_LINE" | awk '{print $2, $3}')"

echo
echo "== lean dials go (multistream /noise, muxer from the noise extension) =="
./.lake/build/bin/pingnode dial "$GO_ADDR"

echo
echo "== go dials lean =="
./scripts/pingd -mode dial -addr "$LEAN_ADDR"

echo
echo "PASS: lean <-> go-libp2p loopback ping, both directions"
