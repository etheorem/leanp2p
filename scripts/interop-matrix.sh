#!/usr/bin/env bash
# interop-matrix.sh — the VECTOR_TEST_PLAN.md phase 5 (steps 25+26) live
# evidence: the transport-interop harness (`interop`, scripts/interopd.go)
# run against go-libp2p v0.50.0 through Redis, exactly the way
# libp2p/test-plans transport-interop coordinates dialer and listener.
#
# Cells (dialer x listener), per muxer:
#   lean -> go   and   go -> lean     (tcp x noise x yamux)
#   mplex: go-libp2p v0.50 removed mplex upstream, so those cells are
#   reported as not-runnable-against-go; the Lean side's go-compatible
#   mplex identity is covered in-process (Tests/Interop.lean).
#
# Both nodes run on the host over loopback (the go binary is built in
# docker, CGO off, like scripts/ping-interop.sh); Redis runs in docker.
#
# Requires: docker (golang + redis images, network for the module
# download), lake, OpenSSL dev libs.
set -euo pipefail
cd "$(dirname "$0")/.."

WORK=$(mktemp -d)
GPID=""; LPID=""
cleanup () {
  [ -n "$GPID" ] && kill "$GPID" 2>/dev/null || true
  [ -n "$LPID" ] && kill "$LPID" 2>/dev/null || true
  docker rm -f leanp2p-redis >/dev/null 2>&1 || true
  rm -rf "$WORK"
}
trap cleanup EXIT

echo "== building the go harness node (docker, go-libp2p v0.50.0) =="
docker run --rm -v "$PWD/scripts:/src" golang:alpine sh -c '
  set -e
  mkdir /work && cd /work
  go mod init leaninterop >/dev/null 2>&1
  GOFLAGS=-mod=mod go get github.com/libp2p/go-libp2p@v0.50.0 >/dev/null 2>&1
  cp /src/interopd.go .
  CGO_ENABLED=0 go build -o /src/interopd interopd.go
  echo "go node built"'
test -x scripts/interopd

echo "== building the lean harness (lake build interop) =="
lake build interop >/dev/null
echo "lean harness built"

echo
echo "== starting redis (docker, redis:7-alpine) =="
docker rm -f leanp2p-redis >/dev/null 2>&1 || true
docker run -d --name leanp2p-redis -p 127.0.0.1:16379:6379 redis:7-alpine >/dev/null
for _ in $(seq 1 20); do
  if docker exec leanp2p-redis redis-cli PING 2>/dev/null | grep -q PONG; then break; fi
  sleep 0.5
done
docker exec leanp2p-redis redis-cli PING

PASS=0; FAIL=0; SKIP=0

run_cell () { # dialer listener muxer label
  local dialer=$1 listener=$2 muxer=$3 label=$4
  docker exec leanp2p-redis redis-cli DEL listenerAddr >/dev/null

  if [ "$listener" = "lean" ]; then
    env transport=tcp muxer="$muxer" security=noise is_dialer=false ip=127.0.0.1 \
        redis_addr=127.0.0.1:16379 test_timeout_seconds=60 \
        ./.lake/build/bin/interop >"$WORK/l.out" 2>"$WORK/l.err" &
  else
    env transport=tcp muxer="$muxer" security=noise is_dialer=false ip=127.0.0.1 \
        redis_addr=127.0.0.1:16379 test_timeout_seconds=60 \
        ./scripts/interopd >"$WORK/l.out" 2>"$WORK/l.err" &
  fi
  LPID=$!
  sleep 0.5
  # a go listener asked for mplex refuses to start (mplex removed upstream)
  if ! kill -0 "$LPID" 2>/dev/null; then
    if grep -q "removed mplex" "$WORK/l.err" 2>/dev/null; then
      echo "SKIP  $label (go-libp2p v0.50 removed mplex upstream)"
      SKIP=$((SKIP+1))
      return 0
    fi
  fi

  local rc=0
  if [ "$dialer" = "lean" ]; then
    env transport=tcp muxer="$muxer" security=noise is_dialer=true ip=127.0.0.1 \
        redis_addr=127.0.0.1:16379 test_timeout_seconds=60 \
        ./.lake/build/bin/interop >"$WORK/d.out" 2>"$WORK/d.err" || rc=$?
  else
    env transport=tcp muxer="$muxer" security=noise is_dialer=true ip=127.0.0.1 \
        redis_addr=127.0.0.1:16379 test_timeout_seconds=60 \
        ./scripts/interopd >"$WORK/d.out" 2>"$WORK/d.err" || rc=$?
  fi

  kill "$LPID" 2>/dev/null || true
  wait "$LPID" 2>/dev/null || true
  LPID=""

  if [ $rc -ne 0 ]; then
    if grep -q "removed mplex" "$WORK/d.err" 2>/dev/null; then
      echo "SKIP  $label (go-libp2p v0.50 removed mplex upstream)"
      SKIP=$((SKIP+1))
      return 0
    fi
    echo "FAIL  $label (dialer exit $rc)"
    sed 's/^/      /' "$WORK/d.err" | tail -3
    FAIL=$((FAIL+1))
    return 0
  fi
  if grep -q '"handshakePlusOneRTTMillis"' "$WORK/d.out" && grep -q '"pingRTTMilllis"' "$WORK/d.out"; then
    echo "PASS  $label  $(cat "$WORK/d.out")"
    PASS=$((PASS+1))
  else
    echo "FAIL  $label (no timing JSON)"
    FAIL=$((FAIL+1))
  fi
}

run_cell lean go   yamux "tcp x noise x yamux: lean dials go"
run_cell go   lean yamux "tcp x noise x yamux: go dials lean"
run_cell lean go   mplex "tcp x noise x mplex: lean dials go"
run_cell go   lean mplex "tcp x noise x mplex: go dials lean"

echo
echo "matrix: $PASS passed, $FAIL failed, $SKIP skipped (go has no mplex; \
lean<->lean mplex is covered in-process by Tests/Interop)"
[ "$FAIL" -eq 0 ]
