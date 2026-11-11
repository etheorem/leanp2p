#!/usr/bin/env bash
# Go dials `pingnode serve` over TCP, Noise, and yamux.
#
# Readiness is `ADDR <multiaddr> <peerid>`. The dial address joins
# those fields with `/p2p/`. The address field has no peer suffix.
#
# The server runs with LEAN_NUM_THREADS=1. Go prints one ping result
# and stays up. The driver then closes the server's stdin and waits
# for the server to exit 0. It then closes Go's stdin and waits for
# Go to exit 0. PASS follows both exits. A peer that exits early
# fails the script. Set PING_GO_BIN to replace the helper.
#
# The helper builds with the host Go toolchain, CGO off, from
# scripts/ping-go. go-libp2p v0.50.0 asks for Go 1.26. An older go
# command downloads that toolchain.
#
# `finish_child` ends one owned child. It sends SIGTERM, waits at most
# `term_grace` seconds, sends SIGKILL if the child is still alive, and
# reaps it. A child that has already exited is reaped. The ping
# deadline, both stdin holders, the Go teardown deadline, and the
# EXIT cleanup use this helper. The server shutdown wait and the Go
# exit wait are polls. EOF is the wake. The helper runs for a child
# that misses its wait, and for each holder when its EOF is due.
set -euo pipefail

root=$(cd "$(dirname "$0")/.." && pwd)
work=$(mktemp -d "${TMPDIR:-/tmp}/ping-go-interop.XXXXXX")
bin="$root/.tmp/ping-go/ping-go"
server_pid=
hold_pid=
go_pid=
go_hold_pid=
server_status=
term_grace=2

finish_child() {
  local pid=$1
  local start now
  if [[ -z ${pid:-} ]]; then
    return 0
  fi
  if kill -0 "$pid" 2>/dev/null; then
    kill "$pid" 2>/dev/null || true
    start=$(date +%s)
    while kill -0 "$pid" 2>/dev/null; do
      now=$(date +%s)
      if (( now - start >= term_grace )); then
        kill -9 "$pid" 2>/dev/null || true
        break
      fi
      sleep 0.2
    done
  fi
  wait "$pid" 2>/dev/null || true
}

reap() {
  local status=$?
  if [[ -n ${go_pid:-} ]]; then
    finish_child "$go_pid"
    go_pid=
  fi
  if [[ -n ${go_hold_pid:-} ]]; then
    finish_child "$go_hold_pid"
    go_hold_pid=
  fi
  if [[ -n ${hold_pid:-} ]]; then
    finish_child "$hold_pid"
    hold_pid=
  fi
  if [[ -n ${server_pid:-} ]]; then
    finish_child "$server_pid"
    server_pid=
  fi
  rm -rf "$work"
  exit "$status"
}
trap reap EXIT

fail() {
  echo "FAIL go-to-lean: $*" >&2
  if [[ -s "$work/server.err" ]]; then
    cat "$work/server.err" >&2
  fi
  if [[ -s "$work/go.err" ]]; then
    cat "$work/go.err" >&2
  fi
  exit 1
}

mkdir -p "$root/.tmp/ping-go"
( cd "$root" && lake build pingnode )
( cd "$root/scripts/ping-go" && CGO_ENABLED=0 go build -o "$bin" . )

mkfifo "$work/in"
sleep 3600 >"$work/in" &
hold_pid=$!
LEAN_NUM_THREADS=1 "$root/.lake/build/bin/pingnode" serve 0 \
  <"$work/in" >"$work/server.out" 2>"$work/server.err" &
server_pid=$!

line=
start=$(date +%s)
while true; do
  if [[ -s "$work/server.out" ]]; then
    line=$(head -n 1 "$work/server.out" || true)
    if [[ "$line" == ADDR\ * ]]; then
      break
    fi
  fi
  if ! kill -0 "$server_pid" 2>/dev/null; then
    fail "server exited before ADDR"
  fi
  now=$(date +%s)
  if (( now - start >= 15 )); then
    fail "no ADDR line within 15 s"
  fi
  sleep 0.2
done

set -- $line
if [[ $# -ne 3 || $1 != ADDR ]]; then
  fail "readiness line: $line"
fi
addr=$2
peer=$3
case "$addr" in
  */p2p/*) fail "readiness address already has a peer suffix: $addr" ;;
esac
case "$addr" in
  /ip4/127.0.0.1/tcp/*) ;;
  *) fail "readiness address: $addr" ;;
esac
port=${addr##*/}
if [[ ! "$port" =~ ^[1-9][0-9]*$ ]] || (( port > 65535 )); then
  fail "bound port: $port"
fi
if [[ -z "$peer" ]]; then
  fail "readiness line has no peer id"
fi
dial="${addr}/p2p/${peer}"

go_bin=${PING_GO_BIN:-$bin}
mkfifo "$work/go.in"
sleep 3600 >"$work/go.in" &
go_hold_pid=$!
"$go_bin" "$dial" <"$work/go.in" >"$work/go.out" 2>"$work/go.err" &
go_pid=$!
start=$(date +%s)
while true; do
  if [[ -s "$work/go.out" ]] && grep -q '^PING OK rtt=.' "$work/go.out"; then
    if ! kill -0 "$go_pid" 2>/dev/null; then
      set +e
      wait "$go_pid"
      go_status=$?
      set -e
      go_pid=
      fail "go exited after the ping result: $go_status"
    fi
    break
  fi
  if ! kill -0 "$go_pid" 2>/dev/null; then
    set +e
    wait "$go_pid"
    go_status=$?
    set -e
    go_pid=
    fail "go exit $go_status"
  fi
  now=$(date +%s)
  if (( now - start >= 25 )); then
    finish_child "$go_pid"
    go_pid=
    fail "go ping missed 25 s"
  fi
  sleep 0.2
done

if ! kill -0 "$go_pid" 2>/dev/null; then
  fail "go exited before the server shutdown"
fi
finish_child "$hold_pid"
hold_pid=
start=$(date +%s)
while kill -0 "$server_pid" 2>/dev/null; do
  if ! kill -0 "$go_pid" 2>/dev/null; then
    fail "go exited during the server shutdown"
  fi
  now=$(date +%s)
  if (( now - start >= 15 )); then
    fail "server missed the shutdown deadline"
  fi
  sleep 0.2
done
set +e
wait "$server_pid"
server_status=$?
set -e
server_pid=
if [[ "$server_status" -ne 0 ]]; then
  fail "server exit $server_status"
fi
if ! kill -0 "$go_pid" 2>/dev/null; then
  fail "go exited before its teardown"
fi
finish_child "$go_hold_pid"
go_hold_pid=
start=$(date +%s)
while kill -0 "$go_pid" 2>/dev/null; do
  now=$(date +%s)
  if (( now - start >= 15 )); then
    finish_child "$go_pid"
    go_pid=
    fail "go missed the teardown deadline"
  fi
  sleep 0.2
done
set +e
wait "$go_pid"
go_status=$?
set -e
go_pid=
if [[ "$go_status" -ne 0 ]]; then
  fail "go teardown exit $go_status"
fi
echo "PASS go-to-lean $(head -n 1 "$work/go.out")"
