#!/usr/bin/env bash
# The TLS interop check (packages/libp2p/security/docs/PLAN.md, unit 2):
# this package's TLS seam value against go-libp2p v0.50.0's TLS
# transport, over plain loopback TCP, in both directions. Each run checks
# both certificates and both peer ids, moves 200000 bytes each way
# (thirteen TLS records), and ends with an orderly close. Six more runs
# check the refusals in both directions, each ending in the alert
# bad_certificate, and peers that use no ALPN.
#
# Go builds offline from the module cache; run `go mod download` in
# scripts/tls-interop once on a machine that lacks it.
set -euo pipefail

root=$(cd "$(dirname "$0")/.." && pwd)
out="$root/.tmp/tls-interop"
mkdir -p "$out"

# Both builds run on two cores at the lowest priority, so the check can
# run beside other work on the machine.
( cd "$root/scripts/tls-interop" &&
  GOPROXY=off GOSUMDB=off nice -n19 taskset -c 0,1 go build -p 2 -o "$out/go-peer" . )
( cd "$root" &&
  LEAN_NUM_THREADS=2 nice -n19 taskset -c 0,1 lake build tls-interop >"$out/lake.out" )
lean="$root/.lake/build/bin/tls-interop"
go="$out/go-peer"

# $2 listens in mode $3 and prints its port; $4 dials that port in
# mode $5.
run() {
  local name=$1 listener=$2 listen_mode=$3 dialer=$4 dial_mode=$5
  coproc LISTEN { timeout 120 "$listener" "$listen_mode"; }
  # Bash unsets the coprocess variables once it exits, so take them now.
  local pid=$LISTEN_PID port=
  # A listener that dies before it prints its port fails this direction
  # alone; `set -e` must not end the script before the other one runs.
  if ! read -r port <&"${LISTEN[0]}" || [[ -z $port ]]; then
    local listen_ok=0
    wait "$pid" || listen_ok=$?
    echo "FAIL $name (the listener printed no port, exit $listen_ok)"
    return 1
  fi
  local dial_ok=0 listen_ok=0
  timeout 120 "$dialer" "$dial_mode" "$port" || dial_ok=$?
  wait "$pid" || listen_ok=$?
  if [[ $dial_ok -eq 0 && $listen_ok -eq 0 ]]; then
    echo "PASS $name"
  else
    echo "FAIL $name (dialer $dial_ok, listener $listen_ok)"
    return 1
  fi
}

status=0
run "lean dials go" "$go" listen "$lean" dial || status=1
run "go dials lean" "$lean" listen "$go" dial || status=1
# Each refusal passes when the refusing side answers its own refusal
# and the other side receives the alert bad_certificate.
run "go dials lean without the extension" "$lean" listen-noext "$go" dial-noext || status=1
run "go dials lean with a chain of two" "$lean" listen-chain "$go" dial-chain || status=1
run "lean dials an expired go server" "$go" listen-expired "$lean" dial-refuse || status=1
run "lean dials go without the extension" "$go" listen-refuse "$lean" dial-noext || status=1
# A peer with no ALPN reads as "libp2p", with no inlined muxer.
run "go dials lean without ALPN" "$lean" listen "$go" dial-noalpn || status=1
run "lean dials go without ALPN" "$go" listen-noalpn "$lean" dial || status=1
exit $status
