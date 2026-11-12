#!/usr/bin/env bash
# The QUIC interop check (packages/libp2p/quic/docs/PLAN.md, unit 1):
# a Host with the QUIC transport against go-libp2p v0.50.0's own host
# with its QUIC transport (quic-go v0.62.0), over loopback UDP, in both
# directions. Each run checks both TLS certificates and peer ids, checks
# that the go host's identify of the Lean host records its agent and its
# protocols, dials with the listener's peer id, negotiates a stream
# whose first proposal draws `na`, echoes 2 MiB on it, and ends
# with a /test/done stream that tells the listener to close. A third run
# has the Lean host dial a go listener that answers with a Retry. The
# last four check the tls.md "Peer Authentication" MUSTs between the two
# sides (scripts/quic-interop/refuse.go): each side refuses the other's
# broken certificates inside the handshake, each refusal ends in its TLS
# alert, and the Lean dialer sends no server name.
#
# Go builds offline from the module cache; run `go mod download` in
# scripts/quic-interop once on a machine that lacks it.
set -euo pipefail

root=$(cd "$(dirname "$0")/.." && pwd)
out="$root/.tmp/quic-interop"
mkdir -p "$out"

# Both builds run on two cores at the lowest priority, so the check can
# run beside other work on the machine.
( cd "$root/scripts/quic-interop" &&
  GOPROXY=off GOSUMDB=off nice -n19 taskset -c 0,1 go build -p 2 -o "$out/go-peer" . )
( cd "$root" &&
  LEAN_NUM_THREADS=2 nice -n19 taskset -c 0,1 lake build quic-interop >"$out/lake.out" )
lean="$root/.lake/build/bin/quic-interop"
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
# The go listener answers the first Initial with a Retry, as a go node
# under load does; the client must take it (RFC 9000 §17.2.5.2).
run "lean dials go, with a Retry" "$go" listen-retry "$lean" dial || status=1
# Go dials with no certificate (certificate_required), without the
# extension, and with a chain of two (bad_certificate), then dials as
# `dial` does.
run "lean refuses go's broken dials" "$lean" listen "$go" dial-refused || status=1
# Lean dials without the extension and with a chain of two, and go
# answers bad_certificate; then Lean dials as `dial` does.
run "go refuses lean's broken dials" "$go" listen "$lean" dial-refused || status=1
run "lean dials go, and sends no server name" "$go" listen-sni "$lean" dial-handshake || status=1
run "lean refuses go's certificate without the extension" "$go" listen-badcert "$lean" dial-badcert || status=1
exit $status
