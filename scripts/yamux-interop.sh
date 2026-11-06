#!/usr/bin/env bash
# The yamux interop check (packages/net/yamux/docs/PLAN.md): this
# package's session against go-yamux v5.1.0, the version go-libp2p v0.50
# pins, over plain loopback TCP, in both directions. Each run moves four
# concurrent streams of 1 MiB + 7 bytes each way, past the 256 KiB
# window, with a half-close before every echo and a ping.
#
# Go builds offline from the module cache; run `go mod download` in
# scripts/yamux-interop once on a machine that lacks it.
set -euo pipefail

root=$(cd "$(dirname "$0")/.." && pwd)
out="$root/.tmp/yamux-interop"
mkdir -p "$out"

# Both builds run on two cores at the lowest priority, so the check can
# run beside other work on the machine.
( cd "$root/scripts/yamux-interop" &&
  GOPROXY=off GOSUMDB=off nice -n19 taskset -c 0,1 go build -p 2 -o "$out/go-peer" . )
( cd "$root" &&
  LEAN_NUM_THREADS=2 nice -n19 taskset -c 0,1 lake build yamux-interop >"$out/lake.out" )
lean="$root/.lake/build/bin/yamux-interop"
go="$out/go-peer"

# $1 listens and prints its port; $2 dials that port.
run() {
  local name=$1 listener=$2 dialer=$3
  coproc LISTEN { timeout 120 "$listener" listen; }
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
  timeout 120 "$dialer" dial "$port" || dial_ok=$?
  wait "$pid" || listen_ok=$?
  if [[ $dial_ok -eq 0 && $listen_ok -eq 0 ]]; then
    echo "PASS $name"
  else
    echo "FAIL $name (dialer $dial_ok, listener $listen_ok)"
    return 1
  fi
}

status=0
run "lean dials go" "$go" "$lean" || status=1
run "go dials lean" "$lean" "$go" || status=1
exit $status
