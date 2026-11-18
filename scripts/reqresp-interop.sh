#!/usr/bin/env bash
# The req/resp interop check (packages/libp2p/protocols/docs/PLAN.md):
# this package's req/resp over the Lean host against a go-libp2p host
# that frames every payload with prysm's own ssz_snappy encoder, over
# loopback TCP with Noise and yamux, in both directions. Each run requests
# Status v1 and BeaconBlocksByRange v2 (three blocks, one past a snappy
# frame, with ForkDigest contexts), then BlocksByRange with a count of 0,
# which draws one InvalidRequest chunk, and ends with a /test/done stream
# that tells the listener to close. When go answers, it fails the run if
# its close after the last chunk fails, as it does when the requester
# resets the stream first.
#
# Go builds offline from the module cache; run `go mod download` in
# scripts/reqresp-interop once on a machine that lacks it.
set -euo pipefail

root=$(cd "$(dirname "$0")/.." && pwd)
out="$root/.tmp/reqresp-interop"
mkdir -p "$out"

# Both builds run on two cores at the lowest priority, so the check can
# run beside other work on the machine.
( cd "$root/scripts/reqresp-interop" &&
  GOPROXY=off GOSUMDB=off nice -n19 taskset -c 0,1 go build -p 2 -o "$out/go-peer" . )
( cd "$root" &&
  LEAN_NUM_THREADS=2 nice -n19 taskset -c 0,1 lake build reqresp-interop >"$out/lake.out" )
lean="$root/.lake/build/bin/reqresp-interop"
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
