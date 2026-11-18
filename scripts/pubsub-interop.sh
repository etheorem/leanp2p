#!/usr/bin/env bash
# The gossipsub interop check (etheorem/leanp2p#110): our gossipsub node
# against a go-libp2p-pubsub v0.19.0 node over go-libp2p v0.51.0, on plain
# loopback TCP, in both directions.
#
# Each run meshes the two nodes on the topic "interop", and each side must
# get a message from the other. Before that topic, our node subscribes to
# BURST filler topics, as a consensus node subscribes to many topics at
# once. A burst past the go peer's queue drops subscription records, and
# our node must send them again for go to learn "interop".
#
# Go builds offline from the module cache; run `go mod download` in
# scripts/pubsub-interop once on a machine that lacks it.
set -euo pipefail

root=$(cd "$(dirname "$0")/.." && pwd)
out="$root/.tmp/pubsub-interop"
mkdir -p "$out"

# Both builds run on two cores at the lowest priority, so the check can
# run beside other work on the machine.
( cd "$root/scripts/pubsub-interop" &&
  GOPROXY=off GOSUMDB=off nice -n19 taskset -c 0,1 go build -p 2 -o "$out/go-peer" . )
( cd "$root" &&
  LEAN_NUM_THREADS=2 nice -n19 taskset -c 0,1 lake build pubsub-interop >"$out/lake.out" )
lean="$root/.lake/build/bin/pubsub-interop"
go="$out/go-peer"

# Wait for the loopback ADDR line of a node's output file, and print it.
addr_of() {
  local file=$1 a=
  for _ in $(seq 1 100); do
    a=$(sed -n 's/^ADDR \(\/ip4\/127\.0\.0\.1\/.*\)$/\1/p' "$file" | head -n 1)
    [[ -n "$a" ]] && { echo "$a"; return 0; }
    sleep 0.1
  done
  return 1
}

# $1 names the run, $2 is lean-dials or go-dials, and $3 is the burst.
run() {
  local name=$1 way=$2 burst=$3
  local gout="$out/$name-go.out" lout="$out/$name-lean.out"
  local go_ok=0 lean_ok=0 a
  if [[ $way == lean-dials ]]; then
    timeout 60 "$go" -timeout 50 >"$gout" 2>"$out/$name-go.err" &
    local pid=$!
    if ! a=$(addr_of "$gout"); then
      echo "FAIL $name (the go node printed no address)"
      kill "$pid" 2>/dev/null || true
      return 1
    fi
    timeout 60 "$lean" dial "$a" "$burst" >"$lout" 2>"$out/$name-lean.err" || lean_ok=$?
    wait "$pid" || go_ok=$?
  else
    timeout 60 "$lean" listen "$burst" >"$lout" 2>"$out/$name-lean.err" &
    local pid=$!
    if ! a=$(addr_of "$lout"); then
      echo "FAIL $name (the Lean node printed no address)"
      kill "$pid" 2>/dev/null || true
      return 1
    fi
    timeout 60 "$go" -connect "$a" -timeout 50 >"$gout" 2>"$out/$name-go.err" || go_ok=$?
    wait "$pid" || lean_ok=$?
  fi
  if [[ $go_ok -eq 0 && $lean_ok -eq 0 ]]; then
    echo "PASS $name (go got $(grep -c '^GOT from-lean' "$gout"), lean got $(grep -c '^LEAN-GOT from-go' "$lout"), lean dropped $(sed -n 's/^DROPPED //p' "$lout"))"
  else
    echo "FAIL $name (go $go_ok, lean $lean_ok)"
    return 1
  fi
}

status=0
run "lean-dials" lean-dials 0 || status=1
run "go-dials" go-dials 0 || status=1
run "lean-dials-burst" lean-dials 250 || status=1
run "go-dials-burst" go-dials 250 || status=1
exit $status
