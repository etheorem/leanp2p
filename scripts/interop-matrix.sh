#!/usr/bin/env bash
# The W5.9 gate (root PLAN W5.9; packages/cli/docs/PLAN.md, "Test
# milestones (unit 2)"): the transport-interop matrix against go-libp2p
# over tcp + /noise + yamux, plus the silent-peer and slow-reader
# scenarios. Docker appears here and nowhere else (cli ARCHITECTURE,
# "Decisions").
#
# The go side is go-libp2p's own test-plan peer, built from the vendored
# tree (vendor/go-libp2p, v0.50.0) with its own PingDockerfile. Redis and
# the go containers share one docker network. The Lean `interop` binary
# runs on this host: it listens on the network's gateway address, which
# the containers reach, and it reaches Redis through a port published on
# loopback.
#
# Usage: scripts/interop-matrix.sh [out-dir]
#   LEAN_INTEROP   the harness binary (default .lake/build/bin/interop)
#   TEST_TIMEOUT   test_timeout_seconds of every run (default 60)
# The dialer lines and a results table land in out-dir (default
# .tmp/interop). The script exits nonzero when a cell fails.
set -euo pipefail

root=$(cd "$(dirname "$0")/.." && pwd)
lean=${LEAN_INTEROP:-$root/.lake/build/bin/interop}
timeout_s=${TEST_TIMEOUT:-60}
out=${1:-$root/.tmp/interop}
net=leanp2p-interop
redis=leanp2p-interop-redis
go_listener=leanp2p-interop-go-listener
go_image=leanp2p-interop-go
slow_image=leanp2p-interop-slowreader
# The unauthenticated-phase deadline of root §5.4 (Streams.unauthDeadlineMs).
unauth_s=30

mkdir -p "$out"
results="$out/results.csv"
echo "name,outcome,record" >"$results"
failed=0
lean_pid=

remove_container() {
  if docker container inspect "$1" >/dev/null 2>/dev/null; then
    docker rm -f "$1" >/dev/null
  fi
}

cleanup() {
  if [ -n "$lean_pid" ]; then kill "$lean_pid" 2>/dev/null || true; fi
  remove_container "$go_listener"
  remove_container "$redis"
  if docker network inspect "$net" >/dev/null 2>/dev/null; then
    docker network rm "$net" >/dev/null
  fi
}
trap cleanup EXIT

[ -x "$lean" ] || { echo "interop-matrix: build the harness first: lake build interop" >&2; exit 2; }

echo "building the go peers (vendor/go-libp2p $(cat "$root/vendor/go-libp2p/.pin"))" >&2
docker build -q -t "$go_image" -f "$root/vendor/go-libp2p/test-plans/PingDockerfile" \
  "$root/vendor/go-libp2p" >/dev/null
docker build -q -t "$slow_image" -f "$root/scripts/interop-slowreader/Dockerfile" \
  --build-context slowreader="$root/scripts/interop-slowreader" "$root/vendor/go-libp2p" >/dev/null

cleanup
docker network create "$net" >/dev/null
gateway=$(docker network inspect -f '{{(index .IPAM.Config 0).Gateway}}' "$net")
docker run -d --rm --name "$redis" --network "$net" -p 127.0.0.1::6379 redis:7-alpine >/dev/null
redis_host=$(docker port "$redis" 6379/tcp)
# The readiness wait has a bound, like every wait in this script: a
# server that never answers PING fails the run, and the script exits
# instead of hanging CI.
waited=0
until docker exec "$redis" redis-cli PING >/dev/null 2>/dev/null; do
  [ "$waited" -lt 100 ] || { echo "interop-matrix: redis did not answer PING" >&2; exit 2; }
  sleep 0.1
  waited=$((waited + 1))
done

# The test plan's variables, for one side. $1 is_dialer, $2 redis_addr.
plan_env() {
  echo "transport=tcp muxer=yamux security=noise is_dialer=$1 redis_addr=$2 test_timeout_seconds=$timeout_s"
}

start_lean_listener() {
  # shellcheck disable=SC2046  # the words of plan_env are the variables
  env $(plan_env false "$redis_host") ip="$gateway" "$lean" 2>"$out/$1.listener.log" &
  lean_pid=$!
}

start_go_listener() {
  docker run -d --rm --name "$go_listener" --network "$net" \
    -e transport=tcp -e muxer=yamux -e security=noise -e is_dialer=false \
    -e redis_addr="$redis:6379" -e test_timeout_seconds="$timeout_s" "$go_image" >/dev/null
}

stop_listeners() {
  if [ -n "$lean_pid" ]; then kill "$lean_pid" 2>/dev/null || true; wait "$lean_pid" 2>/dev/null || true; lean_pid=; fi
  remove_container "$go_listener"
}

run_lean_dialer() {
  # shellcheck disable=SC2046
  timeout $((timeout_s + 10)) env $(plan_env true "$redis_host") "$lean" >"$out/$1.json" 2>"$out/$1.dialer.log"
}

run_go_dialer() {
  timeout $((timeout_s + 10)) docker run --rm --network "$net" \
    -e transport=tcp -e muxer=yamux -e security=noise -e is_dialer=true \
    -e redis_addr="$redis:6379" -e test_timeout_seconds="$timeout_s" "$go_image" \
    >"$out/$1.json" 2>"$out/$1.dialer.log"
}

# One CSV field: the value in double quotes, each inner quote doubled.
csv() { local v=${1//\"/\"\"}; printf '"%s"' "$v"; }

# Record one result. $1 the file stem, $2 the name, $3 the exit status,
# then the JSON keys the output line must carry. A pass needs exit 0
# and every key.
verdict() {
  local file=$1 name=$2 status=$3 line= key ok=1 outcome=success
  shift 3
  [ "$status" = 0 ] || ok=0
  [ -s "$out/$file.json" ] && line=$(tr -d '\n' <"$out/$file.json")
  for key in "$@"; do [[ $line == *"\"$key\""* ]] || ok=0; done
  if [ "$ok" = 1 ]; then
    echo "PASS $name $line" >&2
  else
    outcome=failure
    echo "FAIL $name (exit $status; see $out/$file.*.log)" >&2
    failed=$((failed + 1))
  fi
  echo "$(csv "$name"),$outcome,$(csv "$line")" >>"$results"
}

# One cell of the matrix: $1 dialer (lean|go), $2 listener (lean|go).
cell() {
  local file="$1-x-$2" status=0
  docker exec "$redis" redis-cli FLUSHALL >/dev/null
  "start_$2_listener" "$file"
  "run_$1_dialer" "$file" || status=$?
  stop_listeners
  verdict "$file" "$1 x $2 (tcp, noise, yamux)" "$status" handshakePlusOneRTTMillis pingRTTMilllis
}

# The listener's published address, once it is in Redis.
published_addr() {
  local addr= waited=0
  while [ -z "$addr" ] && [ "$waited" -lt $((timeout_s * 10)) ]; do
    addr=$(docker exec "$redis" redis-cli LINDEX listenerAddr 0)
    [ -n "$addr" ] || { sleep 0.1; waited=$((waited + 1)); }
  done
  echo "$addr"
}

# The silent peer (PRINCIPLES 5.4): a raw TCP connection that sends
# nothing. The Lean listener must close it at the deadline of §5.4, and a
# go dialer must pass meanwhile.
silent_peer() {
  local name=silent-peer status=0 addr ip port start elapsed
  docker exec "$redis" redis-cli FLUSHALL >/dev/null
  start_lean_listener "$name"
  addr=$(published_addr)
  if [ -z "$addr" ]; then
    echo "$name: the Lean listener published no address" >&2
    stop_listeners
    verdict "$name" "$name" 1
    return
  fi
  IFS=/ read -r _ _ ip _ port _ <<<"$addr"
  start=$(date +%s)
  # The client keeps its write side open, sends nothing, and reads until
  # the listener closes the connection.
  timeout $((unauth_s + 15)) bash -c 'exec 3<>"/dev/tcp/$0/$1"; cat <&3 >/dev/null' "$ip" "$port" &
  local silent=$!
  run_go_dialer "$name" || status=$?
  local silent_status=0
  wait "$silent" || silent_status=$?
  elapsed=$(( $(date +%s) - start ))
  stop_listeners
  if [ "$silent_status" != 0 ] || [ "$elapsed" -lt $((unauth_s - 2)) ]; then
    echo "$name: the silent connection ended with $silent_status after ${elapsed}s" >&2
    status=1
  else
    echo "$name: the silent connection closed after ${elapsed}s" >&2
  fi
  verdict "$name" "$name" "$status" handshakePlusOneRTTMillis pingRTTMilllis
}

# The slow reader: a go peer that writes on a ping stream and never reads
# the echoes (scripts/interop-slowreader/main.go).
slow_reader() {
  local name=slow-reader status=0
  docker exec "$redis" redis-cli FLUSHALL >/dev/null
  start_lean_listener "$name"
  timeout $((timeout_s + 10)) docker run --rm --network "$net" \
    -e redis_addr="$redis:6379" -e test_timeout_seconds="$timeout_s" "$slow_image" \
    >"$out/$name.json" 2>"$out/$name.dialer.log" || status=$?
  stop_listeners
  verdict "$name" "$name" "$status" stalledAfterBytes pingRTTMillis
}

# The go x go cell checks the setup itself.
cell go go
cell lean go
cell go lean
cell lean lean
silent_peer
slow_reader

echo "$failed failed; results in $results" >&2
[ "$failed" = 0 ]
