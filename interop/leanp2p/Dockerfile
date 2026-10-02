# leanp2p transport-interop image (VECTOR_TEST_PLAN.md, phase 5 step 25).
#
# Shape-compatible with libp2p/test-plans transport-interop: the entrypoint
# reads `transport`, `muxer`, `security`, `is_dialer`, `ip`, `redis_addr`,
# `test_timeout_seconds` from the environment; the listener RPUSHes its
# multiaddr on the `listenerAddr` Redis list, the dialer BLPOPs it, pings
# once and prints the timing JSON to stdout.
#
# Drop this directory into a fork of libp2p/test-plans as
# `impl/leanp2p/<version>/` and build with the sibling Makefile.
#
# Single stage on purpose: the lean toolchain bundles the glibc the
# binaries link against, so building and running in the same base keeps
# the loader and `libcrypto.so.3` (absolute path in lakefile.lean) intact.
# Base: debian trixie - the toolchain bundles glibc 2.26 and links the
# system libcrypto by absolute path, so the base needs a glibc that still
# exports the @GLIBC_2.34 symbols trixie-era libcrypto references
# (bookworm/older-ubuntu do not; trixie matches the dev environment).
FROM debian:trixie-slim

ENV DEBIAN_FRONTEND=noninteractive
RUN apt-get update \
    && apt-get install -y --no-install-recommends \
       ca-certificates curl git xz-utils make \
       libgmp10 libssl3 libssl-dev libc6-dev \
    && rm -rf /var/lib/apt/lists/*

# elan + the pinned toolchain (lean-toolchain) bring the Lean compiler and
# the bundled clang/glibc used to compile c/p2pcrypto.c.
RUN curl -sSfL https://elan.lean-lang.org/elan-init.sh | sh -s -- -y \
    && /root/.elan/bin/elan toolchain install leanprover/lean4:v4.34.0
ENV PATH=/root/.elan/bin:$PATH

WORKDIR /src
COPY lakefile.lean lake-manifest.json lean-toolchain ./
COPY c/ c/
COPY LeanP2P/ LeanP2P/
COPY LeanP2P.lean Interop.lean ./
RUN lake build interop

# test-plans harness contract
ENV transport=tcp muxer=yamux security=noise is_dialer=false \
    ip=0.0.0.0 redis_addr=redis:6379 test_timeout_seconds=180
ENTRYPOINT ["/src/.lake/build/bin/interop"]
