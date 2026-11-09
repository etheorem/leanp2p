# syntax=docker/dockerfile:1
# Built by scripts/interop-matrix.sh with vendor/go-libp2p as the context
# and this directory as the `slowreader` named context. The program joins
# go-libp2p's test-plans module, as its own ping program does
# (vendor/go-libp2p/test-plans/PingDockerfile).

FROM golang:1.27-alpine AS builder

WORKDIR /app/
COPY ./ .
COPY --from=slowreader main.go /app/test-plans/cmd/slowreader/main.go
WORKDIR /app/test-plans
RUN go mod download
RUN go build -o /slowreader ./cmd/slowreader

FROM alpine
COPY --from=builder /slowreader /slowreader
ENTRYPOINT [ "/slowreader" ]
