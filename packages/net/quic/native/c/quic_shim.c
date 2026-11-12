/*
 * quic_shim.c: the ngtcp2 shim behind `net/quic`.
 *
 * One endpoint object holds every QUIC connection of one UDP socket. It
 * holds the ngtcp2 connections, the routing of a datagram to its
 * connection by connection ID, and the send buffer of each stream. It
 * also holds two queues for the Lean side: the events, and the
 * datagrams to send. The Lean loop owns the socket and the clock. It
 * feeds each datagram it reads, each command of the application, and
 * each timer expiry into the endpoint, then drains both queues
 * (packages/net/quic/docs/ARCHITECTURE.md, "The endpoint"). So the shim
 * opens no socket, starts no thread, and reads no clock. Every call
 * that needs the time takes it, in milliseconds of the caller's clock.
 *
 * The conventions, binding for every function below:
 *
 * - Every exported symbol carries the `leanp2p_quic_` prefix, and
 *   exactly one `@[extern]` declaration in `QuicNative.lean` reaches it.
 *   Lean v4.34 calls an `IO` extern with its declared arguments alone,
 *   no world token, and reads an IO result back.
 * - The shim borrows every argument (`b_lean_obj_arg`).
 * - One task calls an endpoint: the loop of `Quic/Endpoint.lean`. The
 *   endpoint has no lock, and a second caller is a bug of the Lean
 *   side.
 * - A connection is named by a handle, a number the endpoint gives it
 *   and never reuses. A handle that names no connection makes a command
 *   do nothing, so a command that races the end of its connection is
 *   harmless.
 * - The TLS handshake runs on the `SSL_CTX` of a `Tls.Context` from
 *   `net/tls`, so the TLS settings have one home (`tls_shim.h`). Each
 *   connection's `SSL` holds the caller's certificate check, which the
 *   context's verify callback runs inside the handshake, as for TLS over
 *   TCP. A refused certificate sends the alert that libssl raised, as
 *   the QUIC transport error 0x100 plus the alert (RFC 9001 §4.8).
 * - The numbers the endpoint sends (transport parameters, windows,
 *   timeouts) come from the Lean side at `leanp2p_quic_endpoint_new`.
 *   Their one home is `Quic/Constants.lean`.
 */

#include <lean/lean.h>

#include <errno.h>
#include <fcntl.h>
#include <pthread.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include <arpa/inet.h>
#include <netinet/in.h>
#include <sys/socket.h>

#include <ngtcp2/ngtcp2.h>
#include <ngtcp2/ngtcp2_crypto.h>
#include <ngtcp2/ngtcp2_crypto_ossl.h>

#include <openssl/err.h>
#include <openssl/rand.h>
#include <openssl/ssl.h>
#include <openssl/x509.h>

#include "tls_shim.h"

/* ------------------------------------------------------------------ */
/* Sizes of the shim's own buffers                                     */
/* ------------------------------------------------------------------ */

/* The length of the connection IDs this endpoint issues. */
#define SCID_LEN 16
/* The largest datagram the shim writes. ngtcp2 sends at most
   `max_tx_udp_payload_size` bytes, 1452 by default
   (`ngtcp2_settings_default`). */
#define MAX_DATAGRAM 1500
/* The packets one flush writes for one connection, so one busy
   connection cannot hold the loop. The next turn writes the rest. */
#define MAX_PACKETS_PER_FLUSH 256
/* The TLS alert `no_application_protocol` (RFC 8446 §6.2). */
#define ALERT_NO_APPLICATION_PROTOCOL 120
/* The largest reason text an end event carries. A longer reason is cut
   at this count of bytes; `Quic.reasonText` drops a character the cut
   splits. */
#define REASON_MAX 256
/* The length of the secret the Retry tokens of an endpoint derive their
   keys from (`ngtcp2_crypto_generate_retry_token2`). */
#define RETRY_SECRET_LEN 32
/* The buckets the connection ID table starts with; it doubles when it
   holds more IDs than buckets. */
#define CID_TABLE_START 64

/* The answers of the shim that are no value; `QuicNative.lean` holds the
   same numbers. */
#define WRITE_REFUSED UINT64_MAX   /* `leanp2p_quic_stream_write`: the stream takes no bytes */
#define OPEN_BLOCKED UINT64_MAX    /* `leanp2p_quic_open_stream`: the peer allows no more streams now */
#define OPEN_GONE (UINT64_MAX - 1) /* `leanp2p_quic_open_stream`: the connection is gone or not set up */
#define NO_EXPIRY UINT64_MAX       /* `leanp2p_quic_expiry`: no timer is set */
/* The `code` of a stream data event whose bytes the peer's FIN follows. */
#define STREAM_DATA_FIN 1

static uint64_t ns_of_ms(uint64_t ms) { return ms * 1000000ull; }

/* ------------------------------------------------------------------ */
/* Lean object helpers                                                 */
/* ------------------------------------------------------------------ */

static lean_object *mk_bytes(const uint8_t *p, size_t n) {
    lean_object *r = lean_alloc_sarray(1, n, n);
    if (n > 0) memcpy(lean_sarray_cptr(r), p, n);
    return r;
}

static lean_object *none(void) { return lean_box(0); }

static lean_object *some(lean_object *v) {
    lean_object *r = lean_alloc_ctor(1, 1, 0);
    lean_ctor_set(r, 0, v);
    return r;
}

/* ------------------------------------------------------------------ */
/* Addresses                                                           */
/* ------------------------------------------------------------------ */

/* An address crosses as bytes: the family (4 or 6), the address in
   network order (4 or 16 bytes), then the port, big-endian
   (`Quic/Address.lean`). */
static int addr_from_bytes(b_lean_obj_arg b, struct sockaddr_storage *ss, socklen_t *len) {
    const uint8_t *p = lean_sarray_cptr(b);
    size_t n = lean_sarray_size(b);
    memset(ss, 0, sizeof *ss);
    if (n == 7 && p[0] == 4) {
        struct sockaddr_in *a = (struct sockaddr_in *)ss;
        a->sin_family = AF_INET;
        memcpy(&a->sin_addr, p + 1, 4);
        a->sin_port = htons((uint16_t)(p[5] << 8 | p[6]));
        *len = sizeof *a;
        return 1;
    }
    if (n == 19 && p[0] == 6) {
        struct sockaddr_in6 *a = (struct sockaddr_in6 *)ss;
        a->sin6_family = AF_INET6;
        memcpy(&a->sin6_addr, p + 1, 16);
        a->sin6_port = htons((uint16_t)(p[17] << 8 | p[18]));
        *len = sizeof *a;
        return 1;
    }
    return 0;
}

static lean_object *addr_to_bytes(const struct sockaddr_storage *ss) {
    uint8_t buf[19];
    if (ss->ss_family == AF_INET) {
        const struct sockaddr_in *a = (const struct sockaddr_in *)ss;
        uint16_t port = ntohs(a->sin_port);
        buf[0] = 4;
        memcpy(buf + 1, &a->sin_addr, 4);
        buf[5] = (uint8_t)(port >> 8);
        buf[6] = (uint8_t)port;
        return mk_bytes(buf, 7);
    }
    const struct sockaddr_in6 *a = (const struct sockaddr_in6 *)ss;
    uint16_t port = ntohs(a->sin6_port);
    buf[0] = 6;
    memcpy(buf + 1, &a->sin6_addr, 16);
    buf[17] = (uint8_t)(port >> 8);
    buf[18] = (uint8_t)port;
    return mk_bytes(buf, 19);
}

/* ------------------------------------------------------------------ */
/* The exclusive bind                                                  */
/* ------------------------------------------------------------------ */

/* Lean v4.34 binds every UDP socket with `UV_UDP_REUSEADDR`
   (vendor/lean4/src/runtime/uv/udp.cpp, line 106), and `Std.Async.UDP` has
   no bind without it. On Linux, SO_REUSEADDR lets a port-0 bind take a
   port that another socket already holds, and the kernel then gives
   each datagram to one of the two. One connection then receives another
   connection's packets, and the loop's wake datagram can reach the
   wrong socket (packages/net/quic/docs/ARCHITECTURE.md, "Decisions",
   the exclusive bind). So the shim opens and binds the socket itself,
   with no reuse option. It then hands the descriptor to the libuv
   handle inside Lean's socket object.

   Three facts of the toolchain hold this up. A toolchain bump re-checks
   each one before it lifts the guard below:
   - the first field of `lean_uv_udp_socket_object` is the `uv_udp_t`
     pointer (vendor/lean4/src/runtime/uv/udp.h, line 26);
   - `lean_uv_udp_new` makes the handle with `uv_udp_init`, which opens
     no descriptor (vendor/lean4/src/runtime/uv/udp.cpp, line 79), so
     `uv_udp_open` takes ours;
   - libuv's `uv_udp_open` sets the reuse option on the descriptor it
     takes (libuv v1.48.0, src/unix/udp.c, line 1040, `uv__set_reuse`),
     so the shim clears that option again after the call. */
#if !(LEAN_VERSION_MAJOR == 4 && LEAN_VERSION_MINOR == 34)
#error "quic_shim.c: re-check the exclusive bind against src/runtime/uv/udp.h, src/runtime/uv/udp.cpp, and the toolchain's libuv uv_udp_open (packages/net/quic/docs/ARCHITECTURE.md, the exclusive bind)"
#endif

/* libuv ships in the toolchain's libuv.a with no header. The handle is
   an opaque pointer, and `uv_os_sock_t` is int on Unix. */
extern int uv_udp_open(void *handle, int sock);

static lean_obj_res errno_error(int e) {
    return lean_io_result_mk_error(lean_decode_io_error(e, NULL));
}

/* Bind the Lean socket `sock` (`Std.Internal.UV.UDP.Socket`) to the
   address bytes `addr`, with no address reuse. The caller calls it once,
   on a socket fresh from `Std.Async.UDP.Socket.mk`, before any receive
   or send: libuv's loop thread then never touches the handle, so the
   call needs no loop lock. A port another socket holds fails with
   EADDRINUSE. */
LEAN_EXPORT lean_obj_res leanp2p_quic_udp_bind(b_lean_obj_arg sock, b_lean_obj_arg addr) {
    struct sockaddr_storage ss;
    socklen_t len;
    if (!addr_from_bytes(addr, &ss, &len)) return errno_error(EINVAL);
    int fd = socket(ss.ss_family, SOCK_DGRAM, 0);
    if (fd < 0) return errno_error(errno);
    if (fcntl(fd, F_SETFD, FD_CLOEXEC) != 0 || bind(fd, (struct sockaddr *)&ss, len) != 0) {
        int e = errno;
        close(fd);
        return errno_error(e);
    }
    void **object = (void **)lean_get_external_data(sock);
    int rv = uv_udp_open(object[0], fd);
    if (rv != 0) {
        /* libuv's error codes on Unix are the negated errno values. */
        close(fd);
        return errno_error(-rv);
    }
    /* The handle owns the descriptor now, and the runtime's finalizer
       closes it. libuv set the reuse option; clear it, so no later bind
       can share the port. */
    int off = 0;
    if (setsockopt(fd, SOL_SOCKET, SO_REUSEADDR, &off, sizeof off) != 0) return errno_error(errno);
#ifdef SO_REUSEPORT
    if (setsockopt(fd, SOL_SOCKET, SO_REUSEPORT, &off, sizeof off) != 0) return errno_error(errno);
#endif
    return lean_io_result_mk_ok(lean_box(0));
}

/* ------------------------------------------------------------------ */
/* Events and outgoing datagrams                                       */
/* ------------------------------------------------------------------ */

/* The event kinds; `QuicNative.EventKind` holds the same numbers. A
   connection ends with exactly one of the last seven. */
enum {
    EV_HANDSHAKE_DONE = 1, /* data: the peer's certificate, DER */
    EV_STREAM_OPENED = 2,  /* the peer opened `stream` */
    EV_STREAM_DATA = 3,    /* data: the bytes; code 1 when the peer's FIN follows them */
    EV_STREAM_RESET = 4,   /* the peer reset its sending part of `stream`; code: the app error */
    EV_STREAM_STOPPED = 5, /* the peer will read no more of `stream`; code: the app error */
    EV_STREAM_CLOSED = 6,  /* both directions of `stream` are over */
    EV_STREAM_ACKED = 7,   /* code: the bytes of `stream` the peer has not acknowledged */
    EV_OPEN_CREDIT = 8,    /* the peer allows more streams of ours */
    EV_CONN_CLOSED = 9,    /* an application close, ours or the peer's; code: its error, 0 orderly */
    EV_CONN_REFUSED = 10,  /* our TLS refused the peer's certificate; data: the reason */
    EV_CONN_FAILED = 11,   /* we closed on a transport error; code: the error we sent */
    EV_PEER_FAILED = 12,   /* the peer closed on a transport error; code: its error */
    EV_CONN_TIMEOUT = 13,  /* the handshake did not finish in time */
    EV_CONN_IDLE = 14,     /* the idle timer ended the connection */
    EV_CONN_DROPPED = 15   /* the connection ended with no CONNECTION_CLOSE */
};

typedef struct event {
    struct event *next;
    uint8_t kind;
    uint64_t conn;
    int64_t stream;
    uint64_t code;
    uint8_t *data;
    size_t len;
    int inline_data; /* `data` points into the event's own block (`end_event`) */
} event;

/* The end event of a connection, with room for its reason. Each
   connection allocates its own when it is made. So the end of a
   connection always reaches the Lean side, also when memory runs out.
   A lost end event would leave every view of the connection parked. */
typedef struct end_event {
    event ev;
    uint8_t reason[REASON_MAX];
} end_event;

typedef struct packet {
    struct packet *next;
    struct sockaddr_storage to;
    size_t len;
    uint8_t data[MAX_DATAGRAM];
} packet;

/* ------------------------------------------------------------------ */
/* Streams                                                             */
/* ------------------------------------------------------------------ */

/* A chunk of a stream's send buffer. ngtcp2 keeps pointers into the
   bytes it has sent until the peer acknowledges them, so a chunk never
   moves. The shim frees it once the peer acknowledges every byte. */
typedef struct chunk {
    struct chunk *next;
    uint64_t off; /* the stream offset of data[0] */
    size_t len;
    uint8_t data[];
} chunk;

typedef struct qstream {
    struct qstream *next;
    int64_t id;
    chunk *head, *tail;
    chunk *cursor;      /* the chunk the next send starts in */
    size_t cursor_pos;  /* the position in `cursor` */
    uint64_t end_off;   /* the offset after the last buffered byte */
    uint64_t acked_off; /* the offset below which the peer acknowledged everything */
    int fin_wanted;     /* the application closed its write direction */
    int fin_sent;
    int write_shut;     /* a reset of ours or a STOP_SENDING of the peer ended our writes */
    uint64_t blocked_round; /* the flush that found the stream blocked last */
} qstream;

/* ------------------------------------------------------------------ */
/* Connections and the endpoint                                        */
/* ------------------------------------------------------------------ */

/* The numbers of `Quic/Constants.lean`, which the Lean side passes to
   `leanp2p_quic_endpoint_new`. */
typedef struct {
    uint64_t max_streams_bidi;
    uint64_t stream_window;     /* the initial stream receive window */
    uint64_t stream_window_max; /* the window auto-tuning grows to */
    uint64_t conn_window;
    uint64_t conn_window_max;
    uint64_t idle_timeout_ms;
    uint64_t keep_alive_ms;
    uint64_t handshake_timeout_ms;
    uint64_t max_handshakes;    /* the server connections in their handshake at once */
    uint64_t retry_threshold;   /* past this count, a new client proves its address first */
    uint64_t max_closed;        /* the closing periods a listening endpoint keeps at once */
    uint64_t connection_refused; /* the transport error CONNECTION_REFUSED */
    uint64_t invalid_token;      /* the transport error INVALID_TOKEN */
} params;

struct endpoint;
struct qconn;
struct closed_conn;

/* One entry of the connection ID table: an ID, and the connection or the
   closing period it routes to. Each entry is also on the list of its
   owner (`keys`), so the owner's end removes its IDs without a scan. */
typedef struct cid_entry {
    struct cid_entry *next;     /* the next entry of the bucket */
    struct cid_entry *next_own; /* the next entry of the same owner */
    ngtcp2_cid cid;
    struct qconn *conn;         /* the owner, a live connection; or NULL */
    struct closed_conn *closed; /* the owner, a closing period; or NULL */
} cid_entry;

/* The connection ID table of an endpoint: buckets of entries, by a hash
   of the ID under a random seed. The peer chooses the IDs it looks up,
   so the seed keeps it from aiming every lookup at one bucket. The IDs
   it can insert are the first DCIDs of its handshakes, which
   `max_handshakes` bounds. */
typedef struct {
    cid_entry **buckets;
    size_t nbuckets;
    size_t count;
    uint64_t seed;
} cid_table;

/* A connection of a listening endpoint that we closed, kept for its
   closing period (RFC 9000 §10.2): its IDs, the client's first DCID, and
   the CONNECTION_CLOSE we sent. A packet for one of the IDs gets the
   close again, on the 1st, 2nd, 4th, 8th, ... packet, as quic-go's
   `closedLocalConn` does. So a lost close reaches the peer, and a client
   whose refusal was lost gets the refusal again in place of a second
   handshake. The record holds no ngtcp2 state; the connection itself is
   freed at once. The endpoint keeps at most `max_closed` records, and a
   new one past that count replaces the oldest. A dropped record costs
   only the resend: the peer still ends the connection by its own idle
   timer. */
typedef struct closed_conn {
    struct closed_conn *next;
    cid_entry *keys; /* its IDs in the endpoint's table */
    uint8_t pkt[MAX_DATAGRAM];
    size_t pktlen;
    uint64_t until_ms; /* the end of the closing period, 3 PTO from the close */
    uint32_t seen;     /* the packets that came for the record */
} closed_conn;

typedef struct qconn {
    struct qconn *next;
    struct endpoint *ep;
    uint64_t handle;
    ngtcp2_conn *conn;
    SSL *ssl;
    ngtcp2_crypto_ossl_ctx *octx;
    ngtcp2_crypto_conn_ref ref;
    /* The peer's address at the start, behind `path`. ngtcp2 keeps the
       current path from there (`ngtcp2_conn_get_path2`), and the shim
       never changes these. */
    struct sockaddr_storage remote;
    socklen_t remote_len;
    ngtcp2_path path;
    /* The DCID of the client's Initial that made a server connection: its
       first DCID, or the SCID of our Retry. Its first packets carry it. */
    ngtcp2_cid odcid;
    int is_server;
    int no_alpn;       /* the handshake completed with no ALPN protocol */
    int reset_seen;    /* a stateless reset ended the connection */
    int closed;        /* set once; the next sweep frees the connection */
    int in_handshake;  /* a server connection that `handshaking` counts */
    uint64_t started_ms; /* the caller's time at the start: ngtcp2's `initial_ts` */
    uint64_t flush_round; /* the count of flushes, which marks a blocked stream's flush */
    qstream *streams;
    cid_entry *keys;   /* its IDs in the endpoint's table, until it is closed */
    end_event *end;    /* its end event, made with it (`end_event`) */
} qconn;

typedef struct endpoint {
    lean_object *tls; /* one reference to the `Tls.Context` object */
    params p;
    struct sockaddr_storage local;
    socklen_t local_len;
    int accept;       /* this endpoint takes new connections */
    int listening;    /* the endpoint of a listener; set once, as `accept` is cleared at its close */
    uint64_t next_handle;
    qconn *conns;
    cid_table ids;    /* every live ID: of the connections, and of the closing periods */
    uint64_t handshaking; /* the server connections in their handshake */
    /* The closing periods of its closed connections, oldest first. */
    closed_conn *closed, *closed_tail;
    uint64_t nclosed;
    uint8_t retry_secret[RETRY_SECRET_LEN]; /* random, from the endpoint's start */
    event *ev_head, *ev_tail;
    packet *pk_head, *pk_tail;
    uint64_t now_ms;  /* the time of the call in progress */
} endpoint;

static void queue_event(endpoint *ep, event *e) {
    if (ep->ev_tail) ep->ev_tail->next = e; else ep->ev_head = e;
    ep->ev_tail = e;
}

static void free_event(event *e) {
    if (!e->inline_data) free(e->data);
    free(e);
}

/* Queue an event of a live connection. The answer is 0, or -1 when
   memory ran out. The event is then lost, so the caller fails its
   ngtcp2 callback. The connection then ends with its own end event
   (`push_end`), which never needs memory. */
static int push_event(endpoint *ep, uint8_t kind, uint64_t conn, int64_t stream, uint64_t code,
                      const uint8_t *data, size_t len) {
    event *e = calloc(1, sizeof *e);
    if (e == NULL) return -1;
    if (len > 0) {
        e->data = malloc(len);
        if (e->data == NULL) {
            free(e);
            return -1;
        }
        memcpy(e->data, data, len);
        e->len = len;
    }
    e->kind = kind;
    e->conn = conn;
    e->stream = stream;
    e->code = code;
    queue_event(ep, e);
    return 0;
}

/* Queue the end event of a connection, from the block it was made with
   (`end_event`). A connection ends once (`closed`), so the block is used
   once. */
static void push_end(qconn *c, uint8_t kind, uint64_t code, const char *why) {
    end_event *ee = c->end;
    if (ee == NULL) return;
    c->end = NULL;
    size_t n = strlen(why);
    if (n > REASON_MAX) n = REASON_MAX;
    memcpy(ee->reason, why, n);
    ee->ev.data = ee->reason;
    ee->ev.len = n;
    ee->ev.inline_data = 1;
    ee->ev.kind = kind;
    ee->ev.conn = c->handle;
    ee->ev.stream = -1;
    ee->ev.code = code;
    queue_event(c->ep, &ee->ev);
}

/* Queue a datagram for `to`: the remote address of the path that ngtcp2
   chose for the packet (`ngtcp2_conn_writev_stream`, `path`). The
   address buffer behind `to` may be shorter than `sockaddr_storage`, so
   the copy takes `addrlen` bytes. When memory runs out the datagram is
   lost, as the network may lose it. ngtcp2's loss recovery sends its
   frames again (RFC 9002), and no state of ours depends on it. */
static void push_packet(endpoint *ep, const ngtcp2_addr *to, const uint8_t *data, size_t len) {
    packet *p = malloc(sizeof *p);
    if (p == NULL || len > MAX_DATAGRAM || to->addrlen > sizeof p->to) {
        free(p);
        return;
    }
    p->next = NULL;
    memset(&p->to, 0, sizeof p->to);
    memcpy(&p->to, to->addr, to->addrlen);
    p->len = len;
    memcpy(p->data, data, len);
    if (ep->pk_tail) ep->pk_tail->next = p; else ep->pk_head = p;
    ep->pk_tail = p;
}

static ngtcp2_tstamp now_ts(endpoint *ep) { return ns_of_ms(ep->now_ms); }

/* ------------------------------------------------------------------ */
/* The connection ID table                                             */
/* ------------------------------------------------------------------ */

/* FNV-1a over the ID, started from the table's random seed. */
static size_t cid_bucket(const cid_table *t, const uint8_t *data, size_t len) {
    uint64_t h = t->seed ^ 14695981039346656037ull;
    for (size_t i = 0; i < len; i++) {
        h ^= data[i];
        h *= 1099511628211ull;
    }
    return (size_t)(h & (t->nbuckets - 1));
}

static int cid_table_init(cid_table *t) {
    t->buckets = calloc(CID_TABLE_START, sizeof *t->buckets);
    if (t->buckets == NULL) return 0;
    t->nbuckets = CID_TABLE_START;
    t->count = 0;
    return RAND_bytes((unsigned char *)&t->seed, sizeof t->seed) == 1;
}

/* Double the buckets. When memory runs out the table keeps its size:
   the chains grow longer, and every lookup still answers right. */
static void cid_table_grow(cid_table *t) {
    size_t n = t->nbuckets * 2;
    cid_entry **b = calloc(n, sizeof *b);
    if (b == NULL) return;
    cid_entry **old = t->buckets;
    size_t oldn = t->nbuckets;
    t->buckets = b;
    t->nbuckets = n;
    for (size_t i = 0; i < oldn; i++) {
        cid_entry *e = old[i];
        while (e) {
            cid_entry *next = e->next;
            size_t k = cid_bucket(t, e->cid.data, e->cid.datalen);
            e->next = b[k];
            b[k] = e;
            e = next;
        }
    }
    free(old);
}

/* The entry of the ID `data`, or NULL. */
static cid_entry *cid_find(const cid_table *t, const uint8_t *data, size_t len) {
    for (cid_entry *e = t->buckets[cid_bucket(t, data, len)]; e; e = e->next)
        if (e->cid.datalen == len && memcmp(e->cid.data, data, len) == 0) return e;
    return NULL;
}

/* Add the ID `cid` for its owner, a connection or a closing period, and
   put the entry on the owner's list `own`. The answer is 0; 1 when the
   ID already has an owner, which keeps it; or -1 when memory ran out. */
static int cid_add(cid_table *t, const ngtcp2_cid *cid, qconn *conn, closed_conn *closed,
                   cid_entry **own) {
    if (cid_find(t, cid->data, cid->datalen) != NULL) return 1;
    cid_entry *e = calloc(1, sizeof *e);
    if (e == NULL) return -1;
    e->cid = *cid;
    e->conn = conn;
    e->closed = closed;
    size_t k = cid_bucket(t, cid->data, cid->datalen);
    e->next = t->buckets[k];
    t->buckets[k] = e;
    e->next_own = *own;
    *own = e;
    if (++t->count > t->nbuckets) cid_table_grow(t);
    return 0;
}

/* Take the entry `e` out of its bucket and free it. */
static void cid_unlink(cid_table *t, cid_entry *e) {
    for (cid_entry **p = &t->buckets[cid_bucket(t, e->cid.data, e->cid.datalen)]; *p;
         p = &(*p)->next) {
        if (*p == e) {
            *p = e->next;
            t->count--;
            break;
        }
    }
    free(e);
}

/* Remove the ID `cid` from the owner's list `own`, if it is there. */
static void cid_remove(cid_table *t, const ngtcp2_cid *cid, cid_entry **own) {
    for (cid_entry **p = own; *p; p = &(*p)->next_own) {
        cid_entry *e = *p;
        if (e->cid.datalen == cid->datalen && memcmp(e->cid.data, cid->data, cid->datalen) == 0) {
            *p = e->next_own;
            cid_unlink(t, e);
            return;
        }
    }
}

/* Remove every ID of an owner. */
static void cid_remove_all(cid_table *t, cid_entry **own) {
    while (*own) {
        cid_entry *e = *own;
        *own = e->next_own;
        cid_unlink(t, e);
    }
}

/* ------------------------------------------------------------------ */
/* Stream state                                                        */
/* ------------------------------------------------------------------ */

static qstream *find_stream(qconn *c, int64_t id) {
    for (qstream *s = c->streams; s; s = s->next)
        if (s->id == id) return s;
    return NULL;
}

static qstream *add_stream(qconn *c, int64_t id) {
    qstream *s = calloc(1, sizeof *s);
    if (s == NULL) return NULL;
    s->id = id;
    s->next = c->streams;
    c->streams = s;
    return s;
}

static void free_chunks(qstream *s) {
    chunk *k = s->head;
    while (k) {
        chunk *n = k->next;
        free(k);
        k = n;
    }
    s->head = s->tail = s->cursor = NULL;
}

static void remove_stream(qconn *c, int64_t id) {
    for (qstream **p = &c->streams; *p; p = &(*p)->next) {
        if ((*p)->id == id) {
            qstream *s = *p;
            *p = s->next;
            free_chunks(s);
            free(s);
            return;
        }
    }
}

static uint64_t buffered(const qstream *s) { return s->end_off - s->acked_off; }

/* ------------------------------------------------------------------ */
/* ngtcp2 callbacks                                                    */
/* ------------------------------------------------------------------ */

static ngtcp2_conn *get_conn(ngtcp2_crypto_conn_ref *ref) { return ((qconn *)ref->user_data)->conn; }

/* ngtcp2's own randomness: one byte that spaces the packet numbers it
   skips, an optimistic-ACK defense (`ngtcp2_conn.c`,
   `conn_update_skip_pkt`, the one call of `callbacks.rand`). The
   callback cannot fail, so a failed draw gives zero. Zero is the
   shortest gap, and still a valid one. The IDs, the tokens, and the
   Retry secret check their own draws. */
static void rand_cb(uint8_t *dest, size_t len, const ngtcp2_rand_ctx *ctx) {
    (void)ctx;
    if (RAND_bytes(dest, (int)len) != 1) memset(dest, 0, len);
}

/* A new connection ID and its stateless reset token, both random. The
   endpoint sends no stateless reset, so the token needs no secret to
   derive it again later (RFC 9000 §10.3). The ID goes into the
   endpoint's table; an ID that another owner holds is drawn again. */
static int new_cid_cb(ngtcp2_conn *conn, ngtcp2_cid *cid, ngtcp2_stateless_reset_token *token,
                      size_t cidlen, void *ud) {
    (void)conn;
    qconn *c = ud;
    uint8_t buf[NGTCP2_MAX_CIDLEN];
    if (cidlen > sizeof buf) return NGTCP2_ERR_CALLBACK_FAILURE;
    for (;;) {
        if (RAND_bytes(buf, (int)cidlen) != 1) return NGTCP2_ERR_CALLBACK_FAILURE;
        ngtcp2_cid_init(cid, buf, cidlen);
        int rv = cid_add(&c->ep->ids, cid, c, NULL, &c->keys);
        if (rv < 0) return NGTCP2_ERR_CALLBACK_FAILURE;
        if (rv == 0) break;
    }
    if (RAND_bytes(token->data, (int)sizeof token->data) != 1) return NGTCP2_ERR_CALLBACK_FAILURE;
    return 0;
}

/* ngtcp2 retired one of our connection IDs: it routes no more. */
static int remove_cid_cb(ngtcp2_conn *conn, const ngtcp2_cid *cid, void *ud) {
    (void)conn;
    qconn *c = ud;
    cid_remove(&c->ep->ids, cid, &c->keys);
    return 0;
}

/* A server connection leaves its handshake: done, or closed. */
static void leave_handshake(qconn *c) {
    if (!c->in_handshake) return;
    c->in_handshake = 0;
    c->ep->handshaking--;
}

/* The TLS handshake is done. RFC 9001 §8.1: "endpoints MUST
   immediately close a connection ... with a no_application_protocol TLS
   alert ... if an application protocol is not negotiated". ngtcp2's
   OpenSSL glue drives `SSL_do_handshake` directly, and libssl enforces
   QUIC's ALPN rule only in its own QUIC stack. So the shim checks here,
   and closes after the call that completed the handshake. */
static int handshake_completed_cb(ngtcp2_conn *conn, void *ud) {
    (void)conn;
    qconn *c = ud;
    leave_handshake(c);
    const unsigned char *alpn = NULL;
    unsigned int alen = 0;
    SSL_get0_alpn_selected(c->ssl, &alpn, &alen);
    if (alen == 0) {
        c->no_alpn = 1;
        return 0;
    }
    X509 *x = SSL_get0_peer_certificate(c->ssl);
    unsigned char *der = NULL;
    int n = x != NULL ? i2d_X509(x, &der) : -1;
    /* No certificate: the Lean side refuses the connection on the empty
       DER. The server's `SSL` requires one, and the verify callback ran
       on the server's, so only a fault reaches this case. */
    int rv = push_event(c->ep, EV_HANDSHAKE_DONE, c->handle, -1, 0, der, n > 0 ? (size_t)n : 0);
    OPENSSL_free(der);
    return rv == 0 ? 0 : NGTCP2_ERR_CALLBACK_FAILURE;
}

static int stream_open_cb(ngtcp2_conn *conn, int64_t id, void *ud) {
    (void)conn;
    qconn *c = ud;
    if (!ngtcp2_is_bidi_stream(id)) return 0;
    if (add_stream(c, id) == NULL) return NGTCP2_ERR_CALLBACK_FAILURE;
    if (push_event(c->ep, EV_STREAM_OPENED, c->handle, id, 0, NULL, 0) != 0)
        return NGTCP2_ERR_CALLBACK_FAILURE;
    return 0;
}

static int recv_stream_data_cb(ngtcp2_conn *conn, uint32_t flags, int64_t id, uint64_t off,
                               const uint8_t *data, size_t len, void *ud, void *sud) {
    (void)conn;
    (void)off;
    (void)sud;
    qconn *c = ud;
    uint64_t fin = (flags & NGTCP2_STREAM_DATA_FLAG_FIN) != 0 ? STREAM_DATA_FIN : 0;
    if ((len > 0 || fin) && push_event(c->ep, EV_STREAM_DATA, c->handle, id, fin, data, len) != 0)
        return NGTCP2_ERR_CALLBACK_FAILURE;
    /* The credit returns when the application has read the bytes
       (`leanp2p_quic_stream_consume`). */
    return 0;
}

static int acked_cb(ngtcp2_conn *conn, int64_t id, uint64_t off, uint64_t len, void *ud,
                    void *sud) {
    (void)conn;
    (void)sud;
    qconn *c = ud;
    qstream *s = find_stream(c, id);
    if (s == NULL) return 0;
    uint64_t upto = off + len;
    if (upto > s->acked_off) s->acked_off = upto;
    /* Free every chunk that lies wholly below the acknowledged offset,
       but never the chunk the next send starts in. */
    while (s->head && s->head != s->cursor && s->head->off + s->head->len <= s->acked_off) {
        chunk *k = s->head;
        s->head = k->next;
        if (s->tail == k) s->tail = NULL;
        free(k);
    }
    if (push_event(c->ep, EV_STREAM_ACKED, c->handle, id, buffered(s), NULL, 0) != 0)
        return NGTCP2_ERR_CALLBACK_FAILURE;
    return 0;
}

static int stream_close_cb(ngtcp2_conn *conn, uint32_t flags, int64_t id, uint64_t code, void *ud,
                           void *sud) {
    (void)flags;
    (void)code;
    (void)sud;
    (void)conn;
    qconn *c = ud;
    remove_stream(c, id);
    /* The credit of a stream of the peer's returns once the stream is
       over and the application has accepted it
       (`leanp2p_quic_grant_stream`). So the peer never has more streams
       open or waiting than the accept queue holds. */
    if (push_event(c->ep, EV_STREAM_CLOSED, c->handle, id, 0, NULL, 0) != 0)
        return NGTCP2_ERR_CALLBACK_FAILURE;
    return 0;
}

/* The peer's RESET_STREAM: its sending part is over, so our reads end. */
static int stream_reset_cb(ngtcp2_conn *conn, int64_t id, uint64_t final_size, uint64_t code,
                           void *ud, void *sud) {
    (void)conn;
    (void)final_size;
    (void)sud;
    qconn *c = ud;
    if (push_event(c->ep, EV_STREAM_RESET, c->handle, id, code, NULL, 0) != 0)
        return NGTCP2_ERR_CALLBACK_FAILURE;
    return 0;
}

/* The peer's STOP_SENDING: it will read no more, so our writes end.
   ngtcp2 sends the RESET_STREAM that RFC 9000 §3.5 asks for in answer
   (`conn_recv_stop_sending`), so the shim stops sending only. */
static int recv_stop_sending_cb(ngtcp2_conn *conn, int64_t id, uint64_t code, void *ud,
                                void *sud) {
    (void)conn;
    (void)sud;
    qconn *c = ud;
    qstream *s = find_stream(c, id);
    if (s != NULL) s->write_shut = 1;
    if (push_event(c->ep, EV_STREAM_STOPPED, c->handle, id, code, NULL, 0) != 0)
        return NGTCP2_ERR_CALLBACK_FAILURE;
    return 0;
}

static int extend_local_bidi_cb(ngtcp2_conn *conn, uint64_t max, void *ud) {
    (void)conn;
    (void)max;
    qconn *c = ud;
    if (push_event(c->ep, EV_OPEN_CREDIT, c->handle, -1, 0, NULL, 0) != 0)
        return NGTCP2_ERR_CALLBACK_FAILURE;
    return 0;
}

/* A valid stateless reset from the peer (RFC 9000 §10.3). ngtcp2 then
   moves the connection to draining and answers `NGTCP2_ERR_DRAINING`,
   as for the peer's CONNECTION_CLOSE, so the shim marks it here. */
static int recv_stateless_reset_cb(ngtcp2_conn *conn, const ngtcp2_pkt_stateless_reset2 *sr,
                                   void *ud) {
    (void)conn;
    (void)sr;
    qconn *c = ud;
    c->reset_seen = 1;
    return 0;
}

static ngtcp2_callbacks callbacks(int server) {
    ngtcp2_callbacks cb;
    memset(&cb, 0, sizeof cb);
    if (server) {
        cb.recv_client_initial = ngtcp2_crypto_recv_client_initial_cb;
    } else {
        cb.client_initial = ngtcp2_crypto_client_initial_cb;
        cb.recv_retry = ngtcp2_crypto_recv_retry_cb;
    }
    cb.recv_crypto_data = ngtcp2_crypto_recv_crypto_data_cb;
    cb.encrypt = ngtcp2_crypto_encrypt_cb;
    cb.decrypt = ngtcp2_crypto_decrypt_cb;
    cb.hp_mask = ngtcp2_crypto_hp_mask_cb;
    cb.update_key = ngtcp2_crypto_update_key_cb;
    cb.delete_crypto_aead_ctx = ngtcp2_crypto_delete_crypto_aead_ctx_cb;
    cb.delete_crypto_cipher_ctx = ngtcp2_crypto_delete_crypto_cipher_ctx_cb;
    cb.get_path_challenge_data2 = ngtcp2_crypto_get_path_challenge_data2_cb;
    cb.version_negotiation = ngtcp2_crypto_version_negotiation_cb;
    cb.rand = rand_cb;
    cb.get_new_connection_id2 = new_cid_cb;
    cb.remove_connection_id = remove_cid_cb;
    cb.handshake_completed = handshake_completed_cb;
    cb.stream_open = stream_open_cb;
    cb.recv_stream_data = recv_stream_data_cb;
    cb.acked_stream_data_offset = acked_cb;
    cb.stream_close = stream_close_cb;
    cb.stream_reset = stream_reset_cb;
    cb.recv_stop_sending = recv_stop_sending_cb;
    cb.extend_max_local_streams_bidi = extend_local_bidi_cb;
    cb.recv_stateless_reset2 = recv_stateless_reset_cb;
    return cb;
}

/* ------------------------------------------------------------------ */
/* The endpoint object                                                 */
/* ------------------------------------------------------------------ */

/* Free a connection. The order follows ngtcp2's OpenSSL glue: the `SSL`
   reaches the connection through its app data, so the app data goes
   first (`ngtcp2_crypto_ossl.h`, "Application must call
   SSL_set_app_data(ssl, NULL) before calling SSL_free(ssl)"). `SSL_free`
   also drops the certificate check (`tls_shim.h`). */
static void conn_free(qconn *c) {
    leave_handshake(c);
    cid_remove_all(&c->ep->ids, &c->keys);
    free(c->end);
    while (c->streams) remove_stream(c, c->streams->id);
    if (c->ssl != NULL) {
        SSL_set_app_data(c->ssl, NULL);
        SSL_free(c->ssl);
    }
    ngtcp2_crypto_ossl_ctx_del(c->octx);
    ngtcp2_conn_del(c->conn);
    free(c);
}

static void endpoint_finalize(void *p) {
    endpoint *ep = p;
    while (ep->conns) {
        qconn *c = ep->conns;
        ep->conns = c->next;
        conn_free(c);
    }
    while (ep->ev_head) {
        event *e = ep->ev_head;
        ep->ev_head = e->next;
        free_event(e);
    }
    while (ep->pk_head) {
        packet *k = ep->pk_head;
        ep->pk_head = k->next;
        free(k);
    }
    while (ep->closed) {
        closed_conn *k = ep->closed;
        ep->closed = k->next;
        cid_remove_all(&ep->ids, &k->keys);
        free(k);
    }
    free(ep->ids.buckets);
    lean_dec(ep->tls);
    free(ep);
}

static void noop_foreach(void *p, b_lean_obj_arg f) { (void)p; (void)f; }

static lean_external_class *endpoint_class;
static int crypto_ready;

static void init_once(void) {
    endpoint_class = lean_register_external_class(endpoint_finalize, noop_foreach);
    crypto_ready = ngtcp2_crypto_ossl_init() == 0;
}

static pthread_once_t init_flag = PTHREAD_ONCE_INIT;

static endpoint *endpoint_of(b_lean_obj_arg o) { return lean_get_external_data(o); }

/* A new endpoint for the socket bound at `local` (address bytes), with
   the TLS context `tls` and the numbers of `Quic/Constants.lean`.
   `accept` = 1 lets it take new connections, as a listener does. `none`
   when the address does not parse, the crypto glue did not start, or
   the endpoint's random secret and table could not be made. */
LEAN_EXPORT lean_obj_res leanp2p_quic_endpoint_new(
    b_lean_obj_arg tls, b_lean_obj_arg local, uint8_t accept, uint64_t max_streams_bidi,
    uint64_t stream_window, uint64_t stream_window_max, uint64_t conn_window,
    uint64_t conn_window_max, uint64_t idle_timeout_ms, uint64_t keep_alive_ms,
    uint64_t handshake_timeout_ms, uint64_t max_handshakes, uint64_t retry_threshold,
    uint64_t max_closed, uint64_t connection_refused, uint64_t invalid_token) {
    pthread_once(&init_flag, init_once);
    endpoint *ep = calloc(1, sizeof *ep);
    if (ep == NULL || !crypto_ready || !addr_from_bytes(local, &ep->local, &ep->local_len)
        || RAND_bytes(ep->retry_secret, sizeof ep->retry_secret) != 1) {
        free(ep);
        return lean_io_result_mk_ok(none());
    }
    if (!cid_table_init(&ep->ids)) {
        free(ep->ids.buckets);
        free(ep);
        return lean_io_result_mk_ok(none());
    }
    lean_inc(tls);
    ep->tls = tls;
    ep->p = (params){max_streams_bidi,   stream_window,     stream_window_max,  conn_window,
                     conn_window_max,    idle_timeout_ms,   keep_alive_ms,      handshake_timeout_ms,
                     max_handshakes,     retry_threshold,   max_closed,         connection_refused,
                     invalid_token};
    ep->accept = accept;
    ep->listening = accept;
    ep->next_handle = 1;
    return lean_io_result_mk_ok(some(lean_alloc_external(endpoint_class, ep)));
}

static qconn *find_conn(endpoint *ep, uint64_t handle) {
    for (qconn *c = ep->conns; c; c = c->next)
        if (c->handle == handle && !c->closed) return c;
    return NULL;
}

/* ------------------------------------------------------------------ */
/* Making a connection                                                 */
/* ------------------------------------------------------------------ */

/* The transport parameters this endpoint sends. libp2p opens no
   unidirectional stream, so the peer may open none. */
static void fill_params(const endpoint *ep, ngtcp2_transport_params *tp) {
    ngtcp2_transport_params_default(tp);
    tp->initial_max_streams_bidi = ep->p.max_streams_bidi;
    tp->initial_max_streams_uni = 0;
    tp->initial_max_stream_data_bidi_local = ep->p.stream_window;
    tp->initial_max_stream_data_bidi_remote = ep->p.stream_window;
    tp->initial_max_data = ep->p.conn_window;
    tp->max_idle_timeout = ns_of_ms(ep->p.idle_timeout_ms);
}

/* The settings: the clock's time, the handshake deadline, and the
   ceilings of window auto-tuning (`ngtcp2_settings.max_window`,
   `max_stream_window`). */
static void fill_settings(endpoint *ep, ngtcp2_settings *st) {
    ngtcp2_settings_default(st);
    st->initial_ts = now_ts(ep);
    st->handshake_timeout = ns_of_ms(ep->p.handshake_timeout_ms);
    st->max_window = ep->p.conn_window_max;
    st->max_stream_window = ep->p.stream_window_max;
}

/* A connection shell and its TLS session, with the caller's check on
   the `SSL`. NULL on a failure. */
static qconn *conn_shell(endpoint *ep, const struct sockaddr_storage *remote, socklen_t rlen,
                         int server, b_lean_obj_arg check) {
    qconn *c = calloc(1, sizeof *c);
    if (c == NULL) return NULL;
    c->end = calloc(1, sizeof *c->end);
    if (c->end == NULL) {
        free(c);
        return NULL;
    }
    c->ep = ep;
    c->is_server = server;
    c->started_ms = ep->now_ms;
    c->remote = *remote;
    c->remote_len = rlen;
    c->path.local.addr = (ngtcp2_sockaddr *)&ep->local;
    c->path.local.addrlen = ep->local_len;
    c->path.remote.addr = (ngtcp2_sockaddr *)&c->remote;
    c->path.remote.addrlen = c->remote_len;
    c->ref.get_conn = get_conn;
    c->ref.user_data = c;
    c->ssl = SSL_new(leanp2p_tls_context_get(ep->tls));
    int ok = c->ssl != NULL && leanp2p_tls_attach_check(c->ssl, check) == 1;
    if (ok) {
        SSL_set_app_data(c->ssl, &c->ref);
        if (server) {
            SSL_set_verify(c->ssl, SSL_VERIFY_PEER | SSL_VERIFY_FAIL_IF_NO_PEER_CERT, NULL);
            SSL_set_accept_state(c->ssl);
            ok = ngtcp2_crypto_ossl_configure_server_session(c->ssl) == 0;
        } else {
            unsigned int alen = 0;
            const unsigned char *alpn = leanp2p_tls_context_alpn(ep->tls, &alen);
            SSL_set_verify(c->ssl, SSL_VERIFY_PEER, NULL);
            SSL_set_connect_state(c->ssl);
            ok = ngtcp2_crypto_ossl_configure_client_session(c->ssl) == 0
                && SSL_set_alpn_protos(c->ssl, alpn, alen) == 0;
        }
    }
    if (ok) ok = ngtcp2_crypto_ossl_ctx_new(&c->octx, c->ssl) == 0;
    if (!ok) {
        conn_free(c);
        ERR_clear_error();
        return NULL;
    }
    c->handle = ep->next_handle++;
    return c;
}

/* A random ID that no owner of the table holds. 0 when the draw failed. */
static int random_cid(const endpoint *ep, ngtcp2_cid *cid) {
    uint8_t b[SCID_LEN];
    do {
        if (RAND_bytes(b, sizeof b) != 1) return 0;
        ngtcp2_cid_init(cid, b, sizeof b);
    } while (cid_find(&ep->ids, cid->data, cid->datalen) != NULL);
    return 1;
}

/* Put a new connection into the endpoint's list, and its IDs into the
   table: our first SCID, and for a server the DCID its client's first
   packets carry. 0 when memory ran out; the caller then frees it. */
static int conn_link(endpoint *ep, qconn *c) {
    ngtcp2_cid scid[1];
    if (ngtcp2_conn_get_scid2(c->conn, NULL) != 1 || ngtcp2_conn_get_scid2(c->conn, scid) != 1
        || cid_add(&ep->ids, &scid[0], c, NULL, &c->keys) != 0
        || (c->is_server && cid_add(&ep->ids, &c->odcid, c, NULL, &c->keys) < 0))
        return 0;
    ngtcp2_conn_set_tls_native_handle(c->conn, c->octx);
    ngtcp2_conn_set_keep_alive_timeout(c->conn, ns_of_ms(ep->p.keep_alive_ms));
    c->next = ep->conns;
    ep->conns = c;
    return 1;
}

/* Dial `remote` (address bytes) at `now`, with the certificate check
   `check`. The answer is the handle of the new connection, or 0. */
LEAN_EXPORT lean_obj_res leanp2p_quic_connect(b_lean_obj_arg o, b_lean_obj_arg remote,
                                              uint64_t now, b_lean_obj_arg check) {
    endpoint *ep = endpoint_of(o);
    ep->now_ms = now;
    struct sockaddr_storage ra;
    socklen_t rlen;
    if (!addr_from_bytes(remote, &ra, &rlen) || ra.ss_family != ep->local.ss_family)
        return lean_io_result_mk_ok(lean_box_uint64(0));
    qconn *c = conn_shell(ep, &ra, rlen, 0, check);
    if (c == NULL) return lean_io_result_mk_ok(lean_box_uint64(0));
    ngtcp2_cid dcid, scid;
    ngtcp2_settings st;
    fill_settings(ep, &st);
    ngtcp2_transport_params tp;
    fill_params(ep, &tp);
    ngtcp2_callbacks cb = callbacks(0);
    if (!random_cid(ep, &dcid) || !random_cid(ep, &scid)
        || ngtcp2_conn_client_new(&c->conn, &dcid, &scid, &c->path, NGTCP2_PROTO_VER_V1, &cb, &st,
                                  &tp, NULL, c) != 0
        || !conn_link(ep, c)) {
        conn_free(c);
        return lean_io_result_mk_ok(lean_box_uint64(0));
    }
    return lean_io_result_mk_ok(lean_box_uint64(c->handle));
}

/* ------------------------------------------------------------------ */
/* Closing                                                             */
/* ------------------------------------------------------------------ */

/* Mark a connection closed: it leaves the handshake count, and its IDs
   leave the table, so no datagram routes to it again. The next sweep
   frees it. */
static void mark_closed(qconn *c) {
    c->closed = 1;
    leave_handshake(c);
    cid_remove_all(&c->ep->ids, &c->keys);
}

/* Free one closing period: its IDs leave the table. The caller has
   taken it off the endpoint's list. */
static void free_closed(endpoint *ep, closed_conn *k) {
    cid_remove_all(&ep->ids, &k->keys);
    ep->nclosed--;
    free(k);
}

/* Take the oldest closing period off the list, and free it. */
static void drop_oldest_closed(endpoint *ep) {
    closed_conn *k = ep->closed;
    if (k == NULL) return;
    ep->closed = k->next;
    if (ep->closed == NULL) ep->closed_tail = NULL;
    free_closed(ep, k);
}

/* Keep the closing period of a server connection of a listening
   endpoint that sent the close `pkt` (`closed_conn`). It lasts three
   PTOs, as quic-go's does (`connection.go`, `ReplaceWithClosed`). The
   record takes over the connection's IDs in the table; `mark_closed` has
   already removed them from the connection. Past `max_closed` records,
   the oldest goes. When memory runs out, the record is not kept, and the
   peer ends the connection by its idle timer. */
static void remember_closed(qconn *c, const uint8_t *pkt, size_t len) {
    endpoint *ep = c->ep;
    if (!ep->listening || !c->is_server || len > MAX_DATAGRAM || ep->p.max_closed == 0) return;
    size_t n = ngtcp2_conn_get_scid2(c->conn, NULL);
    ngtcp2_cid *ids = malloc((n + 1) * sizeof *ids);
    closed_conn *k = calloc(1, sizeof *k);
    if (ids == NULL || k == NULL) {
        free(ids);
        free(k);
        return;
    }
    n = ngtcp2_conn_get_scid2(c->conn, ids);
    ids[n++] = c->odcid;
    int ok = 1;
    for (size_t i = 0; i < n && ok; i++) ok = cid_add(&ep->ids, &ids[i], NULL, k, &k->keys) >= 0;
    free(ids);
    if (!ok) {
        cid_remove_all(&ep->ids, &k->keys);
        free(k);
        return;
    }
    memcpy(k->pkt, pkt, len);
    k->pktlen = len;
    ngtcp2_duration pto = ngtcp2_conn_get_pto2(c->conn);
    k->until_ms = ep->now_ms + 3 * (pto / 1000000ull + (pto % 1000000ull != 0));
    while (ep->nclosed >= ep->p.max_closed) drop_oldest_closed(ep);
    if (ep->closed_tail) ep->closed_tail->next = k; else ep->closed = k;
    ep->closed_tail = k;
    ep->nclosed++;
}

/* Send a CONNECTION_CLOSE with `ccerr`, unless the connection is
   already closing or draining, mark the connection closed, and report
   the end as `kind`. A listening endpoint keeps the close for the
   closing period (`remember_closed`). */
static void close_with(qconn *c, const ngtcp2_ccerr *ccerr, uint8_t kind, const char *why) {
    if (c->closed) return;
    uint8_t buf[MAX_DATAGRAM];
    ngtcp2_ssize n = 0;
    if (!ngtcp2_conn_in_closing_period2(c->conn) && !ngtcp2_conn_in_draining_period2(c->conn)) {
        ngtcp2_path_storage ps;
        ngtcp2_path_storage_zero(&ps);
        ngtcp2_pkt_info pi;
        n = ngtcp2_conn_write_connection_close(c->conn, &ps.path, &pi, buf, sizeof buf, ccerr,
                                               now_ts(c->ep));
        if (n > 0) push_packet(c->ep, &ps.path.remote, buf, (size_t)n);
    }
    mark_closed(c);
    if (n > 0) remember_closed(c, buf, (size_t)n);
    push_end(c, kind, ccerr->error_code, why);
}

/* Close after a library error. A TLS failure sends the alert that libssl
   raised, as the transport error 0x100 plus the alert (RFC 9001 §4.8):
   ngtcp2's OpenSSL glue records it, and `ngtcp2_conn_get_tls_alert2`
   returns it on `NGTCP2_ERR_CRYPTO` (`ngtcp2_conn_read_pkt`).
   `ngtcp2_ccerr_set_liberr` alone maps that error to PROTOCOL_VIOLATION
   and drops the alert. A refusal of the peer's certificate reports its
   reason: the check's own, the chain rule's, or libssl's. The test reads
   the thread's error queue, so it runs before the queue is cleared. */
static void close_liberr(qconn *c, int rv) {
    ngtcp2_ccerr ccerr;
    ngtcp2_ccerr_default(&ccerr);
    uint8_t alert = rv == NGTCP2_ERR_CRYPTO ? ngtcp2_conn_get_tls_alert2(c->conn) : 0;
    int refused = rv == NGTCP2_ERR_CRYPTO && leanp2p_tls_refused(c->ssl);
    if (alert != 0) ngtcp2_ccerr_set_tls_alert(&ccerr, alert, NULL, 0);
    else ngtcp2_ccerr_set_liberr(&ccerr, rv, NULL, 0);
    char why[REASON_MAX + 1];
    unsigned long e = ERR_peek_error();
    const char *refusal = leanp2p_tls_refusal(c->ssl);
    if (refused && refusal[0] != '\0') {
        snprintf(why, sizeof why, "%s", refusal);
    } else if (e != 0) {
        char tls[160];
        ERR_error_string_n(e, tls, sizeof tls);
        snprintf(why, sizeof why, "%s (%s)", ngtcp2_strerror(rv), tls);
    } else {
        snprintf(why, sizeof why, "%s", ngtcp2_strerror(rv));
    }
    ERR_clear_error();
    close_with(c, &ccerr, refused ? EV_CONN_REFUSED : EV_CONN_FAILED, why);
}

/* The connection has ended with no close of ours to send: the peer
   closed it, a stateless reset ended it, a timer ran out, or ngtcp2
   asked the server to drop it. A peer's close carries its own error:
   an application close is `EV_CONN_CLOSED`, a transport close with
   NO_ERROR an orderly `EV_CONN_CLOSED` too, and any other transport
   close `EV_PEER_FAILED`. */
static void close_silent(qconn *c, int rv) {
    if (c->closed) return;
    mark_closed(c);
    if (rv == NGTCP2_ERR_DRAINING && c->reset_seen) {
        push_end(c, EV_CONN_DROPPED, 0, "the peer reset the connection (stateless reset)");
        return;
    }
    if (rv == NGTCP2_ERR_DRAINING) {
        const ngtcp2_ccerr *e = ngtcp2_conn_get_ccerr2(c->conn);
        int app = e->type == NGTCP2_CCERR_TYPE_APPLICATION;
        char why[REASON_MAX + 1];
        snprintf(why, sizeof why, "the peer closed the connection (%s 0x%llx): %.*s",
                 app ? "application" : "transport", (unsigned long long)e->error_code,
                 (int)(e->reasonlen < 120 ? e->reasonlen : 120),
                 e->reason != NULL ? (const char *)e->reason : "");
        uint8_t kind = app || e->error_code == NGTCP2_NO_ERROR ? EV_CONN_CLOSED : EV_PEER_FAILED;
        push_end(c, kind, e->error_code, why);
        return;
    }
    if (rv == NGTCP2_ERR_IDLE_CLOSE)
        push_end(c, EV_CONN_IDLE, 0, "the connection was idle too long");
    else if (rv == NGTCP2_ERR_HANDSHAKE_TIMEOUT)
        push_end(c, EV_CONN_TIMEOUT, 0, "the handshake timed out");
    else
        push_end(c, EV_CONN_DROPPED, 0, ngtcp2_strerror(rv));
}

/* Close a connection with the error `code` and a reason (RFC 9000
   §10.2): an application error, as the application asks, or a transport
   error when `transport` = 1, as the endpoint itself refuses a
   connection (CONNECTION_REFUSED, RFC 9000 §20.1). */
LEAN_EXPORT lean_obj_res leanp2p_quic_close(b_lean_obj_arg o, uint64_t handle, uint8_t transport,
                                            uint64_t code, b_lean_obj_arg reason, uint64_t now) {
    endpoint *ep = endpoint_of(o);
    ep->now_ms = now;
    qconn *c = find_conn(ep, handle);
    if (c != NULL) {
        ngtcp2_ccerr ccerr;
        ngtcp2_ccerr_default(&ccerr);
        const uint8_t *r = (const uint8_t *)lean_string_cstr(reason);
        size_t rl = lean_string_size(reason) - 1;
        if (transport) ngtcp2_ccerr_set_transport_error(&ccerr, code, r, rl);
        else ngtcp2_ccerr_set_application_error(&ccerr, code, r, rl);
        close_with(c, &ccerr, transport ? EV_CONN_FAILED : EV_CONN_CLOSED,
                   lean_string_cstr(reason));
    }
    return lean_io_result_mk_ok(lean_box(0));
}

/* Refuse every server connection that has not finished its handshake,
   with the transport error `code` and a reason. The listener has
   closed, and these connections are still unauthenticated. So they end
   now, as root ARCHITECTURE §5.5 closes the pending connections of a
   host. The endpoint takes no new connection after the call. */
LEAN_EXPORT lean_obj_res leanp2p_quic_refuse_pending(b_lean_obj_arg o, uint64_t code,
                                                     b_lean_obj_arg reason, uint64_t now) {
    endpoint *ep = endpoint_of(o);
    ep->now_ms = now;
    ep->accept = 0;
    const uint8_t *r = (const uint8_t *)lean_string_cstr(reason);
    size_t rl = lean_string_size(reason) - 1;
    for (qconn *c = ep->conns; c; c = c->next) {
        if (c->closed || !c->is_server || ngtcp2_conn_get_handshake_completed2(c->conn)) continue;
        ngtcp2_ccerr ccerr;
        ngtcp2_ccerr_default(&ccerr);
        ngtcp2_ccerr_set_transport_error(&ccerr, code, r, rl);
        close_with(c, &ccerr, EV_CONN_FAILED, lean_string_cstr(reason));
    }
    return lean_io_result_mk_ok(lean_box(0));
}

/* Free the connections marked closed, and the closed records whose
   closing period has passed. The sweep runs at every flush, so a record
   lives at most until the loop's first turn after its period. */
static void sweep(endpoint *ep) {
    for (qconn **p = &ep->conns; *p;) {
        if ((*p)->closed) {
            qconn *c = *p;
            *p = c->next;
            conn_free(c);
        } else {
            p = &(*p)->next;
        }
    }
    closed_conn *last = NULL;
    for (closed_conn **p = &ep->closed; *p;) {
        if ((*p)->until_ms <= ep->now_ms) {
            closed_conn *k = *p;
            *p = k->next;
            free_closed(ep, k);
        } else {
            last = *p;
            p = &(*p)->next;
        }
    }
    ep->closed_tail = last;
}

/* ------------------------------------------------------------------ */
/* Receiving                                                           */
/* ------------------------------------------------------------------ */

/* A datagram for a connection in its closing period: send the close
   again to the datagram's source, on the 1st, 2nd, 4th, 8th, ... packet
   (quic-go's `closedLocalConn.handlePacket`). */
static void answer_closed(endpoint *ep, closed_conn *k, const struct sockaddr_storage *from,
                          socklen_t flen) {
    k->seen++;
    if ((k->seen & (k->seen - 1)) == 0) {
        ngtcp2_addr to = {(ngtcp2_sockaddr *)from, flen};
        push_packet(ep, &to, k->pkt, k->pktlen);
    }
}

/* Answer a client's Initial with a CONNECTION_CLOSE of the transport
   error `code`, and keep no state for it (RFC 9000 §10.2;
   `ngtcp2_crypto_write_connection_close`). The packet's DCID is the
   client's SCID, and the client's DCID derives the Initial keys. quic-go
   refuses a new connection the same way (`server.go`,
   `refuseNewConn`). */
static void stateless_close(endpoint *ep, const ngtcp2_pkt_hd *hd,
                            const struct sockaddr_storage *from, socklen_t flen, uint64_t code) {
    uint8_t buf[MAX_DATAGRAM];
    ngtcp2_ssize n = ngtcp2_crypto_write_connection_close(buf, sizeof buf, hd->version, &hd->scid,
                                                          &hd->dcid, code, NULL, 0);
    ngtcp2_addr to = {(ngtcp2_sockaddr *)from, flen};
    if (n > 0) push_packet(ep, &to, buf, (size_t)n);
}

/* Answer a client's Initial with a Retry (RFC 9000 §8.1.2, §17.2.5): a
   new SCID, and a token that binds the client's address and its first
   DCID under the endpoint's secret. A client that holds its address
   sends the token back in its next Initial; a spoofed source never sees
   it. The Retry is smaller than the 1200 bytes of the Initial, so it
   amplifies nothing. When a draw or a write fails, the Initial is
   dropped, and the client sends it again. */
static void send_retry(endpoint *ep, const ngtcp2_pkt_hd *hd, const struct sockaddr_storage *from,
                       socklen_t flen) {
    ngtcp2_cid rscid;
    if (!random_cid(ep, &rscid)) return;
    uint8_t token[NGTCP2_CRYPTO_MAX_RETRY_TOKENLEN2];
    ngtcp2_ssize tlen = ngtcp2_crypto_generate_retry_token2(
        token, ep->retry_secret, sizeof ep->retry_secret, hd->version,
        (const ngtcp2_sockaddr *)from, flen, &rscid, &hd->dcid, now_ts(ep));
    if (tlen < 0) return;
    uint8_t buf[MAX_DATAGRAM];
    ngtcp2_ssize n = ngtcp2_crypto_write_retry(buf, sizeof buf, hd->version, &hd->scid, &rscid,
                                               &hd->dcid, token, (size_t)tlen);
    ngtcp2_addr to = {(ngtcp2_sockaddr *)from, flen};
    if (n > 0) push_packet(ep, &to, buf, (size_t)n);
}

/* What a client's Initial carries: no token of ours, a Retry token that
   proves its address, or a Retry token that fails the check. A token of
   another kind is no token of ours: the endpoint sends no NEW_TOKEN. */
enum { TOKEN_NONE, TOKEN_VALID, TOKEN_INVALID };

/* Check the Retry token of an Initial. On `TOKEN_VALID`, `odcid` holds
   the DCID of the client's first Initial, which the token carries. The
   token lives as long as the handshake deadline, as quic-go's does
   (`config.go`, `maxRetryTokenAge`). */
static int check_token(endpoint *ep, const ngtcp2_pkt_hd *hd, const struct sockaddr_storage *from,
                       socklen_t flen, ngtcp2_cid *odcid) {
    if (hd->tokenlen == 0 || hd->token[0] != NGTCP2_CRYPTO_TOKEN_MAGIC_RETRY2) return TOKEN_NONE;
    int rv = ngtcp2_crypto_verify_retry_token2(
        odcid, hd->token, hd->tokenlen, ep->retry_secret, sizeof ep->retry_secret, hd->version,
        (const ngtcp2_sockaddr *)from, flen, &hd->dcid, ns_of_ms(ep->p.handshake_timeout_ms),
        now_ts(ep));
    return rv == 0 ? TOKEN_VALID : TOKEN_INVALID;
}

/* The answer to a client's first Initial, before any state exists for
   it. Each new connection costs an ngtcp2 connection and a TLS session
   until its handshake ends, so the endpoint bounds them:

   - an invalid Retry token gets INVALID_TOKEN: "the server SHOULD
     immediately close ... with an INVALID_TOKEN error" (RFC 9000
     §8.1.2);
   - at `max_handshakes` connections in their handshake, a client gets
     CONNECTION_REFUSED;
   - from `retry_threshold` on, a client that has not proved its address
     gets a Retry first. A spoofed source cannot answer it, so spoofed
     Initials never fill the rest of the count. go-libp2p asks for the
     same proof of up to half its unverified connections
     (`vendor/go-libp2p/p2p/host/resource-manager/conn_limiter.go`,
     `newVerifySourceAddressRateLimiter`).

   The answer is 1 when the Initial may open a connection. */
static int admit_initial(endpoint *ep, const ngtcp2_pkt_hd *hd,
                         const struct sockaddr_storage *from, socklen_t flen) {
    ngtcp2_cid odcid;
    int token = check_token(ep, hd, from, flen, &odcid);
    if (token == TOKEN_INVALID) {
        stateless_close(ep, hd, from, flen, ep->p.invalid_token);
        return 0;
    }
    if (ep->handshaking >= ep->p.max_handshakes) {
        stateless_close(ep, hd, from, flen, ep->p.connection_refused);
        return 0;
    }
    if (token == TOKEN_NONE && ep->handshaking >= ep->p.retry_threshold) {
        send_retry(ep, hd, from, flen);
        return 0;
    }
    return 1;
}

/* Answer a client whose version we do not speak (RFC 9000 §6.1). The
   decoder asks for this only for a long header of at least 1200 bytes
   (`ngtcp2_pkt_decode_version_cid`, RFC 9000 §5.2.2). The packet's DCID
   is the client's SCID, and its SCID the client's DCID (§17.2.1). */
static void version_negotiation(endpoint *ep, const ngtcp2_version_cid *vc,
                                const struct sockaddr_storage *from, socklen_t flen) {
    uint8_t buf[MAX_DATAGRAM];
    uint32_t versions[] = {NGTCP2_PROTO_VER_V1};
    uint8_t r;
    RAND_bytes(&r, 1);
    ngtcp2_ssize n = ngtcp2_pkt_write_version_negotiation(buf, sizeof buf, r, vc->scid,
                                                          vc->scidlen, vc->dcid, vc->dcidlen,
                                                          versions, 1);
    ngtcp2_addr to = {(ngtcp2_sockaddr *)from, flen};
    if (n > 0) push_packet(ep, &to, buf, (size_t)n);
}

/* Hand one datagram, which arrived on `path`, to its connection, and end
   the connection when the read ends it. A completed handshake with no
   ALPN closes here, after the read (`handshake_completed_cb`). */
static void read_into(qconn *c, const ngtcp2_path *path, const uint8_t *data, size_t len) {
    ngtcp2_pkt_info pi;
    memset(&pi, 0, sizeof pi);
    ERR_clear_error();
    int rv = ngtcp2_conn_read_pkt(c->conn, path, &pi, data, len, now_ts(c->ep));
    if (rv == NGTCP2_ERR_DRAINING || rv == NGTCP2_ERR_DROP_CONN) close_silent(c, rv);
    else if (rv == NGTCP2_ERR_CLOSING) return;
    else if (rv != 0) close_liberr(c, rv);
    else if (c->no_alpn) {
        ngtcp2_ccerr ccerr;
        ngtcp2_ccerr_default(&ccerr);
        ngtcp2_ccerr_set_tls_alert(&ccerr, ALERT_NO_APPLICATION_PROTOCOL, NULL, 0);
        close_with(c, &ccerr, EV_CONN_FAILED, "no application protocol negotiated");
    }
}

/* Take one datagram from `from` (address bytes) at `now`. The answer
   is 1 when the datagram would open a new connection that
   `admit_initial` lets in: the caller then admits it or not, and calls
   `leanp2p_quic_accept` with its certificate check or
   `leanp2p_quic_refuse`. 0 otherwise: the datagram went to its
   connection or its closing period, the endpoint answered it, or it was
   dropped. */
LEAN_EXPORT lean_obj_res leanp2p_quic_recv(b_lean_obj_arg o, b_lean_obj_arg bytes,
                                           b_lean_obj_arg from, uint64_t now) {
    endpoint *ep = endpoint_of(o);
    ep->now_ms = now;
    const uint8_t *data = lean_sarray_cptr(bytes);
    size_t len = lean_sarray_size(bytes);
    struct sockaddr_storage fa;
    socklen_t flen;
    if (len == 0 || !addr_from_bytes(from, &fa, &flen)) return lean_io_result_mk_ok(lean_box(0));
    ngtcp2_version_cid vc;
    int rv = ngtcp2_pkt_decode_version_cid(&vc, data, len, SCID_LEN);
    if (rv == NGTCP2_ERR_VERSION_NEGOTIATION) {
        if (ep->accept) version_negotiation(ep, &vc, &fa, flen);
        return lean_io_result_mk_ok(lean_box(0));
    }
    if (rv != 0) return lean_io_result_mk_ok(lean_box(0));
    /* The route is the DCID: one of a connection's own IDs, the DCID its
       client's first packets carry, or an ID of a closing period. */
    cid_entry *e = cid_find(&ep->ids, vc.dcid, vc.dcidlen);
    if (e != NULL && e->closed != NULL) {
        answer_closed(ep, e->closed, &fa, flen);
        return lean_io_result_mk_ok(lean_box(0));
    }
    if (e == NULL) {
        /* An unknown CID: a new client's first datagram, when this
           endpoint accepts and the datagram is a valid Initial
           (`ngtcp2_accept`); anything else is dropped. */
        ngtcp2_pkt_hd hd;
        int fresh = ep->accept && ngtcp2_accept(&hd, data, len) == 0
            && admit_initial(ep, &hd, &fa, flen);
        return lean_io_result_mk_ok(lean_box(fresh ? 1 : 0));
    }
    qconn *c = e->conn;
    /* The datagram's own path. The shim never moves the connection to
       it. ngtcp2 compares it with its current path, and moves only after
       a packet from the new address decrypts. It then validates the new
       path itself (RFC 9000 §9). Every packet goes where ngtcp2 says
       (`flush_conn`), so a datagram from a spoofed source cannot move
       the connection. */
    ngtcp2_path path = c->path;
    path.remote.addr = (ngtcp2_sockaddr *)&fa;
    path.remote.addrlen = flen;
    read_into(c, &path, data, len);
    return lean_io_result_mk_ok(lean_box(0));
}

/* Open the server connection of a client's first datagram from `from`
   at `now`, with the certificate check `check`, and read the datagram
   into it. The caller calls it after `leanp2p_quic_recv` answered 1
   for the datagram. An Initial with a valid Retry token opens a
   connection whose address is proved: its transport parameters name the
   Retry (RFC 9000 §7.3), and the token lifts the limit of three times
   the bytes received (`ngtcp2_settings.token`, RFC 9000 §8.1). The
   answer is the handle of the new connection, or 0 when none opened.
   The read can end the connection at once; its end event then waits in
   the queue like any other. */
LEAN_EXPORT lean_obj_res leanp2p_quic_accept(b_lean_obj_arg o, b_lean_obj_arg bytes,
                                             b_lean_obj_arg from, uint64_t now,
                                             b_lean_obj_arg check) {
    endpoint *ep = endpoint_of(o);
    ep->now_ms = now;
    const uint8_t *data = lean_sarray_cptr(bytes);
    size_t len = lean_sarray_size(bytes);
    struct sockaddr_storage fa;
    socklen_t flen;
    ngtcp2_pkt_hd hd;
    if (!ep->accept || len == 0 || !addr_from_bytes(from, &fa, &flen)
        || ngtcp2_accept(&hd, data, len) != 0)
        return lean_io_result_mk_ok(lean_box_uint64(0));
    ngtcp2_cid odcid;
    int token = check_token(ep, &hd, &fa, flen, &odcid);
    if (token == TOKEN_INVALID) return lean_io_result_mk_ok(lean_box_uint64(0));
    qconn *c = conn_shell(ep, &fa, flen, 1, check);
    if (c == NULL) return lean_io_result_mk_ok(lean_box_uint64(0));
    ngtcp2_cid scid;
    ngtcp2_settings st;
    fill_settings(ep, &st);
    ngtcp2_transport_params tp;
    fill_params(ep, &tp);
    tp.original_dcid_present = 1;
    if (token == TOKEN_VALID) {
        tp.original_dcid = odcid;
        tp.retry_scid = hd.dcid;
        tp.retry_scid_present = 1;
        st.token = hd.token;
        st.tokenlen = hd.tokenlen;
        st.token_type = NGTCP2_TOKEN_TYPE_RETRY;
    } else {
        tp.original_dcid = hd.dcid;
    }
    c->odcid = hd.dcid;
    ngtcp2_callbacks cb = callbacks(1);
    if (!random_cid(ep, &scid)
        || ngtcp2_conn_server_new(&c->conn, &hd.scid, &scid, &c->path, hd.version, &cb, &st, &tp,
                                  NULL, c) != 0
        || !conn_link(ep, c)) {
        conn_free(c);
        return lean_io_result_mk_ok(lean_box_uint64(0));
    }
    c->in_handshake = 1;
    ep->handshaking++;
    uint64_t handle = c->handle;
    read_into(c, &c->path, data, len);
    return lean_io_result_mk_ok(lean_box_uint64(handle));
}

/* Refuse the new connection of a client's first datagram from `from`,
   for which `leanp2p_quic_recv` answered 1, with CONNECTION_REFUSED and
   no state. The caller's admission said no, as go-libp2p's resource
   manager refuses a QUIC connection before its handshake starts
   (`vendor/go-libp2p/config/config.go`, `ConnContext`). */
LEAN_EXPORT lean_obj_res leanp2p_quic_refuse(b_lean_obj_arg o, b_lean_obj_arg bytes,
                                             b_lean_obj_arg from, uint64_t now) {
    endpoint *ep = endpoint_of(o);
    ep->now_ms = now;
    const uint8_t *data = lean_sarray_cptr(bytes);
    size_t len = lean_sarray_size(bytes);
    struct sockaddr_storage fa;
    socklen_t flen;
    ngtcp2_pkt_hd hd;
    if (len > 0 && addr_from_bytes(from, &fa, &flen) && ngtcp2_accept(&hd, data, len) == 0)
        stateless_close(ep, &hd, &fa, flen, ep->p.connection_refused);
    return lean_io_result_mk_ok(lean_box(0));
}

/* ------------------------------------------------------------------ */
/* Sending                                                             */
/* ------------------------------------------------------------------ */

/* The stream that has bytes or a FIN to send and has not been found
   blocked in this flush, `round`. Each stream carries its own mark, so
   any number of blocked streams leaves every other stream its turn. */
static qstream *next_ready(qconn *c, uint64_t round) {
    for (qstream *s = c->streams; s; s = s->next) {
        if (s->write_shut || s->blocked_round == round) continue;
        if (s->cursor != NULL || (s->fin_wanted && !s->fin_sent)) return s;
    }
    return NULL;
}

/* Advance a stream's cursor past `n` bytes that ngtcp2 took. */
static void advance(qstream *s, size_t n) {
    while (n > 0 && s->cursor) {
        size_t left = s->cursor->len - s->cursor_pos;
        size_t step = n < left ? n : left;
        s->cursor_pos += step;
        n -= step;
        if (s->cursor_pos == s->cursor->len) {
            s->cursor = s->cursor->next;
            s->cursor_pos = 0;
        }
    }
}

/* Record what one write took from `s`: `datalen` bytes, and the FIN
   when it was asked for and no byte is left. */
static void took(qstream *s, ngtcp2_ssize datalen, uint32_t flags) {
    if (s == NULL || datalen < 0) return;
    advance(s, (size_t)datalen);
    if ((flags & NGTCP2_WRITE_STREAM_FLAG_FIN) && s->cursor == NULL) s->fin_sent = 1;
}

/* Write every packet the connection wants to send now, up to
   `MAX_PACKETS_PER_FLUSH`. Each turn offers one ready stream's bytes;
   a stream that cannot take more in this flush is set aside for the
   rest of the flush. Each packet goes on the path ngtcp2 chose for it
   (`ngtcp2_conn_writev_stream`, `path`). */
static void flush_conn(qconn *c) {
    endpoint *ep = c->ep;
    uint8_t buf[MAX_DATAGRAM];
    uint64_t round = ++c->flush_round;
    ngtcp2_path_storage ps;
    ngtcp2_path_storage_zero(&ps);
    ngtcp2_pkt_info pi;
    size_t max = ngtcp2_conn_get_max_tx_udp_payload_size2(c->conn);
    if (max > sizeof buf) max = sizeof buf;
    for (int count = 0; count < MAX_PACKETS_PER_FLUSH && !c->closed;) {
        qstream *s = ngtcp2_conn_get_handshake_completed2(c->conn) ? next_ready(c, round) : NULL;
        ngtcp2_vec v = {NULL, 0};
        uint32_t flags = NGTCP2_WRITE_STREAM_FLAG_MORE;
        int64_t sid = -1;
        if (s != NULL) {
            sid = s->id;
            if (s->cursor) {
                v.base = s->cursor->data + s->cursor_pos;
                v.len = s->cursor->len - s->cursor_pos;
            }
            /* The FIN goes with the last bytes: the cursor's chunk is the
               last one. */
            if (s->fin_wanted && (s->cursor == NULL || s->cursor->next == NULL))
                flags |= NGTCP2_WRITE_STREAM_FLAG_FIN;
        }
        ngtcp2_ssize datalen = -1;
        ngtcp2_ssize n = ngtcp2_conn_writev_stream(c->conn, &ps.path, &pi, buf, max, &datalen,
                                                   flags, sid, s != NULL ? &v : NULL,
                                                   s != NULL ? 1 : 0, now_ts(ep));
        if (n < 0) {
            if (n == NGTCP2_ERR_STREAM_DATA_BLOCKED || n == NGTCP2_ERR_STREAM_SHUT_WR
                || n == NGTCP2_ERR_STREAM_NOT_FOUND) {
                if (s != NULL) s->blocked_round = round;
                continue;
            }
            if (n == NGTCP2_ERR_WRITE_MORE) {
                /* The packet has room for more, and `datalen` >= 0
                   (`ngtcp2.h`). A FIN-only frame reports 0, so the FIN went
                   in. A stream that was offered bytes and gave none cannot
                   fill the packet further, so it leaves this flush. */
                if (s != NULL && datalen == 0 && v.len > 0) s->blocked_round = round;
                else took(s, datalen, flags);
                continue;
            }
            close_liberr(c, (int)n);
            return;
        }
        took(s, datalen, flags);
        if (n == 0) {
            /* No packet: either nothing is left, or the stream we offered
               is held by the congestion, the flow window, or the pacer. */
            if (s == NULL) break;
            s->blocked_round = round;
            continue;
        }
        push_packet(ep, &ps.path.remote, buf, (size_t)n);
        count++;
    }
    /* The pacer learns when this burst went out: the call "must be called
       after (multiple invocation of) `ngtcp2_conn_writev_stream`"
       (`ngtcp2.h`, `ngtcp2_conn_update_pkt_tx_time`). */
    if (!c->closed) ngtcp2_conn_update_pkt_tx_time(c->conn, now_ts(ep));
}

/* Write the packets of every connection, and free the closed ones. */
LEAN_EXPORT lean_obj_res leanp2p_quic_flush(b_lean_obj_arg o, uint64_t now) {
    endpoint *ep = endpoint_of(o);
    ep->now_ms = now;
    for (qconn *c = ep->conns; c; c = c->next)
        if (!c->closed) flush_conn(c);
    sweep(ep);
    return lean_io_result_mk_ok(lean_box(0));
}

/* Run the timers due at `now`: loss detection, the idle timer, the
   keep-alive, the handshake deadline.

   The handshake deadline comes first, as in quic-go's run loop
   (`connection.go`: `ErrHandshakeTimeout` before `ErrIdleTimeout`).
   `ngtcp2_conn_handle_expiry` tests the idle timer first, and the idle
   timer starts with the connection. So a peer that never answers would
   end on both timers at the same instant, and read as an idle end. The
   deadline is the one root ARCHITECTURE §5.4 names. */
LEAN_EXPORT lean_obj_res leanp2p_quic_expire(b_lean_obj_arg o, uint64_t now) {
    endpoint *ep = endpoint_of(o);
    ep->now_ms = now;
    for (qconn *c = ep->conns; c; c = c->next) {
        if (c->closed || ngtcp2_conn_get_expiry2(c->conn) > now_ts(ep)) continue;
        if (!ngtcp2_conn_get_handshake_completed2(c->conn)
            && now - c->started_ms >= ep->p.handshake_timeout_ms) {
            close_silent(c, NGTCP2_ERR_HANDSHAKE_TIMEOUT);
            continue;
        }
        ERR_clear_error();
        int rv = ngtcp2_conn_handle_expiry(c->conn, now_ts(ep));
        if (rv == NGTCP2_ERR_IDLE_CLOSE || rv == NGTCP2_ERR_HANDSHAKE_TIMEOUT) close_silent(c, rv);
        else if (rv != 0) close_liberr(c, rv);
    }
    return lean_io_result_mk_ok(lean_box(0));
}

/* The earliest timer of every connection, in the caller's
   milliseconds, rounded up. `NO_EXPIRY` when no timer is set. */
LEAN_EXPORT lean_obj_res leanp2p_quic_expiry(b_lean_obj_arg o) {
    endpoint *ep = endpoint_of(o);
    uint64_t best = NO_EXPIRY;
    for (qconn *c = ep->conns; c; c = c->next) {
        if (c->closed) continue;
        ngtcp2_tstamp t = ngtcp2_conn_get_expiry2(c->conn);
        /* ngtcp2's own answer for a connection with no timer. */
        if (t == UINT64_MAX) continue;
        uint64_t ms = t / 1000000ull + (t % 1000000ull != 0);
        if (ms < best) best = ms;
    }
    return lean_io_result_mk_ok(lean_box_uint64(best));
}

/* ------------------------------------------------------------------ */
/* Streams: the application's commands                                 */
/* ------------------------------------------------------------------ */

/* Open a stream on a connection. The answer is the stream id,
   `OPEN_BLOCKED` when the peer allows no more streams now (an open
   credit event follows when it does), or `OPEN_GONE`. When memory for
   the stream's record runs out, the connection ends with an internal
   error, as when an event cannot be queued (`push_event`). */
LEAN_EXPORT lean_obj_res leanp2p_quic_open_stream(b_lean_obj_arg o, uint64_t handle) {
    endpoint *ep = endpoint_of(o);
    qconn *c = find_conn(ep, handle);
    uint64_t answer = OPEN_GONE;
    if (c != NULL && ngtcp2_conn_get_handshake_completed2(c->conn)) {
        int64_t id;
        int rv = ngtcp2_conn_open_bidi_stream(c->conn, &id, NULL);
        if (rv == NGTCP2_ERR_STREAM_ID_BLOCKED) answer = OPEN_BLOCKED;
        else if (rv == 0 && add_stream(c, id) != NULL) answer = (uint64_t)id;
        else if (rv == 0) close_liberr(c, NGTCP2_ERR_NOMEM);
    }
    return lean_io_result_mk_ok(lean_box_uint64(answer));
}

/* Append bytes to a stream's send buffer, and the FIN after them when
   `fin` = 1. The answer is the count of bytes the peer has not
   acknowledged, after the append. It is `WRITE_REFUSED` when the stream
   cannot take bytes: the stream is gone, reset, stopped by the peer, or
   closed for writing. The bytes go out at the next flush. When memory for the
   bytes runs out, the connection ends with an internal error, and the
   write is refused. */
LEAN_EXPORT lean_obj_res leanp2p_quic_stream_write(b_lean_obj_arg o, uint64_t handle,
                                                   uint64_t sid, b_lean_obj_arg bytes,
                                                   uint8_t fin) {
    endpoint *ep = endpoint_of(o);
    qconn *c = find_conn(ep, handle);
    qstream *s = c != NULL ? find_stream(c, (int64_t)sid) : NULL;
    if (s == NULL || s->write_shut || s->fin_wanted)
        return lean_io_result_mk_ok(lean_box_uint64(WRITE_REFUSED));
    size_t n = lean_sarray_size(bytes);
    if (n > 0) {
        chunk *k = malloc(sizeof *k + n);
        if (k == NULL) {
            close_liberr(c, NGTCP2_ERR_NOMEM);
            return lean_io_result_mk_ok(lean_box_uint64(WRITE_REFUSED));
        }
        k->next = NULL;
        k->off = s->end_off;
        k->len = n;
        memcpy(k->data, lean_sarray_cptr(bytes), n);
        if (s->tail) s->tail->next = k; else s->head = k;
        s->tail = k;
        if (s->cursor == NULL) {
            s->cursor = k;
            s->cursor_pos = 0;
        }
        s->end_off += n;
    }
    if (fin) s->fin_wanted = 1;
    return lean_io_result_mk_ok(lean_box_uint64(buffered(s)));
}

/* The application has read `n` bytes of a stream, or dropped them:
   return the credit to the peer, for the stream and for the connection.
   The stream's part does nothing once the stream is gone; the
   connection's part still counts. */
LEAN_EXPORT lean_obj_res leanp2p_quic_stream_consume(b_lean_obj_arg o, uint64_t handle,
                                                     uint64_t sid, uint64_t n) {
    endpoint *ep = endpoint_of(o);
    qconn *c = find_conn(ep, handle);
    if (c != NULL && n > 0) {
        ngtcp2_conn_extend_max_stream_offset(c->conn, (int64_t)sid, n);
        ngtcp2_conn_extend_max_offset(c->conn, n);
    }
    return lean_io_result_mk_ok(lean_box(0));
}

/* Let the peer open one more stream: one of its streams is over, and
   the application has accepted it (`ngtcp2_conn_extend_max_streams_bidi`:
   the library does not raise the limit itself). quic-go returns the
   credit at the same point (`streams_map_incoming.go`, `deleteStream`). */
LEAN_EXPORT lean_obj_res leanp2p_quic_grant_stream(b_lean_obj_arg o, uint64_t handle) {
    endpoint *ep = endpoint_of(o);
    qconn *c = find_conn(ep, handle);
    if (c != NULL) ngtcp2_conn_extend_max_streams_bidi(c->conn, 1);
    return lean_io_result_mk_ok(lean_box(0));
}

/* Reset both directions of a stream with the application error
   `code`: RESET_STREAM and STOP_SENDING (RFC 9000 §3.5), as go-libp2p's
   `Reset` does. */
LEAN_EXPORT lean_obj_res leanp2p_quic_stream_reset(b_lean_obj_arg o, uint64_t handle,
                                                   uint64_t sid, uint64_t code) {
    endpoint *ep = endpoint_of(o);
    qconn *c = find_conn(ep, handle);
    qstream *s = c != NULL ? find_stream(c, (int64_t)sid) : NULL;
    if (s != NULL) {
        s->write_shut = 1;
        ngtcp2_conn_shutdown_stream(c->conn, 0, (int64_t)sid, code);
    }
    return lean_io_result_mk_ok(lean_box(0));
}

/* ------------------------------------------------------------------ */
/* Draining the queues                                                 */
/* ------------------------------------------------------------------ */

/* The next event, as the Lean structure `QuicNative.EventRaw`: one
   object field (the data), then three `UInt64` scalars (the
   connection, the stream, the code) and one `UInt8` (the kind), in
   declaration order. */
LEAN_EXPORT lean_obj_res leanp2p_quic_next_event(b_lean_obj_arg o) {
    endpoint *ep = endpoint_of(o);
    event *e = ep->ev_head;
    if (e == NULL) return lean_io_result_mk_ok(none());
    ep->ev_head = e->next;
    if (ep->ev_head == NULL) ep->ev_tail = NULL;
    lean_object *r = lean_alloc_ctor(0, 1, 3 * 8 + 1);
    lean_ctor_set(r, 0, mk_bytes(e->data, e->len));
    lean_ctor_set_uint64(r, sizeof(void *), e->conn);
    lean_ctor_set_uint64(r, sizeof(void *) + 8, (uint64_t)e->stream);
    lean_ctor_set_uint64(r, sizeof(void *) + 16, e->code);
    lean_ctor_set_uint8(r, sizeof(void *) + 24, e->kind);
    free_event(e);
    return lean_io_result_mk_ok(some(r));
}

/* The next datagram to send, as the Lean pair (bytes, address bytes). */
LEAN_EXPORT lean_obj_res leanp2p_quic_next_packet(b_lean_obj_arg o) {
    endpoint *ep = endpoint_of(o);
    packet *p = ep->pk_head;
    if (p == NULL) return lean_io_result_mk_ok(none());
    ep->pk_head = p->next;
    if (ep->pk_head == NULL) ep->pk_tail = NULL;
    lean_object *pair = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(pair, 0, mk_bytes(p->data, p->len));
    lean_ctor_set(pair, 1, addr_to_bytes(&p->to));
    free(p);
    return lean_io_result_mk_ok(some(pair));
}

/* The negotiated ALPN protocol of a connection; empty when none. */
LEAN_EXPORT lean_obj_res leanp2p_quic_alpn(b_lean_obj_arg o, uint64_t handle) {
    endpoint *ep = endpoint_of(o);
    qconn *c = find_conn(ep, handle);
    const unsigned char *p = NULL;
    unsigned int n = 0;
    if (c != NULL) SSL_get0_alpn_selected(c->ssl, &p, &n);
    return lean_io_result_mk_ok(
        lean_mk_string_from_bytes((const char *)(p != NULL ? p : (const unsigned char *)""), n));
}

/* The peer's address of a connection, as address bytes: the remote
   address of ngtcp2's current path, which follows a validated
   migration. Empty when the handle names no connection. */
LEAN_EXPORT lean_obj_res leanp2p_quic_remote(b_lean_obj_arg o, uint64_t handle) {
    endpoint *ep = endpoint_of(o);
    qconn *c = find_conn(ep, handle);
    if (c == NULL) return lean_io_result_mk_ok(mk_bytes(NULL, 0));
    const ngtcp2_addr *r = &ngtcp2_conn_get_path2(c->conn)->remote;
    struct sockaddr_storage ss;
    memset(&ss, 0, sizeof ss);
    if (r->addrlen > sizeof ss) return lean_io_result_mk_ok(mk_bytes(NULL, 0));
    memcpy(&ss, r->addr, r->addrlen);
    return lean_io_result_mk_ok(addr_to_bytes(&ss));
}
