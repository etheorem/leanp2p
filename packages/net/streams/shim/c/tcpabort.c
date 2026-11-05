/*
 * The TCP abort of net/streams: end every pending request of a socket
 * that the Lean runtime's libuv binding holds.
 *
 * Lean v4.34 binds libuv TCP with no close call. The runtime closes a
 * handle in the finalizer of the socket object, and every pending
 * connect, write, and shutdown request holds a reference to that object
 * (src/runtime/uv/tcp.cpp). A write to a peer that stops reading never
 * completes, so its socket, and the descriptor, would live forever.
 *
 * This shim makes the kernel fail the pending requests instead:
 * shutdown(SHUT_RDWR) ends both directions, and connect(AF_UNSPEC)
 * dissolves the association (an unfinished connect aborts, and an
 * established connection sends RST). libuv then runs each request's
 * callback with an error, the callback drops its reference, and the
 * runtime's own finalizer closes the handle. The shim never calls
 * uv_close and never touches libuv's handle state, so the finalizer's
 * own uv_close stays the only one.
 */
#include <lean/lean.h>
#include <string.h>
#include <sys/socket.h>

/*
 * The one runtime-internal fact the shim relies on: the first field of
 * lean_uv_tcp_socket_object (src/runtime/uv/tcp.h) is the uv_tcp_t
 * pointer. A toolchain bump must re-read that header before it lifts
 * this guard.
 */
#if !(LEAN_VERSION_MAJOR == 4 && LEAN_VERSION_MINOR == 34)
#error "tcpabort.c: re-check lean_uv_tcp_socket_object in src/runtime/uv/tcp.h; m_uv_tcp must be the first field"
#endif

/* libuv ships in the toolchain's libuv.a with no header. The handle is
 * passed through as an opaque pointer; uv_os_fd_t is int on Unix. */
extern int uv_fileno(const void *handle, int *fd);

/* Std.Internal.UV.TCP.Socket → BaseIO Unit. A socket with no descriptor
 * yet (never bound, never connected) has no request to end, and the
 * call does nothing. */
LEAN_EXPORT lean_obj_res leanp2p_tcp_abort(b_lean_obj_arg sock, lean_obj_arg world) {
  (void)world;
  void **object = (void **)lean_get_external_data(sock);
  int fd = -1;
  if (uv_fileno(object[0], &fd) == 0 && fd >= 0) {
    /* Both calls are best effort. A failure means the socket is already
     * past the state the call ends (not connected, already shut), and
     * nothing is left to do. */
    (void)shutdown(fd, SHUT_RDWR);
    struct sockaddr unspec;
    memset(&unspec, 0, sizeof unspec);
    unspec.sa_family = AF_UNSPEC;
    (void)connect(fd, &unspec, sizeof unspec);
  }
  return lean_io_result_mk_ok(lean_box(0));
}
