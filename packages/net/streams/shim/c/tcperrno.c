/*
 * The errno of a TCP reset for net/streams: the platform's ECONNRESET.
 *
 * The Lean runtime reports a failed libuv read as IO.Error. A reset by
 * the peer becomes resourceVanished with the errno as its osCode, the
 * same constructor as EPIPE, ENETDOWN, and ENETRESET (Init/System/
 * IOError.lean). Only the code tells the peer's reset apart, and its
 * value differs between platforms (104 on Linux, 54 on the BSDs and
 * macOS). Lean exposes no errno constants, so the shim reads it from
 * <errno.h>.
 */
#include <errno.h>
#include <stdint.h>
#include <lean/lean.h>

/* Unit → UInt32: the platform's ECONNRESET. A constant, so the binding
 * is pure, in the form of the runtime's own platform constants
 * (lean_system_platform_target in lean.h). */
LEAN_EXPORT uint32_t leanp2p_tcp_econnreset(lean_obj_arg unit) {
  (void)unit;
  return (uint32_t)ECONNRESET;
}
