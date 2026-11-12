/-!
# The constants of `net/tls`

Each fact has one home (root ARCHITECTURE §3.8). TLS fixes the record
size, and this package takes its read size from it.
-/

set_option autoImplicit false

namespace Tls

/-- The largest plaintext of one TLS record: 2^14 bytes (RFC 8446
§5.1, "The length MUST NOT exceed 2^14 bytes"). One secure read asks
the engine for at most this many bytes, so one read answers at most
one record of plaintext, and the read allocates no more. -/
def maxRecordPlaintext : Nat := 16384

end Tls
