/-! POSIX hostname binding for the interop participant. -/
@[extern "interop_participant_hostname"]
opaque InteropHostname.get : IO String
