import Tests.Support

/-!
# Demo and pingnode arguments

The checks run the built binaries. Each one records the exit code,
an empty stdout, and the stderr line. A valid list reaches the
unfinished diagnostic. A usage error exits 2.
-/

set_option autoImplicit false

namespace Tests.Cli

/-- An Ed25519 peer id from the identity suite. -/
private def peer : String :=
  "12D3KooWD3eckifWpRn9wQpMG9R9hX3sD158z7EqHWmweQAJU5SA"

/-- Run one built executable and compare its exit, stdout, and stderr. -/
private def expect (runner : Runner) (name exe : String) (args : Array String)
    (code : UInt32) (stderr : String) : IO Unit := do
  let out ← IO.Process.output { cmd := s!".lake/build/bin/{exe}", args }
  runner.check s!"{name}: exit {code}" (out.exitCode == code)
  runner.check s!"{name}: stdout empty" (out.stdout == "")
  runner.check s!"{name}: stderr" (out.stderr == stderr ++ "\n")

/-- The argument table of the demo and the ping node. -/
def run (runner : Runner) : IO Unit := do
  runner.section "cli arguments" "packages/cli/Demo.lean, packages/cli/PingNode.lean"
  expect runner "demo empty" "demo" #[] 1 "demo: not implemented"
  expect runner "demo one argument" "demo" #["foo"] 2
    "Redundant positional argument `foo`."
  expect runner "demo two arguments" "demo" #["foo", "bar"] 2
    "Redundant positional argument `foo`."
  expect runner "demo help" "demo" #["--help"] 2 "Unknown flag `--help`."
  expect runner "demo short help" "demo" #["-h"] 2 "Unknown flag `-h`."
  expect runner "demo version" "demo" #["--version"] 2 "Unknown flag `--version`."
  expect runner "demo end of flags" "demo" #["--"] 2 "unexpected argument: --"
  expect runner "pingnode missing subcommand" "pingnode" #[] 2 "missing subcommand"
  expect runner "pingnode unknown subcommand" "pingnode" #["foo"] 2
    "Redundant positional argument `foo`."
  expect runner "pingnode help" "pingnode" #["--help"] 2 "Unknown flag `--help`."
  expect runner "pingnode serve missing port" "pingnode" #["serve"] 2
    "Missing positional argument `<port>.`"
  expect runner "pingnode serve 0" "pingnode" #["serve", "0"] 1
    "pingnode: not implemented"
  expect runner "pingnode serve 1" "pingnode" #["serve", "1"] 1
    "pingnode: not implemented"
  expect runner "pingnode serve 65535" "pingnode" #["serve", "65535"] 1
    "pingnode: not implemented"
  expect runner "pingnode serve 65536" "pingnode" #["serve", "65536"] 2
    "invalid port: 65536"
  expect runner "pingnode serve 00" "pingnode" #["serve", "00"] 2 "invalid port: 00"
  expect runner "pingnode serve 01" "pingnode" #["serve", "01"] 2 "invalid port: 01"
  expect runner "pingnode serve sign" "pingnode" #["serve", "-1"] 2 "Unknown flag `-1`."
  expect runner "pingnode serve plus" "pingnode" #["serve", "+1"] 2 "invalid port: +1"
  expect runner "pingnode serve leading space" "pingnode" #["serve", " 1"] 2
    "invalid port:  1"
  expect runner "pingnode serve trailing space" "pingnode" #["serve", "1 "] 2
    "invalid port: 1 "
  expect runner "pingnode serve nondigit" "pingnode" #["serve", "1a"] 2
    "invalid port: 1a"
  expect runner "pingnode serve extra" "pingnode" #["serve", "1", "extra"] 2
    "Redundant positional argument `extra`."
  let dial := s!"/ip4/127.0.0.1/tcp/4001/p2p/{peer}"
  expect runner "pingnode dial missing address" "pingnode" #["dial"] 2
    "Missing positional argument `<multiaddr>.`"
  expect runner "pingnode dial" "pingnode" #[ "dial", dial ] 1
    "pingnode: not implemented"
  expect runner "pingnode dial port 0" "pingnode"
    #[ "dial", s!"/ip4/127.0.0.1/tcp/0/p2p/{peer}" ] 1
    "pingnode: not implemented"
  expect runner "pingnode dial extra" "pingnode" #[ "dial", dial, "extra" ] 2
    "Redundant positional argument `extra`."
  expect runner "pingnode dial parse" "pingnode" #["dial", "not-an-addr"] 2
    "Multiformats.Error.badAddress not-an-addr"
  expect runner "pingnode dial bare peer component" "pingnode" #["dial", "/p2p"] 2
    "Multiformats.Error.badValue /p2p"
  expect runner "pingnode dial no peer" "pingnode" #["dial", "/ip4/127.0.0.1/tcp/4001"] 2
    "dial address has no final /p2p peer: /ip4/127.0.0.1/tcp/4001"
  expect runner "pingnode dial peer only" "pingnode" #[ "dial", s!"/p2p/{peer}" ] 2
    s!"no transport handles /p2p/{peer} /p2p/{peer}"
  expect runner "pingnode dial peer not final" "pingnode"
    #[ "dial", s!"/ip4/127.0.0.1/p2p/{peer}/tcp/4001" ] 2
    s!"dial address has no final /p2p peer: /ip4/127.0.0.1/p2p/{peer}/tcp/4001"
  expect runner "pingnode dial repeated peer" "pingnode"
    #[ "dial", s!"/ip4/127.0.0.1/tcp/4001/p2p/{peer}/p2p/{peer}" ] 2
    s!"dial address has an earlier /p2p peer: /ip4/127.0.0.1/tcp/4001/p2p/{peer}/p2p/{peer}"
  expect runner "pingnode dial earlier peer" "pingnode"
    #[ "dial", s!"/ip4/127.0.0.1/p2p/{peer}/tcp/4001/p2p/{peer}" ] 2
    s!"dial address has an earlier /p2p peer: /ip4/127.0.0.1/p2p/{peer}/tcp/4001/p2p/{peer}"
  expect runner "pingnode serve newline" "pingnode" #["serve", "1\n"] 2
    "invalid port: 1\\n"
  expect runner "pingnode dial newline" "pingnode" #["dial", "not-an-addr\n"] 2
    "Multiformats.Error.badAddress not-an-addr\\n"

end Tests.Cli
