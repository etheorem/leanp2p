"""Driver unit tests; these exercise child-process handling, not libp2p interop."""
import importlib.util
from pathlib import Path
import sys
import tempfile
import time
import unittest

SPEC = importlib.util.spec_from_file_location("ping_interop", Path(__file__).with_name("ping-interop.py"))
GATE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(GATE)


class DriverTests(unittest.TestCase):
    def test_readiness_pins_the_announced_peer(self):
        self.assertEqual(GATE.peer_address("ADDR /ip4/127.0.0.1/tcp/1234 peer"),
                         "/ip4/127.0.0.1/tcp/1234/p2p/peer")
        self.assertEqual(GATE.peer_address("ADDR /ip4/127.0.0.1/tcp/1234/p2p/peer peer"),
                         "/ip4/127.0.0.1/tcp/1234/p2p/peer")

    def test_readiness_rejects_invalid_contracts(self):
        for line in ["", "ADDR a", "ADDR /ip4/127.0.0.1/tcp/0 peer",
                     "ADDR /ip4/127.0.0.1/tcp/65536 peer", "ADDR /ip4/0.0.0.0/tcp/80 peer",
                     "ADDR /ip4/127.0.0.1/tcp/80/p2p/other peer", "ADDR a peer extra"]:
            with self.subTest(line=line), self.assertRaises(ValueError):
                GATE.peer_address(line)

    def test_early_exit_does_not_announce_success(self):
        with tempfile.TemporaryDirectory() as directory:
            with GATE.server([sys.executable, "-c", "raise SystemExit(1)"], Path(directory) / "stderr") as process:
                with self.assertRaises(RuntimeError):
                    GATE.readiness(process, 1)
            self.assertIsNotNone(process.poll())

    def test_partial_line_obeys_the_deadline_and_child_is_joined(self):
        code = "import sys;sys.stdout.write('ADDR partial');sys.stdout.flush();sys.stdin.read()"
        with tempfile.TemporaryDirectory() as directory:
            with GATE.server([sys.executable, "-c", code], Path(directory) / "stderr") as process:
                started = time.monotonic()
                with self.assertRaises(TimeoutError):
                    GATE.readiness(process, 0.15)
                self.assertLess(time.monotonic() - started, 2)
            self.assertEqual(process.returncode, 0)

    def test_oversized_line_is_rejected(self):
        code = "import sys;sys.stdout.write('x'*9000);sys.stdout.flush();sys.stdin.read()"
        with tempfile.TemporaryDirectory() as directory:
            with GATE.server([sys.executable, "-c", code], Path(directory) / "stderr") as process:
                with self.assertRaises(RuntimeError):
                    GATE.readiness(process, 1)
            self.assertIsNotNone(process.poll())

    def test_nonzero_dial_exit_never_passes(self):
        with self.assertRaises(RuntimeError):
            GATE.require_ping([sys.executable, "-c", "print('PING OK rtt=7ms');raise SystemExit(1)"])

    def test_zero_exit_without_ping_result_never_passes(self):
        with self.assertRaises(RuntimeError):
            GATE.require_ping([sys.executable, "-c", "print('not a ping result')"])

    def test_default_mock_binary_never_announces_a_live_address(self):
        if not (GATE.ROOT / "packages/cli/CliApp/Mock/Stack.lean").exists():
            self.skipTest("mocks removed; run the live networking gates")
        binary = GATE.ROOT / ".lake/build/bin/pingnode"
        self.assertTrue(binary.is_file(), "lake build must build pingnode before driver checks")
        with tempfile.TemporaryDirectory() as directory:
            log = Path(directory) / "stderr"
            with GATE.server([str(binary), "serve", "0"], log) as process:
                with self.assertRaises(RuntimeError):
                    GATE.readiness(process, 5)
            self.assertEqual(process.returncode, 1)
            self.assertIn("not integrated", log.read_text())


if __name__ == "__main__":
    unittest.main()
