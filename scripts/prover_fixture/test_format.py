"""Adversarial framing tests for the committed Rust prover captures."""

from pathlib import Path
import unittest

from prover_fixture.format import (
    CaptureError, MAGIC, MAX_BYTES, P, compress, decode, decompress, encode, records,
)

FIXTURES = Path(__file__).resolve().parents[2] / "Zcash/Snark/Fixtures/Prover"


class CaptureFormatTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.raw = decompress((FIXTURES / "single-honest.bin.gz").read_bytes())
        cls.events = records(cls.raw)

    def reject(self, events):
        with self.assertRaises(CaptureError):
            decode(encode(events), 1)

    def replace_first(self, tag, replacement):
        events = self.events.copy()
        index = next(i for i, (found, _) in enumerate(events) if found == tag)
        events[index] = replacement
        self.reject(events)

    def test_both_complete_captures(self):
        for name, actions in [("single-honest", 1), ("multi-honest", 2)]:
            raw = decompress((FIXTURES / (name + ".bin.gz")).read_bytes())
            decoded = decode(raw, actions)
            self.assertEqual(encode(records(raw)), raw)
            self.assertEqual(len(decoded["rng_words"]), 8 * (148 * actions + 46))
            self.assertEqual(len(decoded["challenges"]), 22)

    def test_truncated_or_extra_stream(self):
        for raw in [self.raw[:-1], self.raw + b"\0", self.raw[:8], b"IZKCAP02" + self.raw[8:]]:
            with self.assertRaises(CaptureError):
                decode(raw, 1)

    def test_noncanonical_field(self):
        self.replace_first(21, (21, b"\1" + P.to_bytes(32, "little")))

    def test_invalid_or_identity_message_point(self):
        for point in [b"\0", b"\1" + bytes(64), b"\2"]:
            self.replace_first(22, (22, b"\1" + point))

    def test_failed_write_cannot_be_success(self):
        payload = next(payload for tag, payload in self.events if tag == 23)
        self.replace_first(23, (23, b"\0" + payload[1:]))

    def test_terminal_result_required_once(self):
        self.reject(self.events[:-1])
        self.reject(self.events + [(30, b"")])
        self.replace_first(30, (31, b"Opening"))
        self.replace_first(30, (30, b"trailing"))

    def test_rng_method_and_width(self):
        self.replace_first(11, (10, bytes(4)))
        self.replace_first(11, (11, bytes(7)))
        self.replace_first(11, (11, bytes(9)))

    def test_rng_boundary_order(self):
        events = self.events.copy()
        challenge = next(i for i, (tag, _) in enumerate(events) if tag == 24)
        rng = next(i for i, (tag, _) in enumerate(events) if tag == 11)
        events[rng], events[challenge] = events[challenge], events[rng]
        self.reject(events)

    def test_setup_and_action_dimensions(self):
        payload = next(payload for tag, payload in self.events if tag == 1)
        self.replace_first(1, (1, (10).to_bytes(4, "little") + payload[4:]))
        with self.assertRaises(CaptureError):
            decode(self.raw, 2)
        with self.assertRaises(CaptureError):
            decode(self.raw, 3)

    def test_capacity_and_storage(self):
        with self.assertRaises(CaptureError):
            records(MAGIC + bytes(MAX_BYTES))
        with self.assertRaises(CaptureError):
            decompress(compress(bytes(MAX_BYTES + 1)))
        self.assertEqual(compress(self.raw), (FIXTURES / "single-honest.bin.gz").read_bytes())
        self.assertEqual(decompress(compress(self.raw)), self.raw)


if __name__ == "__main__":
    unittest.main()
