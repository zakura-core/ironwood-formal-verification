"""Strict decoder for the observational IZKCAP01 stream.

This validates framing and release dimensions; the independent Lean decoder and
prover replay validate the algebra. Gzip is only storage compression: digests and
regeneration comparisons bind the uncompressed stream as well.
"""

from collections import Counter
from dataclasses import dataclass
import gzip
import io
import struct

MAGIC = b"IZKCAP01"
P = 28948022309329048855892746252171976963363056481941560715954676764349967630337
Q = 28948022309329048855892746252171976963363056481941647379679742748393362948097
MAX_BYTES = 8_000_000


class CaptureError(ValueError):
    """A capture is malformed or outside the supported release profile."""


def require(condition: bool, message: str) -> None:
    if not condition:
        raise CaptureError(message)


@dataclass
class Reader:
    data: bytes
    offset: int = 0

    def take(self, size: int) -> bytes:
        require(0 <= size <= len(self.data) - self.offset, "truncated capture")
        result = self.data[self.offset:self.offset + size]
        self.offset += size
        return result

    def number(self) -> int:
        return int.from_bytes(self.take(4), "little")

    def field(self, modulus: int = P) -> int:
        value = int.from_bytes(self.take(32), "little")
        require(value < modulus, "noncanonical field representative")
        return value

    def point(self) -> tuple[int, int] | None:
        flag = self.take(1)
        if flag == b"\0":
            return None
        require(flag == b"\1", "invalid point flag")
        x, y = self.field(Q), self.field(Q)
        require((y * y - x * x * x - 5) % Q == 0, "point is not on Vesta")
        return x, y

    def fields(self, count: int) -> list[int]:
        require(self.number() == count, "unsupported field-vector dimension")
        return [self.field() for _ in range(count)]

    def matrix(self, columns: int) -> list[list[int]]:
        require(self.number() == columns, "unsupported column count")
        return [self.fields(2048) for _ in range(columns)]

    def end(self) -> None:
        require(self.offset == len(self.data), "trailing payload data")


def records(data: bytes) -> list[tuple[int, bytes]]:
    require(len(data) <= MAX_BYTES, "capture exceeds supported capacity")
    reader = Reader(data)
    require(reader.take(len(MAGIC)) == MAGIC, "unsupported capture version")
    result = []
    while reader.offset < len(data):
        tag = reader.take(1)[0]
        result.append((tag, reader.take(reader.number())))
    return result


def encode(events: list[tuple[int, bytes]]) -> bytes:
    return MAGIC + b"".join(bytes([tag]) + struct.pack("<I", len(payload)) + payload
                            for tag, payload in events)


def compress(data: bytes) -> bytes:
    output = io.BytesIO()
    with gzip.GzipFile(fileobj=output, mode="wb", filename="", mtime=0, compresslevel=9) as stream:
        stream.write(data)
    return output.getvalue()


def decompress(data: bytes) -> bytes:
    with gzip.GzipFile(fileobj=io.BytesIO(data), mode="rb") as stream:
        result = stream.read(MAX_BYTES + 1)
    require(len(result) <= MAX_BYTES, "decompressed capture exceeds supported capacity")
    return result


def decode(data: bytes, actions: int) -> dict:
    """Accept only complete successful executions for the two declared drivers."""
    require(actions in (1, 2), "unsupported Action count")
    events = records(data)
    counts = Counter(tag for tag, _ in events)
    require(counts == {1: 1, 2: 1, 3: 1, 11: 8 * (148 * actions + 46),
                       20: actions, 21: 1, 22: 22 * actions + 33,
                       23: 49 * actions + 52, 24: 22, 30: 1},
            "unsupported event inventory or incomplete execution")
    require(events[0][0] == 21 and events[-1] == (30, b""), "invalid call boundaries")
    require([tag for tag, _ in events[:4 + actions]] == [21, 1, 2] + [20] * actions + [3],
            "invalid initialization or witness boundary")
    result = {"rng_words": [], "challenges": [], "transcript": []}
    for tag, payload in events:
        reader = Reader(payload)
        if tag == 1:
            require(tuple(reader.number() for _ in range(5)) == (11, 2048, 5, 9, 2048),
                    "unsupported prover setup")
            result["generators"] = [reader.point() for _ in range(2048)]
            result["w"], result["u"] = reader.point(), reader.point()
            result["fixed"] = reader.matrix(29)
            require(reader.number() == actions, "instance Action count mismatch")
            result["instances"] = []
            for _ in range(actions):
                require(reader.number() == 1, "unsupported instance-column count")
                result["instances"].append(reader.fields(10))
        elif tag == 2:
            result["sigma"] = reader.matrix(15)
        elif tag == 3:
            require(reader.number() == actions, "witness Action count mismatch")
            result["witness"] = [reader.matrix(10) for _ in range(actions)]
        elif tag == 11:
            result["rng_words"].append(int.from_bytes(reader.take(8), "little"))
        elif tag in (20, 21, 22, 23):
            require(reader.take(1) == b"\1", "failed transcript write in success capture")
            value = reader.point() if tag in (20, 22) else reader.field()
            if tag in (20, 22):
                require(value is not None, "identity point in success capture")
            result["transcript"].append((tag, value))
        elif tag == 24:
            result["challenges"].append(reader.field())
            result["transcript"].append((tag, len(result["rng_words"])))
        reader.end()
    expected = [70 * actions, 112 * actions, 112 * actions,
                148 * actions + 3, 148 * actions + 11,
                148 * actions + 11, 148 * actions + 11,
                148 * actions + 12, 148 * actions + 12,
                148 * actions + 24, 148 * actions + 24]
    expected += [148 * actions + 26 + 2 * i for i in range(11)]
    require([value for tag, value in result["transcript"] if tag == 24] ==
            [8 * count for count in expected], "RNG consumption changed across protocol stages")
    result["counts"] = dict(sorted(counts.items()))
    return result
