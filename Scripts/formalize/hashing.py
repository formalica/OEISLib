"""Lean's `String.hash`, so ids computed here equal the ones the Lean tools write.

`String.hash` is MurmurHash64A over the UTF-8 bytes with seed 11. `formula_hash` of an item and
`program.hash` are `hex(String.hash text)`; the check against stored `program.hash` values is in
`selftest`.
"""

from __future__ import annotations

_M = 0xC6A4A7935BD1E995
_MASK = (1 << 64) - 1
_R = 47
_SEED = 11


def string_hash(text: str) -> int:
    data = text.encode("utf-8")
    n = len(data)
    h = (_SEED ^ (n * _M)) & _MASK
    for i in range(0, n - n % 8, 8):
        k = int.from_bytes(data[i : i + 8], "little")
        k = (k * _M) & _MASK
        k ^= k >> _R
        k = (k * _M) & _MASK
        h ^= k
        h = (h * _M) & _MASK
    tail = data[n - n % 8 :]
    if tail:
        h ^= int.from_bytes(tail, "little")
        h = (h * _M) & _MASK
    h ^= h >> _R
    h = (h * _M) & _MASK
    h ^= h >> _R
    return h


def formula_hash(texts: list[str]) -> str:
    """The identity of an item: 16 hex chars of the hash of its original texts joined by `\\n`."""
    return f"{string_hash(chr(10).join(texts)):016x}"
