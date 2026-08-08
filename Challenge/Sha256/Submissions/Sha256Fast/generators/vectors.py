"""The 19 scored SHA-256 vectors, mirroring Challenge/Sha256/Scorer.lean."""


def patterned(n):
    return bytes(((i * 37 + (i // 251) * 11 + 7) % 256) for i in range(n))


def repeated(n, ch):
    return bytes(ch, "ascii") * n


VECTORS = [
    ("empty", b""),
    ("abc", b"abc"),
    ("1-byte", patterned(1)),
    ("31-byte", patterned(31)),
    ("32-byte", patterned(32)),
    ("54-byte", patterned(54)),
    ("55-byte (last one-block)", patterned(55)),
    ("56-byte (length spills)", patterned(56)),
    ("fips-b2 (56-byte)", b"abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq"),
    ("63-byte", patterned(63)),
    ("64-byte (exact block)", patterned(64)),
    ("65-byte", patterned(65)),
    ("119-byte", patterned(119)),
    ("120-byte", patterned(120)),
    ("127-byte", patterned(127)),
    ("128-byte (two blocks)", patterned(128)),
    ("256-byte", patterned(256)),
    ("1000-byte", patterned(1000)),
    ("1000 a's", repeated(1000, "a")),
]

# Gas the pinned Lean semantics reports for the frozen reference bytecode.
REFERENCE_GAS = [
    158035, 158038, 158038, 158038, 158038, 158041, 158041, 314044, 314044,
    314044, 314044, 314047, 314050, 470053, 470053, 470053, 782070, 2498174,
    2498174,
]
