"""Check that the committed .hex artifacts are exactly what the committed
generators emit.

The hex files are outputs, not hand-maintained data; this is the check that
says so mechanically.  Run from anywhere:

    python3 check_hex.py
"""
import pathlib
import importlib
import sys

HERE = pathlib.Path(__file__).resolve().parent
ROOT = HERE.parent
sys.path.insert(0, str(HERE))

# committed artifact  <-  generator that must reproduce it byte for byte
ARTIFACTS = [
    ("bytecode.hex", "sha256gen4"),
]

ok = True
for name, generator in ARTIFACTS:
    committed = (ROOT / name).read_text().strip()
    emitted = importlib.import_module(generator).generate().hex()
    match = committed == emitted
    ok &= match
    print(
        f"{name:14s} <- {generator + '.generate()':22s} "
        f"{len(emitted) // 2:5d} bytes  {'match' if match else 'MISMATCH'}"
    )
    if not match:
        print(f"  committed {len(committed) // 2} bytes, emitted {len(emitted) // 2} bytes")

print("ALL OK" if ok else "MISMATCH")
sys.exit(0 if ok else 1)
