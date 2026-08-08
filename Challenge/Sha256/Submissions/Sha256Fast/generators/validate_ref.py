import hashlib, sys
from evm import execute
from vectors import VECTORS, REFERENCE_GAS

code = bytes.fromhex(open(__import__("pathlib").Path(__file__).resolve().parents[3] / "Reference" / "reference.hex").read().strip())
print("reference size", len(code))
ok = True
for (label, data), expect in zip(VECTORS, REFERENCE_GAS):
    h, gas, vm = execute(code, data)
    digest = hashlib.sha256(data).digest()
    good = (h.kind == "return" and h.data == digest)
    if not good or gas != expect:
        ok = False
    print(f"{label:28s} halt={h.kind:8s} digest={'ok' if good else 'BAD'} gas={gas} expect={expect} delta={gas-expect}")
print("ALL OK" if ok else "MISMATCH")
