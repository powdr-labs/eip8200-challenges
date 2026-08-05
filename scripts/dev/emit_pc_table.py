#!/usr/bin/env python3
"""Emit `instructionPC` lemmas for a set of instruction indices.

Usage: emit_pc_table.py <reference.hex> <lo>:<hi> [<lo>:<hi> ...] [--end]

Each lemma is an `rfl` that folds the instruction list up to its index, so the
table is quadratic in the highest index it mentions: a complete 847-entry table
for RIPEMD-160 costs over ten minutes of elaboration, while the 132 entries the
initialization and padding proofs need cost under two.  Generate the ranges a
module actually anchors on, not the whole program.

`--end` adds the one-past-the-end index, whose PC is the code size.
"""
import pathlib
import sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
from artifact import disassemble, load

ENTRY = """@[simp] theorem referenceArtifact_pc_{i} :
    referenceArtifact.instructionPC {i} = 0x{pc:x} := by rfl"""


def main():
    table = disassemble(load(sys.argv[1]))
    pcs = {ins["index"]: ins["pc"] for ins in table}
    pcs[len(table)] = table[-1]["pc"] + table[-1]["size"]

    want = set()
    for arg in sys.argv[2:]:
        if arg == "--end":
            want.add(len(table))
        elif ":" in arg:
            lo, hi = (int(x, 0) for x in arg.split(":"))
            want.update(range(lo, hi + 1))
        else:
            want.add(int(arg, 0))
    missing = [i for i in want if i not in pcs]
    if missing:
        sys.exit(f"index out of range: {sorted(missing)}")
    print("\n\n".join(ENTRY.format(i=i, pc=pcs[i]) for i in sorted(want)))


if __name__ == "__main__":
    main()
