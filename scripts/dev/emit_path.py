#!/usr/bin/env python3
"""Emit a `Stepper.Located` path for an index range of a frozen artifact.

Hand-transcribing anchors is the easiest way to introduce a silent mismatch, so
every `Located` entry the re-derivation needs is generated from the artifact
itself.  The rendering matches the corpus convention: `wfOp (by decide) trivial
rfl` for plain operations, `by decide` for pushes.
"""
import pathlib
import sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
from artifact import disassemble, load


def natlit(v):
    return hex(v) if v > 255 else str(v)


def entry(ins):
    i = ins["index"]
    k = ins["kind"]
    if k == "push":
        w = ins["width"]
        if w == 0:
            val = "⟨0⟩"
        else:
            val = f"(UInt256.ofNat {natlit(ins['value'])})"
        return (f"⟨{i}, .push ⟨{w}, by decide⟩ {val}, by rfl, by decide⟩")
    if k == "dup":
        return (f"⟨{i}, .op (.Dup ⟨{ins['idx']}, by decide⟩), by rfl, "
                f"wfOp (by decide) trivial rfl⟩")
    if k == "swap":
        return (f"⟨{i}, .op (.Swap ⟨{ins['idx']}, by decide⟩), by rfl, "
                f"wfOp (by decide) trivial rfl⟩")
    return (f"⟨{i}, .op .{ins['name']}, by rfl, "
            f"wfOp (by decide) trivial rfl⟩")


def main():
    path, lo, hi = sys.argv[1], int(sys.argv[2], 0), int(sys.argv[3], 0)
    table = disassemble(load(path))
    body = [entry(ins) for ins in table[lo:hi + 1]]
    print("  [" + ",\n   ".join(body) + "]")


if __name__ == "__main__":
    main()
