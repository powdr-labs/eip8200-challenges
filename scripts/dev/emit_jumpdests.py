#!/usr/bin/env python3
"""Emit a `validJumpDest_<pc>` certificate for every JUMPDEST in an artifact.

The old certificates named the old layout's targets.  Rather than guess which
targets the re-derived proofs will reach, certify all of them: the set is small
(25 for RIPEMD-160, 36 for SHA-256) and each lemma is a `simpa` over the
artifact's own `isValidJumpDest_index`.
"""
import pathlib
import sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
from artifact import disassemble, load

TEMPLATE = """@[simp] theorem validJumpDest_{name} :
    Decode.isValidJumpDest referenceBytecode 0x{pc:x} = true := by
  have h := referenceArtifact.isValidJumpDest_index {index} (by rfl)
  change Decode.isValidJumpDest referenceBytecode
    (referenceArtifact.instructionPC {index}) = true at h
  have hpc : referenceArtifact.instructionPC {index} = 0x{pc:x} := by rfl
  rwa [hpc] at h"""


def main():
    table = disassemble(load(sys.argv[1]))
    out = []
    for ins in table:
        if ins["kind"] == "op" and ins["name"] == "JUMPDEST":
            out.append(TEMPLATE.format(name=f"{ins['pc']:x}", pc=ins["pc"],
                                       index=ins["index"]))
    print("\n\n".join(out))


if __name__ == "__main__":
    main()
