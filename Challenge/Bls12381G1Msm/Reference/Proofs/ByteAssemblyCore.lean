import Challenge.Bls12381G1Msm.Reference.Proofs.Lowering

set_option warningAsError true

/-!
# Bounded G1MSM byte-assembly checks

The 1,870 lowered instructions are checked in blocks of at most 100 so each
kernel reduction stays behind a small `.olean` boundary.
-/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.Compilation

open YulEvmCompiler
open Challenge.Bls12381G1Msm

def referenceInstructionChunk (index : Nat) : List Instr :=
  if index = 18 then referenceInstructions.drop (index * 100)
  else (referenceInstructions.drop (index * 100)).take 100

def referenceInstructionBytesChunk (index : Nat) : List UInt8 :=
  assembleBytes (referenceInstructionChunk index)

/-- Cumulative byte offsets after each 100-instruction block. -/
def referenceByteOffset : Nat → Nat
  | 0 => 0
  | 1 => 184
  | 2 => 462
  | 3 => 670
  | 4 => 802
  | 5 => 945
  | 6 => 1092
  | 7 => 1242
  | 8 => 1512
  | 9 => 1749
  | 10 => 1946
  | 11 => 2115
  | 12 => 2341
  | 13 => 2629
  | 14 => 2823
  | 15 => 3048
  | 16 => 3225
  | 17 => 3388
  | 18 => 3589
  | _ => 3688

def referenceFrozenBytesChunk (index : Nat) : List UInt8 :=
  (frozenReferenceBytes.drop (referenceByteOffset index)).take
    (referenceByteOffset (index + 1) - referenceByteOffset index)

end Challenge.Bls12381G1Msm.Reference.Proofs.Compilation
