import Challenge.Bls12381G1Add.Reference.Proofs.Lowering

set_option warningAsError true

/-!
# Bounded G1ADD byte-assembly checks

The 1,083 lowered instructions are checked in blocks of at most 100.  This
keeps kernel reduction bounded while preserving an ordinary proof that their
assembled bytes equal the explicit 1,723-byte runtime.
-/

namespace Challenge.Bls12381G1Add.Reference.Proofs.Compilation

open YulEvmCompiler
open Challenge.Bls12381G1Add

def referenceInstructionChunk (index : Nat) : List Instr :=
  if index = 10 then
    referenceInstructions.drop (index * 100)
  else
    (referenceInstructions.drop (index * 100)).take 100

def referenceInstructionBytesChunk (index : Nat) : List UInt8 :=
  assembleBytes (referenceInstructionChunk index)

/-- Cumulative byte offsets after each 100-instruction block. -/
def referenceByteOffset : Nat → Nat
  | 0 => 0
  | 1 => 166
  | 2 => 370
  | 3 => 474
  | 4 => 683
  | 5 => 888
  | 6 => 1022
  | 7 => 1177
  | 8 => 1325
  | 9 => 1471
  | 10 => 1609
  | _ => 1723

def referenceFrozenBytesChunk (index : Nat) : List UInt8 :=
  (frozenReferenceBytes.drop (referenceByteOffset index)).take
    (referenceByteOffset (index + 1) - referenceByteOffset index)

end Challenge.Bls12381G1Add.Reference.Proofs.Compilation
