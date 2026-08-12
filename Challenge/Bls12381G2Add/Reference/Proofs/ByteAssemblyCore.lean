import Challenge.Bls12381G2Add.Reference.Proofs.Lowering

set_option warningAsError true

/-! Bounded G2ADD byte-assembly chunks. -/

namespace Challenge.Bls12381G2Add.Reference.Proofs.Compilation

open YulEvmCompiler

def referenceInstructionChunk (index : Nat) : List Instr :=
  if index = 17 then
    referenceInstructions.drop (index * 100)
  else
    (referenceInstructions.drop (index * 100)).take 100

def referenceInstructionBytesChunk (index : Nat) : List UInt8 :=
  assembleBytes (referenceInstructionChunk index)

def referenceComputedByteOffset (index : Nat) : Nat :=
  (assembleBytes (referenceInstructions.take (index * 100))).length

/-- Cumulative byte offsets after each 100-instruction block. -/
def referenceByteOffset : Nat → Nat
  | 0 => 0
  | 1 => 166
  | 2 => 370
  | 3 => 474
  | 4 => 683
  | 5 => 890
  | 6 => 1021
  | 7 => 1147
  | 8 => 1287
  | 9 => 1436
  | 10 => 1580
  | 11 => 1721
  | 12 => 1881
  | 13 => 2020
  | 14 => 2151
  | 15 => 2324
  | 16 => 2492
  | 17 => 2713
  | _ => 2788

def referenceFrozenBytesChunk (index : Nat) : List UInt8 :=
  (Challenge.Bls12381G2Add.frozenReferenceBytes.drop
    (referenceByteOffset index)).take
      (referenceByteOffset (index + 1) - referenceByteOffset index)

end Challenge.Bls12381G2Add.Reference.Proofs.Compilation
