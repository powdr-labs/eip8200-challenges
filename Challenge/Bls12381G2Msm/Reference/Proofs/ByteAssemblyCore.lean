import Challenge.Bls12381G2Msm.Reference.Proofs.Lowering
import Challenge.Bls12381G2Msm.Reference.FrozenBytecode

set_option warningAsError true

namespace Challenge.Bls12381G2Msm.Reference.Proofs.Compilation

open YulEvmCompiler

def referenceInstructionChunk (index : Nat) : List Instr :=
  if index = 20 then referenceInstructions.drop (index * 100)
  else (referenceInstructions.drop (index * 100)).take 100

def referenceInstructionBytesChunk (index : Nat) : List UInt8 :=
  assembleBytes (referenceInstructionChunk index)

def referenceComputedByteOffset (index : Nat) : Nat :=
  (assembleBytes (referenceInstructions.take (index * 100))).length

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
  | 13 => 2021
  | 14 => 2151
  | 15 => 2273
  | 16 => 2406
  | 17 => 2600
  | 18 => 2814
  | 19 => 2986
  | 20 => 3125
  | 21 => 3264
  | _ => 3264

def referenceFrozenBytesChunk (index : Nat) : List UInt8 :=
  (Challenge.Bls12381G2Msm.frozenReferenceBytes.drop
    (referenceByteOffset index)).take
      (referenceByteOffset (index + 1) - referenceByteOffset index)

end Challenge.Bls12381G2Msm.Reference.Proofs.Compilation
