import Challenge.Bls12381G2Msm.Reference.Proofs.ByteAssemblyChunk0
import Challenge.Bls12381G2Msm.Reference.Proofs.ByteAssemblyChunk1
import Challenge.Bls12381G2Msm.Reference.Proofs.ByteAssemblyChunk2
import Challenge.Bls12381G2Msm.Reference.Proofs.ByteAssemblyChunk3
import Challenge.Bls12381G2Msm.Reference.Proofs.ByteAssemblyChunk4
import Challenge.Bls12381G2Msm.Reference.Proofs.ByteAssemblyChunk5
import Challenge.Bls12381G2Msm.Reference.Proofs.ByteAssemblyChunk6
import Challenge.Bls12381G2Msm.Reference.Proofs.ByteAssemblyChunk7
import Challenge.Bls12381G2Msm.Reference.Proofs.ByteAssemblyChunk8
import Challenge.Bls12381G2Msm.Reference.Proofs.ByteAssemblyChunk9
import Challenge.Bls12381G2Msm.Reference.Proofs.ByteAssemblyChunk10
import Challenge.Bls12381G2Msm.Reference.Proofs.ByteAssemblyChunk11
import Challenge.Bls12381G2Msm.Reference.Proofs.ByteAssemblyChunk12
import Challenge.Bls12381G2Msm.Reference.Proofs.ByteAssemblyChunk13
import Challenge.Bls12381G2Msm.Reference.Proofs.ByteAssemblyChunk14
import Challenge.Bls12381G2Msm.Reference.Proofs.ByteAssemblyChunk15
import Challenge.Bls12381G2Msm.Reference.Proofs.ByteAssemblyChunk16
import Challenge.Bls12381G2Msm.Reference.Proofs.ByteAssemblyChunk17
import Challenge.Bls12381G2Msm.Reference.Proofs.ByteAssemblyChunk18
import Challenge.Bls12381G2Msm.Reference.Proofs.ByteAssemblyChunk19
import Challenge.Bls12381G2Msm.Reference.Proofs.ByteAssemblyChunk20

set_option warningAsError true

/-!
# G2MSM byte-assembly reconstruction

Concrete reductions live in bounded chunk modules. This module combines their
opaque equalities through generic list identities.
-/

namespace Challenge.Bls12381G2Msm.Reference.Proofs.Compilation

open YulEvmCompiler
open Challenge.Bls12381G2Msm

private def chunksOf (size : Nat) : Nat → List α → List (List α)
  | 0, xs => [xs]
  | count + 1, xs => xs.take size :: chunksOf size count (xs.drop size)

private theorem flatten_chunksOf (size count : Nat) (xs : List α) :
    (chunksOf size count xs).flatten = xs := by
  induction count generalizing xs with
  | zero => simp [chunksOf]
  | succ count ih =>
      simp only [chunksOf, List.flatten_cons, ih]
      exact List.take_append_drop size xs

private theorem assembleBytes_flatten (chunks : List (List Instr)) :
    assembleBytes chunks.flatten = (chunks.map assembleBytes).flatten := by
  induction chunks with
  | nil => rfl
  | cons chunk chunks ih =>
      simp only [List.flatten_cons, assembleBytes_append, List.map_cons, ih]

private def referenceInstructionByteChunks : List (List UInt8) :=
[    referenceInstructionBytesChunk 0,
    referenceInstructionBytesChunk 1,
    referenceInstructionBytesChunk 2,
    referenceInstructionBytesChunk 3,
    referenceInstructionBytesChunk 4,
    referenceInstructionBytesChunk 5,
    referenceInstructionBytesChunk 6,
    referenceInstructionBytesChunk 7,
    referenceInstructionBytesChunk 8,
    referenceInstructionBytesChunk 9,
    referenceInstructionBytesChunk 10,
    referenceInstructionBytesChunk 11,
    referenceInstructionBytesChunk 12,
    referenceInstructionBytesChunk 13,
    referenceInstructionBytesChunk 14,
    referenceInstructionBytesChunk 15,
    referenceInstructionBytesChunk 16,
    referenceInstructionBytesChunk 17,
    referenceInstructionBytesChunk 18,
    referenceInstructionBytesChunk 19,
    referenceInstructionBytesChunk 20]

private def referenceFrozenByteChunks : List (List UInt8) :=
[    referenceFrozenBytesChunk 0,
    referenceFrozenBytesChunk 1,
    referenceFrozenBytesChunk 2,
    referenceFrozenBytesChunk 3,
    referenceFrozenBytesChunk 4,
    referenceFrozenBytesChunk 5,
    referenceFrozenBytesChunk 6,
    referenceFrozenBytesChunk 7,
    referenceFrozenBytesChunk 8,
    referenceFrozenBytesChunk 9,
    referenceFrozenBytesChunk 10,
    referenceFrozenBytesChunk 11,
    referenceFrozenBytesChunk 12,
    referenceFrozenBytesChunk 13,
    referenceFrozenBytesChunk 14,
    referenceFrozenBytesChunk 15,
    referenceFrozenBytesChunk 16,
    referenceFrozenBytesChunk 17,
    referenceFrozenBytesChunk 18,
    referenceFrozenBytesChunk 19,
    referenceFrozenBytesChunk 20]

private theorem referenceInstructions_split_assemble :
    assembleBytes referenceInstructions =
      referenceInstructionByteChunks.flatten := by
  rw [← flatten_chunksOf 100 20 referenceInstructions, assembleBytes_flatten]
  simp [chunksOf, referenceInstructionByteChunks,
    referenceInstructionBytesChunk, referenceInstructionChunk,
    List.drop_drop]

private theorem referenceInstructionByteChunks_eq :
    referenceInstructionByteChunks = referenceFrozenByteChunks := by
  unfold referenceInstructionByteChunks referenceFrozenByteChunks
  rw [referenceInstructionChunk0_bytes,
    referenceInstructionChunk1_bytes,
    referenceInstructionChunk2_bytes,
    referenceInstructionChunk3_bytes,
    referenceInstructionChunk4_bytes,
    referenceInstructionChunk5_bytes,
    referenceInstructionChunk6_bytes,
    referenceInstructionChunk7_bytes,
    referenceInstructionChunk8_bytes,
    referenceInstructionChunk9_bytes,
    referenceInstructionChunk10_bytes,
    referenceInstructionChunk11_bytes,
    referenceInstructionChunk12_bytes,
    referenceInstructionChunk13_bytes,
    referenceInstructionChunk14_bytes,
    referenceInstructionChunk15_bytes,
    referenceInstructionChunk16_bytes,
    referenceInstructionChunk17_bytes,
    referenceInstructionChunk18_bytes,
    referenceInstructionChunk19_bytes,
    referenceInstructionChunk20_bytes]

set_option maxRecDepth 30000 in
private theorem referenceFrozenByteChunks_flatten :
    referenceFrozenByteChunks.flatten = frozenReferenceBytes := by
  with_unfolding_all decide

theorem referenceInstructions_assemble :
    assemble referenceInstructions = referenceBytecode := by
  unfold referenceBytecode
  apply ByteArray.ext
  change (assembleBytes referenceInstructions).toArray =
    frozenReferenceBytes.toArray
  rw [referenceInstructions_split_assemble,
    referenceInstructionByteChunks_eq,
    referenceFrozenByteChunks_flatten]

end Challenge.Bls12381G2Msm.Reference.Proofs.Compilation
