import Challenge.Bls12381G2Add.Reference.Proofs.ByteAssemblyChunks

set_option warningAsError true

/-!
# G2ADD byte-assembly reconstruction

Concrete reductions live in the bounded chunk modules. This module combines
their opaque equalities through generic list identities.
-/

namespace Challenge.Bls12381G2Add.Reference.Proofs.Compilation

open YulEvmCompiler
open Challenge.Bls12381G2Add

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
    referenceInstructionBytesChunk 17]

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
    referenceFrozenBytesChunk 17]

private theorem referenceInstructions_split_assemble :
    assembleBytes referenceInstructions =
      referenceInstructionByteChunks.flatten := by
  rw [← flatten_chunksOf 100 17 referenceInstructions, assembleBytes_flatten]
  simp [chunksOf, referenceInstructionByteChunks,
    referenceInstructionBytesChunk, referenceInstructionChunk,
    List.drop_drop]

private theorem referenceInstructionByteChunks_eq :
    referenceInstructionByteChunks = referenceFrozenByteChunks := by
  unfold referenceInstructionByteChunks referenceFrozenByteChunks
  rw [referenceInstructionBytesChunk0,
    referenceInstructionBytesChunk1,
    referenceInstructionBytesChunk2,
    referenceInstructionBytesChunk3,
    referenceInstructionBytesChunk4,
    referenceInstructionBytesChunk5,
    referenceInstructionBytesChunk6,
    referenceInstructionBytesChunk7,
    referenceInstructionBytesChunk8,
    referenceInstructionBytesChunk9,
    referenceInstructionBytesChunk10,
    referenceInstructionBytesChunk11,
    referenceInstructionBytesChunk12,
    referenceInstructionBytesChunk13,
    referenceInstructionBytesChunk14,
    referenceInstructionBytesChunk15,
    referenceInstructionBytesChunk16,
    referenceInstructionBytesChunk17]

set_option maxRecDepth 30000 in
private theorem referenceFrozenByteChunks_flatten :
    referenceFrozenByteChunks.flatten = frozenReferenceBytes := by
  with_unfolding_all decide

theorem referenceInstructions_assemble :
    assemble referenceInstructions = referenceBytecode := by
  apply ByteArray.ext
  change (assembleBytes referenceInstructions).toArray =
    frozenReferenceBytes.toArray
  rw [referenceInstructions_split_assemble,
    referenceInstructionByteChunks_eq,
    referenceFrozenByteChunks_flatten]

/-- The frozen runtime is far below the 256-bit program-counter bound. -/
theorem referenceBytecode_size_lt : referenceBytecode.size < 2 ^ 256 := by
  set_option maxRecDepth 20000 in
    decide

end Challenge.Bls12381G2Add.Reference.Proofs.Compilation
