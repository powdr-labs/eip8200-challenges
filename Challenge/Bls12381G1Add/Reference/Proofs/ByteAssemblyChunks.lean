import Challenge.Bls12381G1Add.Reference.Proofs.ByteAssemblyChunk0
import Challenge.Bls12381G1Add.Reference.Proofs.ByteAssemblyChunk1
import Challenge.Bls12381G1Add.Reference.Proofs.ByteAssemblyChunk2
import Challenge.Bls12381G1Add.Reference.Proofs.ByteAssemblyChunk3
import Challenge.Bls12381G1Add.Reference.Proofs.ByteAssemblyChunk4
import Challenge.Bls12381G1Add.Reference.Proofs.ByteAssemblyChunk5
import Challenge.Bls12381G1Add.Reference.Proofs.ByteAssemblyChunk6
import Challenge.Bls12381G1Add.Reference.Proofs.ByteAssemblyChunk7
import Challenge.Bls12381G1Add.Reference.Proofs.ByteAssemblyChunk8
import Challenge.Bls12381G1Add.Reference.Proofs.ByteAssemblyChunk9
import Challenge.Bls12381G1Add.Reference.Proofs.ByteAssemblyChunk10

set_option warningAsError true

/-! Aggregation boundary for bounded G1ADD byte-assembly checks. -/

namespace Challenge.Bls12381G1Add.Reference.Proofs.Compilation

theorem referenceInstructionByteChunkChecks :
    referenceInstructionBytesChunk 0 = referenceFrozenBytesChunk 0 ∧
    referenceInstructionBytesChunk 1 = referenceFrozenBytesChunk 1 ∧
    referenceInstructionBytesChunk 2 = referenceFrozenBytesChunk 2 ∧
    referenceInstructionBytesChunk 3 = referenceFrozenBytesChunk 3 ∧
    referenceInstructionBytesChunk 4 = referenceFrozenBytesChunk 4 ∧
    referenceInstructionBytesChunk 5 = referenceFrozenBytesChunk 5 ∧
    referenceInstructionBytesChunk 6 = referenceFrozenBytesChunk 6 ∧
    referenceInstructionBytesChunk 7 = referenceFrozenBytesChunk 7 ∧
    referenceInstructionBytesChunk 8 = referenceFrozenBytesChunk 8 ∧
    referenceInstructionBytesChunk 9 = referenceFrozenBytesChunk 9 ∧
    referenceInstructionBytesChunk 10 = referenceFrozenBytesChunk 10 := by
  exact ⟨referenceInstructionBytesChunk0,
    referenceInstructionBytesChunk1,
    referenceInstructionBytesChunk2,
    referenceInstructionBytesChunk3,
    referenceInstructionBytesChunk4,
    referenceInstructionBytesChunk5,
    referenceInstructionBytesChunk6,
    referenceInstructionBytesChunk7,
    referenceInstructionBytesChunk8,
    referenceInstructionBytesChunk9,
    referenceInstructionBytesChunk10⟩

end Challenge.Bls12381G1Add.Reference.Proofs.Compilation
