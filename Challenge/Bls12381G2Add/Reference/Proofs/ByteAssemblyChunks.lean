import Challenge.Bls12381G2Add.Reference.Proofs.ByteAssemblyChunk0
import Challenge.Bls12381G2Add.Reference.Proofs.ByteAssemblyChunk1
import Challenge.Bls12381G2Add.Reference.Proofs.ByteAssemblyChunk2
import Challenge.Bls12381G2Add.Reference.Proofs.ByteAssemblyChunk3
import Challenge.Bls12381G2Add.Reference.Proofs.ByteAssemblyChunk4
import Challenge.Bls12381G2Add.Reference.Proofs.ByteAssemblyChunk5
import Challenge.Bls12381G2Add.Reference.Proofs.ByteAssemblyChunk6
import Challenge.Bls12381G2Add.Reference.Proofs.ByteAssemblyChunk7
import Challenge.Bls12381G2Add.Reference.Proofs.ByteAssemblyChunk8
import Challenge.Bls12381G2Add.Reference.Proofs.ByteAssemblyChunk9
import Challenge.Bls12381G2Add.Reference.Proofs.ByteAssemblyChunk10
import Challenge.Bls12381G2Add.Reference.Proofs.ByteAssemblyChunk11
import Challenge.Bls12381G2Add.Reference.Proofs.ByteAssemblyChunk12
import Challenge.Bls12381G2Add.Reference.Proofs.ByteAssemblyChunk13
import Challenge.Bls12381G2Add.Reference.Proofs.ByteAssemblyChunk14
import Challenge.Bls12381G2Add.Reference.Proofs.ByteAssemblyChunk15
import Challenge.Bls12381G2Add.Reference.Proofs.ByteAssemblyChunk16
import Challenge.Bls12381G2Add.Reference.Proofs.ByteAssemblyChunk17

set_option warningAsError true

namespace Challenge.Bls12381G2Add.Reference.Proofs.Compilation

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
    referenceInstructionBytesChunk 10 = referenceFrozenBytesChunk 10 ∧
    referenceInstructionBytesChunk 11 = referenceFrozenBytesChunk 11 ∧
    referenceInstructionBytesChunk 12 = referenceFrozenBytesChunk 12 ∧
    referenceInstructionBytesChunk 13 = referenceFrozenBytesChunk 13 ∧
    referenceInstructionBytesChunk 14 = referenceFrozenBytesChunk 14 ∧
    referenceInstructionBytesChunk 15 = referenceFrozenBytesChunk 15 ∧
    referenceInstructionBytesChunk 16 = referenceFrozenBytesChunk 16 ∧
    referenceInstructionBytesChunk 17 = referenceFrozenBytesChunk 17 := by
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
    referenceInstructionBytesChunk10,
    referenceInstructionBytesChunk11,
    referenceInstructionBytesChunk12,
    referenceInstructionBytesChunk13,
    referenceInstructionBytesChunk14,
    referenceInstructionBytesChunk15,
    referenceInstructionBytesChunk16,
    referenceInstructionBytesChunk17⟩

end Challenge.Bls12381G2Add.Reference.Proofs.Compilation

