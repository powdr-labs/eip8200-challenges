import Challenge.Bls12381G2Add.Reference.Proofs.ByteAssemblyCore

set_option warningAsError true

namespace Challenge.Bls12381G2Add.Reference.Proofs.Compilation

set_option maxRecDepth 30000 in
theorem referenceInstructionBytesChunk1 :
    referenceInstructionBytesChunk 1 = referenceFrozenBytesChunk 1 := by
  with_unfolding_all decide

end Challenge.Bls12381G2Add.Reference.Proofs.Compilation

