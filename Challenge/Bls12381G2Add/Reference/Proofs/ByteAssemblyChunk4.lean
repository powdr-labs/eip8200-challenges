import Challenge.Bls12381G2Add.Reference.Proofs.ByteAssemblyCore

set_option warningAsError true

namespace Challenge.Bls12381G2Add.Reference.Proofs.Compilation

set_option maxRecDepth 30000 in
theorem referenceInstructionBytesChunk4 :
    referenceInstructionBytesChunk 4 = referenceFrozenBytesChunk 4 := by
  with_unfolding_all decide

end Challenge.Bls12381G2Add.Reference.Proofs.Compilation

