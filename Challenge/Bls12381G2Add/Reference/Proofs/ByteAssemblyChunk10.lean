import Challenge.Bls12381G2Add.Reference.Proofs.ByteAssemblyCore

set_option warningAsError true

namespace Challenge.Bls12381G2Add.Reference.Proofs.Compilation

set_option maxRecDepth 30000 in
theorem referenceInstructionBytesChunk10 :
    referenceInstructionBytesChunk 10 = referenceFrozenBytesChunk 10 := by
  with_unfolding_all decide

end Challenge.Bls12381G2Add.Reference.Proofs.Compilation

