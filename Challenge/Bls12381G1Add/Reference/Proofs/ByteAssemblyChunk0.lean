import Challenge.Bls12381G1Add.Reference.Proofs.ByteAssemblyCore

set_option warningAsError true

namespace Challenge.Bls12381G1Add.Reference.Proofs.Compilation

set_option maxRecDepth 20000 in
theorem referenceInstructionBytesChunk0 :
    referenceInstructionBytesChunk 0 = referenceFrozenBytesChunk 0 := by
  with_unfolding_all decide

end Challenge.Bls12381G1Add.Reference.Proofs.Compilation
