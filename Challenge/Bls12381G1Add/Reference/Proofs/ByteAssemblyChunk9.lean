import Challenge.Bls12381G1Add.Reference.Proofs.ByteAssemblyCore

set_option warningAsError true

namespace Challenge.Bls12381G1Add.Reference.Proofs.Compilation

set_option maxRecDepth 20000 in
theorem referenceInstructionBytesChunk9 :
    referenceInstructionBytesChunk 9 = referenceFrozenBytesChunk 9 := by
  with_unfolding_all decide

end Challenge.Bls12381G1Add.Reference.Proofs.Compilation

