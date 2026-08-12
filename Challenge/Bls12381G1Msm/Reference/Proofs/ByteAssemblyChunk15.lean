import Challenge.Bls12381G1Msm.Reference.Proofs.ByteAssemblyCore

set_option warningAsError true

namespace Challenge.Bls12381G1Msm.Reference.Proofs.Compilation

set_option maxRecDepth 50000 in
theorem referenceInstructionBytesChunk15 :
    referenceInstructionBytesChunk 15 = referenceFrozenBytesChunk 15 := by
  with_unfolding_all decide

end Challenge.Bls12381G1Msm.Reference.Proofs.Compilation
