import Challenge.Bls12381G1Msm.Reference.Proofs.ByteAssemblyCore

set_option warningAsError true

namespace Challenge.Bls12381G1Msm.Reference.Proofs.Compilation

set_option maxRecDepth 50000 in
theorem referenceInstructionBytesChunk2 :
    referenceInstructionBytesChunk 2 = referenceFrozenBytesChunk 2 := by
  with_unfolding_all decide

end Challenge.Bls12381G1Msm.Reference.Proofs.Compilation
