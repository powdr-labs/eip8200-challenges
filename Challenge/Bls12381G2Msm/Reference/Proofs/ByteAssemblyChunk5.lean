import Challenge.Bls12381G2Msm.Reference.Proofs.ByteAssemblyCore

set_option warningAsError true

namespace Challenge.Bls12381G2Msm.Reference.Proofs.Compilation

set_option maxRecDepth 30000 in
set_option maxHeartbeats 2000000 in
theorem referenceInstructionChunk5_bytes :
    referenceInstructionBytesChunk 5 = referenceFrozenBytesChunk 5 := by
  with_unfolding_all decide

end Challenge.Bls12381G2Msm.Reference.Proofs.Compilation
