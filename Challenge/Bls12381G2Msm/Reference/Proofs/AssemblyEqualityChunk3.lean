import Challenge.Bls12381G2Msm.Reference.Proofs.AssemblyChunk3

set_option warningAsError true

namespace Challenge.Bls12381G2Msm.Reference.Proofs.Compilation

set_option maxRecDepth 30000 in
set_option maxHeartbeats 2000000 in
theorem referenceAssemblyChunk3_eq :
    (referenceComputedOptimizedAssembly.drop 600).take 200 =
      frozenReferenceAssemblyChunk3 := by
  with_unfolding_all decide

end Challenge.Bls12381G2Msm.Reference.Proofs.Compilation
