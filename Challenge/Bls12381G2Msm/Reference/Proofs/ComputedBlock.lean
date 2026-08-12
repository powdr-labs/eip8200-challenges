import Challenge.Bls12381G2Msm.Reference.Source

set_option warningAsError true

namespace Challenge.Bls12381G2Msm.Reference.Proofs.Compilation

open YulSemantics (Block)
open YulSemantics.EVM (Op)

/-- Parsed and normalized block, compiled once before chunk comparisons. -/
def computedReferenceBlock : Block Op :=
  Challenge.Bls12381G2Msm.referenceNormalizedBlock?.getD []

end Challenge.Bls12381G2Msm.Reference.Proofs.Compilation
