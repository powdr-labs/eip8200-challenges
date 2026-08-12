import Challenge.Bls12381.Scorer
import Challenge.Bls12381.Reference
import Challenge.Bls12381.Vectors
import Challenge.Bls12381G1Msm.Spec

set_option warningAsError true

namespace Challenge.Bls12381G1Msm.Scorer

def config : Challenge.Bls12381.Scorer.Config :=
  { spec := Challenge.Bls12381G1Msm.spec
    initialState := Challenge.Bls12381G1Msm.initialState }

def vectors : List Challenge.Bls12381.Scorer.Vector :=
  [ { label := "empty (invalid)", input := .empty }
  , { label := "one byte short", input := Challenge.Bls12381.Scorer.zeros 159 }
  , { label := "infinity times zero", input := Challenge.Bls12381.Scorer.zeros 160 }
  , { label := "two infinity terms", input := Challenge.Bls12381.Scorer.zeros 320 }
  , { label := Challenge.Bls12381.Vectors.g1Msm.label
      input := Challenge.Bls12381.Vectors.g1Msm.input }
  , { label := "reject non-subgroup g1 even with zero scalar"
      input := Challenge.Bls12381.Vectors.g1MsmNonSubgroup } ]

/-- Unverified upstream Solidity runtime exposed as a reproducible scorer baseline. -/
def baselineArtifact : Challenge.Bls12381.Reference.BaselineArtifact :=
  Challenge.Bls12381.Reference.g1Msm

def scoreBaseline (vector : Challenge.Bls12381.Scorer.Vector) :
    Challenge.Bls12381.Scorer.Outcome :=
  Challenge.Bls12381.Scorer.score config baselineArtifact.runtimeBytecode vector.input

end Challenge.Bls12381G1Msm.Scorer
