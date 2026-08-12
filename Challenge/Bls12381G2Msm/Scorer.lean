import Challenge.Bls12381.Scorer
import Challenge.Bls12381.Reference
import Challenge.Bls12381.Vectors
import Challenge.Bls12381G2Msm.Spec
import Challenge.Bls12381G2Msm.Reference

set_option warningAsError true

namespace Challenge.Bls12381G2Msm.Scorer

def config : Challenge.Bls12381.Scorer.Config :=
  { spec := Challenge.Bls12381G2Msm.spec
    initialState := Challenge.Bls12381G2Msm.initialState }

def vectors : List Challenge.Bls12381.Scorer.Vector :=
  [ { label := "empty (invalid)", input := .empty }
  , { label := "one byte short", input := Challenge.Bls12381.Scorer.zeros 287 }
  , { label := "infinity times zero", input := Challenge.Bls12381.Scorer.zeros 288 }
  , { label := "two infinity terms", input := Challenge.Bls12381.Scorer.zeros 576 }
  , { label := Challenge.Bls12381.Vectors.g2Msm.label
      input := Challenge.Bls12381.Vectors.g2Msm.input }
  , { label := "reject non-subgroup g2 even with zero scalar"
      input := Challenge.Bls12381.Vectors.g2MsmNonSubgroup } ]

/-- Unverified upstream Solidity runtime exposed as a reproducible scorer baseline. -/
def baselineArtifact : Challenge.Bls12381.Reference.BaselineArtifact :=
  Challenge.Bls12381.Reference.g2Msm

def scoreBaseline (vector : Challenge.Bls12381.Scorer.Vector) :
    Challenge.Bls12381.Scorer.Outcome :=
  Challenge.Bls12381.Scorer.score config baselineArtifact.runtimeBytecode vector.input

/-- Execute and measure the frozen proof-friendly runtime. -/
def scoreReference (vector : Challenge.Bls12381.Scorer.Vector) :
    Challenge.Bls12381.Scorer.Outcome :=
  Challenge.Bls12381.Scorer.score config referenceBytecode vector.input

end Challenge.Bls12381G2Msm.Scorer
