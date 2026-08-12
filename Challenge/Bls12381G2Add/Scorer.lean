import Challenge.Bls12381.Scorer
import Challenge.Bls12381.Reference
import Challenge.Bls12381.Vectors
import Challenge.Bls12381G2Add.Spec
import Challenge.Bls12381G2Add.Reference

set_option warningAsError true

namespace Challenge.Bls12381G2Add.Scorer

def config : Challenge.Bls12381.Scorer.Config :=
  { spec := Challenge.Bls12381G2Add.spec
    initialState := Challenge.Bls12381G2Add.initialState }

def vectors : List Challenge.Bls12381.Scorer.Vector :=
  [ { label := "empty (invalid)", input := .empty }
  , { label := "short (invalid)", input := Challenge.Bls12381.Scorer.zeros 511 }
  , { label := "infinity + infinity", input := Challenge.Bls12381.Scorer.zeros 512 }
  , { label := "long (invalid)", input := Challenge.Bls12381.Scorer.zeros 513 }
  , { label := Challenge.Bls12381.Vectors.g2Add.label
      input := Challenge.Bls12381.Vectors.g2Add.input }
  , { label := Challenge.Bls12381.Vectors.g2AddNonSubgroup.label
      input := Challenge.Bls12381.Vectors.g2AddNonSubgroup.input } ]

/-- Unverified upstream Solidity runtime exposed as a reproducible scorer baseline. -/
def baselineArtifact : Challenge.Bls12381.Reference.BaselineArtifact :=
  Challenge.Bls12381.Reference.g2Add

def scoreBaseline (vector : Challenge.Bls12381.Scorer.Vector) :
    Challenge.Bls12381.Scorer.Outcome :=
  Challenge.Bls12381.Scorer.score config baselineArtifact.runtimeBytecode vector.input

/-- Execute and measure the frozen runtime certified by
`Reference.Proofs.FinalCorrectness.reference_correct`. -/
def scoreReference (vector : Challenge.Bls12381.Scorer.Vector) :
    Challenge.Bls12381.Scorer.Outcome :=
  Challenge.Bls12381.Scorer.score config referenceBytecode vector.input

end Challenge.Bls12381G2Add.Scorer
