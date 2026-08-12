import Challenge.Bls12381.Scorer
import Challenge.Bls12381.Reference
import Challenge.Bls12381.Vectors
import Challenge.Bls12381MapFpToG1.Spec

set_option warningAsError true

namespace Challenge.Bls12381MapFpToG1.Scorer

def config : Challenge.Bls12381.Scorer.Config :=
  { spec := Challenge.Bls12381MapFpToG1.spec
    initialState := Challenge.Bls12381MapFpToG1.initialState }

def vectors : List Challenge.Bls12381.Scorer.Vector :=
  [ { label := "empty (invalid)", input := .empty }
  , { label := "one byte short", input := Challenge.Bls12381.Scorer.zeros 63 }
  , { label := "map zero", input := Challenge.Bls12381.Scorer.zeros 64 }
  , { label := "one byte long", input := Challenge.Bls12381.Scorer.zeros 65 }
  , { label := Challenge.Bls12381.Vectors.mapFpToG1.label
      input := Challenge.Bls12381.Vectors.mapFpToG1.input } ]

/-- Unverified upstream Solidity runtime exposed as a reproducible scorer baseline. -/
def baselineArtifact : Challenge.Bls12381.Reference.BaselineArtifact :=
  Challenge.Bls12381.Reference.mapFpToG1

def scoreBaseline (vector : Challenge.Bls12381.Scorer.Vector) :
    Challenge.Bls12381.Scorer.Outcome :=
  Challenge.Bls12381.Scorer.score config baselineArtifact.runtimeBytecode vector.input

end Challenge.Bls12381MapFpToG1.Scorer
