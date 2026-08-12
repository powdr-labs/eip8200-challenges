import Challenge.Bls12381.Scorer
import Challenge.Bls12381.Reference
import Challenge.Bls12381.Vectors
import Challenge.Bls12381MapFp2ToG2.Spec

set_option warningAsError true

namespace Challenge.Bls12381MapFp2ToG2.Scorer

def config : Challenge.Bls12381.Scorer.Config :=
  { spec := Challenge.Bls12381MapFp2ToG2.spec
    initialState := Challenge.Bls12381MapFp2ToG2.initialState }

def vectors : List Challenge.Bls12381.Scorer.Vector :=
  [ { label := "empty (invalid)", input := .empty }
  , { label := "one byte short", input := Challenge.Bls12381.Scorer.zeros 127 }
  , { label := "map zero", input := Challenge.Bls12381.Scorer.zeros 128 }
  , { label := "one byte long", input := Challenge.Bls12381.Scorer.zeros 129 }
  , { label := Challenge.Bls12381.Vectors.mapFp2ToG2.label
      input := Challenge.Bls12381.Vectors.mapFp2ToG2.input } ]

/-- Unverified upstream Solidity runtime exposed as a reproducible scorer baseline. -/
def baselineArtifact : Challenge.Bls12381.Reference.BaselineArtifact :=
  Challenge.Bls12381.Reference.mapFp2ToG2

def scoreBaseline (vector : Challenge.Bls12381.Scorer.Vector) :
    Challenge.Bls12381.Scorer.Outcome :=
  Challenge.Bls12381.Scorer.score config baselineArtifact.runtimeBytecode vector.input

end Challenge.Bls12381MapFp2ToG2.Scorer
