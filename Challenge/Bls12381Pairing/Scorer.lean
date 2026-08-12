import Challenge.Bls12381.Scorer
import Challenge.Bls12381.Reference
import Challenge.Bls12381.Vectors
import Challenge.Bls12381Pairing.Spec

set_option warningAsError true

namespace Challenge.Bls12381Pairing.Scorer

def config : Challenge.Bls12381.Scorer.Config :=
  { spec := Challenge.Bls12381Pairing.spec
    initialState := Challenge.Bls12381Pairing.initialState }

def vectors : List Challenge.Bls12381.Scorer.Vector :=
  [ { label := "empty (invalid)", input := .empty }
  , { label := "one byte short", input := Challenge.Bls12381.Scorer.zeros 383 }
  , { label := "infinity pair", input := Challenge.Bls12381.Scorer.zeros 384 }
  , { label := "two infinity pairs", input := Challenge.Bls12381.Scorer.zeros 768 }
  , { label := Challenge.Bls12381.Vectors.pairing.label
      input := Challenge.Bls12381.Vectors.pairing.input }
  , { label := "reject non-subgroup g1 pairing input"
      input := Challenge.Bls12381.Vectors.pairingG1NonSubgroup }
  , { label := "reject non-subgroup g2 pairing input"
      input := Challenge.Bls12381.Vectors.pairingG2NonSubgroup } ]

/-- Unverified upstream Solidity runtime exposed as a reproducible scorer baseline. -/
def baselineArtifact : Challenge.Bls12381.Reference.BaselineArtifact :=
  Challenge.Bls12381.Reference.pairing

def scoreBaseline (vector : Challenge.Bls12381.Scorer.Vector) :
    Challenge.Bls12381.Scorer.Outcome :=
  Challenge.Bls12381.Scorer.score config baselineArtifact.runtimeBytecode vector.input

end Challenge.Bls12381Pairing.Scorer
