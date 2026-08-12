import Challenge.Bls12381.ProofSupport.Fp2Predicates
import Challenge.Bls12381.ProofSupport.Fp2Source
import Challenge.Bls12381.ProofSupport.Fp2SqrtConstants
import Challenge.Bls12381.ProofSupport.Fp2SqrtProgram
import Challenge.Bls12381.ProofSupport.FpSqrt

set_option warningAsError true

/-! # Direct interpretation of the source Fp2 square-root program -/

namespace Challenge.Bls12381.ProofSupport.Fp2

abbrev SqrtResult := SqrtProgram.Result Repr

def sqrtSourceOps : SqrtProgram.Ops Fp.Limbs Repr where
  c0 := Repr.c0
  c1 := Repr.c1
  zero := zero
  pair := mkRepr
  isZeroPair := isZeroSource
  isZeroCell := Fp.isZeroValue
  eqCell := Fp.eqCanonicalValue
  eqPair := eqSource
  add := Fp.addSource
  sub := Fp.subSource
  neg := Fp.negSource
  mul := Fp.mulCanonical
  square := Fp.squareCanonical
  sqrt := Fp.sqrtCanonical
  inv := Fp.invCanonical
  squarePair := sqrSource
  invTwo := invTwo

def sqrtSource (a : Repr) : SqrtResult :=
  SqrtProgram.run sqrtSourceOps a

end Challenge.Bls12381.ProofSupport.Fp2
