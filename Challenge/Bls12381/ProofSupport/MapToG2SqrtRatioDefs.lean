import Challenge.Bls12381.ProofSupport.Fp2SqrtLawfulOps
import Challenge.Bls12381.ProofSupport.MapToG2

set_option warningAsError true

/-! # Definition-only MAP_FP2_TO_G2 square-root ratio boundary -/

namespace Challenge.Bls12381.ProofSupport.MapToG2

/-- Exact decoded-field schedule of the source Fp2 `sqrtRatio`: try
`sqrt(u / v)`, then unconditionally use `sqrt(Z * u / v)` after failure. -/
def sqrtRatioSource (u v : Field) : Bool × Field :=
  let quotient := u * v⁻¹
  let first := Fp2.SqrtProgram.run Fp2.lawfulSqrtOps quotient
  if first.exists_ then (true, first.root)
  else
    let second := Fp2.SqrtProgram.run Fp2.lawfulSqrtOps (isoZ * quotient)
    (false, second.root)

/-- Opaque source-SSWU stage boundary.  Keeping the schedule behind this
equation prevents downstream isogeny code from normalizing the complete Fp2
square-root program. -/
irreducible_def sourceSswu (lemma := sourceSswu_eq)
    (u : Field) : SswuResult :=
  sswuProjective sqrtRatioSource u

end Challenge.Bls12381.ProofSupport.MapToG2
