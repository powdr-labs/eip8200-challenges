import Challenge.Bls12381G1Add.Reference.Proofs.SourceOnCurveRefinement

set_option warningAsError true

/-! # Lawful meaning of the frozen G1ADD `onCurve` result -/

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics.EVM

private abbrev LawfulFp :=
  Challenge.Bls12381.ProofSupport.PrimeField.LawfulFp

private theorem lawful_onCurveFour :
    (Challenge.Bls12381.ProofSupport.Fp.value onCurveFour : LawfulFp) = 4 := by
  change ((4 : Nat) : LawfulFp) = 4
  norm_num

private theorem lawful_square
    {a : Challenge.Bls12381.ProofSupport.Fp.Limbs}
    (ha : Challenge.Bls12381.ProofSupport.Fp.Canonical a) :
    (Challenge.Bls12381.ProofSupport.Fp.value
        (Challenge.Bls12381.ProofSupport.Fp.mulCanonical a a) : LawfulFp) =
      (Challenge.Bls12381.ProofSupport.Fp.value a : LawfulFp) *
        Challenge.Bls12381.ProofSupport.Fp.value a := by
  have h := congrArg Challenge.Bls12381.ProofSupport.PrimeField.finEquiv
    (Challenge.Bls12381.ProofSupport.Fp.toField_mulCanonical ha ha)
  simpa only [Challenge.Bls12381.ProofSupport.Fp.finEquiv_toField,
    map_mul] using h

private theorem lawful_cube
    {a : Challenge.Bls12381.ProofSupport.Fp.Limbs}
    (ha : Challenge.Bls12381.ProofSupport.Fp.Canonical a) :
    (Challenge.Bls12381.ProofSupport.Fp.value
        (Challenge.Bls12381.ProofSupport.Fp.mulCanonical
          (Challenge.Bls12381.ProofSupport.Fp.mulCanonical a a) a) :
        LawfulFp) =
      ((Challenge.Bls12381.ProofSupport.Fp.value a : LawfulFp) *
        Challenge.Bls12381.ProofSupport.Fp.value a) *
        Challenge.Bls12381.ProofSupport.Fp.value a := by
  have haa := Challenge.Bls12381.ProofSupport.Fp.canonical_mulCanonical ha ha
  have h := congrArg Challenge.Bls12381.ProofSupport.PrimeField.finEquiv
    (Challenge.Bls12381.ProofSupport.Fp.toField_mulCanonical haa ha)
  rw [Challenge.Bls12381.ProofSupport.Fp.finEquiv_toField,
    map_mul, Challenge.Bls12381.ProofSupport.Fp.finEquiv_toField] at h
  rw [lawful_square ha] at h
  exact h

private theorem lawful_rhs
    {a : Challenge.Bls12381.ProofSupport.Fp.Limbs}
    (ha : Challenge.Bls12381.ProofSupport.Fp.Canonical a) :
    (Challenge.Bls12381.ProofSupport.Fp.value
        (Challenge.Bls12381.ProofSupport.Fp.addSource
          (Challenge.Bls12381.ProofSupport.Fp.mulCanonical
            (Challenge.Bls12381.ProofSupport.Fp.mulCanonical a a) a)
          onCurveFour) : LawfulFp) =
      ((Challenge.Bls12381.ProofSupport.Fp.value a : LawfulFp) *
        Challenge.Bls12381.ProofSupport.Fp.value a) *
        Challenge.Bls12381.ProofSupport.Fp.value a + 4 := by
  have haa := Challenge.Bls12381.ProofSupport.Fp.canonical_mulCanonical ha ha
  have hcube := Challenge.Bls12381.ProofSupport.Fp.canonical_mulCanonical haa ha
  have h := congrArg Challenge.Bls12381.ProofSupport.PrimeField.finEquiv
    (Challenge.Bls12381.ProofSupport.Fp.toField_addSource
      hcube canonical_onCurveFour)
  rw [Challenge.Bls12381.ProofSupport.Fp.finEquiv_toField,
    map_add, Challenge.Bls12381.ProofSupport.Fp.finEquiv_toField,
    Challenge.Bls12381.ProofSupport.Fp.finEquiv_toField] at h
  rw [lawful_cube ha, lawful_onCurveFour] at h
  exact h

private theorem affine_onCurve_iff (x y : LawfulFp) :
    Challenge.Bls12381.ProofSupport.G1Affine.OnCurve (.affine x y) ↔
      y * y = (x * x) * x + 4 := by
  simp [Challenge.Bls12381.ProofSupport.G1Affine.OnCurve,
    Challenge.Bls12381.ProofSupport.LawfulAffine.OnCurve,
    Challenge.Bls12381.ProofSupport.G1Affine.curve,
    pow_succ, mul_assoc]

/-- The exact source result is true precisely for points satisfying the shared
lawful G1 equation `y² = x³ + 4`. -/
theorem onCurveResult_eq_one_iff (yst : EvmState)
    (xHi xLo yHi yLo : U256)
    (hx : Challenge.Bls12381.ProofSupport.Fp.Canonical
      (onCurveX xHi xLo))
    (hy : Challenge.Bls12381.ProofSupport.Fp.Canonical
      (onCurveY yHi yLo)) :
    onCurveResult yst xHi xLo yHi yLo = 1 ↔
      Challenge.Bls12381.ProofSupport.G1Affine.OnCurve
        (.affine
          (Challenge.Bls12381.ProofSupport.Fp.value
            (onCurveX xHi xLo))
          (Challenge.Bls12381.ProofSupport.Fp.value
            (onCurveY yHi yLo))) := by
  rw [result_eq_one_iff_limbs_eq,
    onCurveLhs_eq yst yHi yLo hy,
    onCurveRhs_eq yst xHi xLo yHi yLo hx]
  let x := onCurveX xHi xLo
  let y := onCurveY yHi yLo
  let lhs := Challenge.Bls12381.ProofSupport.Fp.mulCanonical y y
  let cube := Challenge.Bls12381.ProofSupport.Fp.mulCanonical
    (Challenge.Bls12381.ProofSupport.Fp.mulCanonical x x) x
  let rhs := Challenge.Bls12381.ProofSupport.Fp.addSource cube onCurveFour
  have hlhs := Challenge.Bls12381.ProofSupport.Fp.canonical_mulCanonical hy hy
  have hx2 := Challenge.Bls12381.ProofSupport.Fp.canonical_mulCanonical hx hx
  have hcube := Challenge.Bls12381.ProofSupport.Fp.canonical_mulCanonical hx2 hx
  have hrhs := Challenge.Bls12381.ProofSupport.Fp.canonical_addSource
    hcube canonical_onCurveFour
  rw [affine_onCurve_iff]
  constructor
  · intro heq
    change lhs = rhs at heq
    have hlaw := congrArg
      (fun a : Challenge.Bls12381.ProofSupport.Fp.Limbs =>
        (Challenge.Bls12381.ProofSupport.Fp.value a : LawfulFp)) heq
    rw [lawful_square hy, lawful_rhs hx] at hlaw
    exact hlaw
  · intro hcurve
    change lhs = rhs
    apply Challenge.Bls12381.ProofSupport.Fp.limbs_ext_of_value_eq
    apply Challenge.Bls12381.ProofSupport.Fp.value_eq_of_lawful_eq hlhs hrhs
    rw [lawful_square hy, lawful_rhs hx]
    exact hcurve

theorem onCurveResult_eq_zero_iff (yst : EvmState)
    (xHi xLo yHi yLo : U256)
    (hx : Challenge.Bls12381.ProofSupport.Fp.Canonical
      (onCurveX xHi xLo))
    (hy : Challenge.Bls12381.ProofSupport.Fp.Canonical
      (onCurveY yHi yLo)) :
    onCurveResult yst xHi xLo yHi yLo = 0 ↔
      ¬Challenge.Bls12381.ProofSupport.G1Affine.OnCurve
        (.affine
          (Challenge.Bls12381.ProofSupport.Fp.value
            (onCurveX xHi xLo))
          (Challenge.Bls12381.ProofSupport.Fp.value
            (onCurveY yHi yLo))) := by
  have hone := onCurveResult_eq_one_iff yst xHi xLo yHi yLo hx hy
  constructor
  · intro hzero hcurve
    have h := hone.mpr hcurve
    rw [hzero] at h
    have h' : (0 : U256) = (1 : U256) := h
    have hnat := congrArg (fun value : U256 => value.toNat) h'
    change 0 = 1 at hnat
    omega
  · intro hnot
    rcases onCurveResult_zero_or_one yst xHi xLo yHi yLo with hzero | hone'
    · exact hzero
    · exact False.elim (hnot (hone.mp hone'))

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
