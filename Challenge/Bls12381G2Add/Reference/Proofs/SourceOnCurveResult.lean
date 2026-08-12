import Challenge.Bls12381G2Add.Reference.Proofs.SourceOnCurveExec
import Challenge.Bls12381.ProofSupport.G2Affine

set_option warningAsError true

/-! # Result-level boundary for frozen G2ADD `onCurve` -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics.EVM
open Challenge.Bls12381.ProofSupport

private def reprOfFp2Words (words : Fp2Words) : Fp2.Repr :=
  { c0 := fpWords words.c0Hi words.c0Lo
    c1 := fpWords words.c1Hi words.c1Lo }

private theorem fp2At_eq_reprOfFp2Words (yst : EvmState) (ptr : U256) :
    fp2At yst ptr = reprOfFp2Words (fp2WordsAt yst ptr) := by
  rfl

theorem fp2EqValue_eq_one_iff_repr (yst : EvmState) (a b : U256) :
    fp2EqValue yst a b = 1 ↔ fp2At yst a = fp2At yst b := by
  rw [fp2EqValue_eq_one_iff_words]
  constructor
  · intro h
    rw [fp2At_eq_reprOfFp2Words, fp2At_eq_reprOfFp2Words]
    exact congrArg reprOfFp2Words h
  · intro h
    rw [fp2At_eq_reprOfFp2Words, fp2At_eq_reprOfFp2Words] at h
    cases ha : fp2WordsAt yst a with
    | mk a0h a0l a1h a1l =>
      cases hb : fp2WordsAt yst b with
      | mk b0h b0l b1h b1l =>
        rw [ha, hb] at h
        simp only [reprOfFp2Words, fpWords] at h
        congr
        · exact YulEvmCompiler.conv_injective
            (congrArg (fun z : Fp2.Repr => z.c0.hi) h)
        · exact YulEvmCompiler.conv_injective
            (congrArg (fun z : Fp2.Repr => z.c0.lo) h)
        · exact YulEvmCompiler.conv_injective
            (congrArg (fun z : Fp2.Repr => z.c1.hi) h)
        · exact YulEvmCompiler.conv_injective
            (congrArg (fun z : Fp2.Repr => z.c1.lo) h)

/-- Once the staged arithmetic modules identify the two final memory values,
the word predicate is exactly lawful G2 curve membership.  This theorem keeps
the concrete source graph out of the algebraic endpoint. -/
theorem onCurveResult_eq_one_iff_of_lawful_outputs
    (yst : EvmState) (x y : U256)
    (hlhs : Fp2.toLawful
        (fp2At (onCurveStateAfterAdd yst x y) (BitVec.ofNat 256 2048)) =
      Fp2.toLawful (fp2At yst y) ^ 2)
    (hrhs : Fp2.toLawful
        (fp2At (onCurveStateAfterAdd yst x y) (BitVec.ofNat 256 2304)) =
      Fp2.toLawful (fp2At yst x) ^ 3 + G2Affine.curve.b)
    (hlhsCanonical : Fp2.Canonical
      (fp2At (onCurveStateAfterAdd yst x y) (BitVec.ofNat 256 2048)))
    (hrhsCanonical : Fp2.Canonical
      (fp2At (onCurveStateAfterAdd yst x y) (BitVec.ofNat 256 2304))) :
    onCurveResult yst x y = 1 ↔
      G2Affine.OnCurve (.affine
        (Fp2.toLawful (fp2At yst x)) (Fp2.toLawful (fp2At yst y))) := by
  rw [onCurveResult, fp2EqValue_eq_one_iff_repr]
  constructor
  · intro heq
    change Fp2.toLawful (fp2At yst y) ^ 2 =
      Fp2.toLawful (fp2At yst x) ^ 3 + G2Affine.curve.a *
        Fp2.toLawful (fp2At yst x) + G2Affine.curve.b
    rw [← hlhs, heq, hrhs]
    simp [G2Affine.curve]
  · intro hcurve
    apply Fp2.eq_of_lawful_eq hlhsCanonical hrhsCanonical
    rw [hlhs, hrhs]
    simpa [G2Affine.OnCurve, LawfulAffine.OnCurve, G2Affine.curve] using hcurve

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
