import Challenge.Bls12381G2Add.Reference.Proofs.SourceMainFiniteInputs
import Challenge.Bls12381G2Add.Reference.Proofs.SourceOnCurveResult
import Challenge.Bls12381G2Add.Reference.Proofs.SourcePointPredicatesRefinement
import Challenge.Bls12381.ProofSupport.Fp2Predicates

set_option warningAsError true

/-! # Lawful meaning of the frozen G2ADD finite-path predicates

The executable predicates are kept behind small Boolean-valued endpoints.
This prevents later branch proofs from reopening their four-word read graph.
-/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics.EVM
open Challenge.Bls12381.ProofSupport

/-- Equality of canonical source representations is exactly equality in the
lawful quadratic extension field. -/
theorem fp2EqValue_ne_zero_iff_lawful (yst : EvmState) (a b : U256)
    (ha : Fp2.Canonical (fp2At yst a))
    (hb : Fp2.Canonical (fp2At yst b)) :
    fp2EqValue yst a b ≠ 0 ↔
      Fp2.toLawful (fp2At yst a) = Fp2.toLawful (fp2At yst b) := by
  constructor
  · intro hne
    rcases fp2EqValue_zero_or_one yst a b with hzero | hone
    · exact (hne hzero).elim
    · exact congrArg Fp2.toLawful
        ((fp2EqValue_eq_one_iff_repr yst a b).mp hone)
  · intro heq hzero
    have hre : fp2At yst a = fp2At yst b :=
      Fp2.eq_of_lawful_eq ha hb heq
    have hone := (fp2EqValue_eq_one_iff_repr yst a b).mpr hre
    rw [hzero] at hone
    contradiction

private theorem fp2ZeroValue_eq_one_iff_repr (yst : EvmState) (ptr : U256) :
    fp2ZeroValue yst ptr = 1 ↔
      fp2At yst ptr = Challenge.Bls12381.ProofSupport.Fp2.zero := by
  rw [fp2ZeroValue_eq_one_iff_words,
    fp2WordsAt_eq_zero_iff_fp2At_eq_zero]

/-- The executable zero predicate on a canonical representation is exactly
zero in the lawful quadratic extension field. -/
theorem fp2ZeroValue_ne_zero_iff_lawful (yst : EvmState) (ptr : U256)
    (ha : Fp2.Canonical (fp2At yst ptr)) :
    fp2ZeroValue yst ptr ≠ 0 ↔ Fp2.toLawful (fp2At yst ptr) = 0 := by
  constructor
  · intro hne
    rcases fp2ZeroValue_zero_or_one yst ptr with hzero | hone
    · exact (hne hzero).elim
    · have hre := (fp2ZeroValue_eq_one_iff_repr yst ptr).mp hone
      rw [hre, Fp2.toLawful_zero_repr]
  · intro hzero hwordZero
    have hre : fp2At yst ptr = Challenge.Bls12381.ProofSupport.Fp2.zero :=
      Fp2.eq_zero_of_isZeroSource_true ((Fp2.isZeroSource_iff ha).mpr hzero)
    have hone := (fp2ZeroValue_eq_one_iff_repr yst ptr).mpr hre
    rw [hwordZero] at hone
    contradiction

theorem mainFiniteXEq1_ne_zero_iff (yst : EvmState)
    (hx1 : Fp2.Canonical (fp2At (mainValidatedState yst) 0))
    (hx2 : Fp2.Canonical (fp2At (mainValidatedState yst) 256)) :
    mainFiniteXEq1 yst ≠ 0 ↔
      Fp2.toLawful (fp2At (mainValidatedState yst) 0) =
        Fp2.toLawful (fp2At (mainValidatedState yst) 256) := by
  exact fp2EqValue_ne_zero_iff_lawful _ _ _ hx1 hx2

theorem mainFiniteXEq2_ne_zero_iff (yst : EvmState)
    (hx1 : Fp2.Canonical (fp2At (mainValidatedState yst) 0))
    (hx2 : Fp2.Canonical (fp2At (mainValidatedState yst) 256)) :
    mainFiniteXEq2 yst ≠ 0 ↔
      Fp2.toLawful (fp2At (mainValidatedState yst) 0) =
        Fp2.toLawful (fp2At (mainValidatedState yst) 256) := by
  have hx1' : Fp2.Canonical (fp2At (mainAfterFiniteXEq1 yst) 0) := by
    rw [mainAfterFiniteXEq1_fp2At]
    exact hx1
  have hx2' : Fp2.Canonical (fp2At (mainAfterFiniteXEq1 yst) 256) := by
    rw [mainAfterFiniteXEq1_fp2At]
    exact hx2
  rw [mainFiniteXEq2,
    fp2EqValue_ne_zero_iff_lawful _ _ _ hx1' hx2',
    mainAfterFiniteXEq1_fp2At, mainAfterFiniteXEq1_fp2At]

theorem mainDoubleYEq_ne_zero_iff (yst : EvmState)
    (hy1 : Fp2.Canonical (fp2At (mainValidatedState yst) 128))
    (hy2 : Fp2.Canonical (fp2At (mainValidatedState yst) 384)) :
    mainDoubleYEq yst ≠ 0 ↔
      Fp2.toLawful (fp2At (mainValidatedState yst) 128) =
        Fp2.toLawful (fp2At (mainValidatedState yst) 384) := by
  have hy1' : Fp2.Canonical (fp2At (mainAfterFiniteXEq1 yst) 128) := by
    rw [mainAfterFiniteXEq1_fp2At]
    exact hy1
  have hy2' : Fp2.Canonical (fp2At (mainAfterFiniteXEq1 yst) 384) := by
    rw [mainAfterFiniteXEq1_fp2At]
    exact hy2
  rw [mainDoubleYEq,
    fp2EqValue_ne_zero_iff_lawful _ _ _ hy1' hy2',
    mainAfterFiniteXEq1_fp2At, mainAfterFiniteXEq1_fp2At]

theorem mainDoubleYZero_ne_zero_iff (yst : EvmState)
    (hy1 : Fp2.Canonical (fp2At (mainValidatedState yst) 128)) :
    mainDoubleYZero yst ≠ 0 ↔
      Fp2.toLawful (fp2At (mainValidatedState yst) 128) = 0 := by
  have hy1' : Fp2.Canonical (fp2At (mainAfterDoubleYEq yst) 128) := by
    rw [mainAfterDoubleYEq_fp2At]
    exact hy1
  rw [mainDoubleYZero,
    fp2ZeroValue_ne_zero_iff_lawful _ _ hy1',
    mainAfterDoubleYEq_fp2At]

theorem mainDoubleXEq2_ne_zero_iff (yst : EvmState)
    (hx1 : Fp2.Canonical (fp2At (mainDoubleFinalState yst) 0))
    (hx2 : Fp2.Canonical (fp2At (mainDoubleFinalState yst) 256)) :
    mainDoubleXEq2 yst ≠ 0 ↔
      Fp2.toLawful (fp2At (mainDoubleFinalState yst) 0) =
        Fp2.toLawful (fp2At (mainDoubleFinalState yst) 256) := by
  exact fp2EqValue_ne_zero_iff_lawful _ _ _ hx1 hx2

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
