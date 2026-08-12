import Challenge.Bls12381G2Add.Reference.Proofs.SourceMainIdentityLawful
import Challenge.Bls12381G2Add.Reference.Proofs.SourceMainFinitePredicates
import Challenge.Bls12381G2Add.Reference.Proofs.SourceRun

set_option warningAsError true

/-! # Source/spec composition for the finite unequal-x G2ADD path -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM
open Challenge.Bls12381.ProofSupport

theorem mainValidated_canonical (yst : EvmState)
    (hvalid : mainValidationValue yst ≠ 0) :
    Fp2.Canonical (fp2At (mainValidatedState yst) 0) ∧
      Fp2.Canonical (fp2At (mainValidatedState yst) 128) ∧
      Fp2.Canonical (fp2At (mainValidatedState yst) 256) ∧
      Fp2.Canonical (fp2At (mainValidatedState yst) 384) := by
  obtain ⟨⟨hx1, hy1, _⟩, hx2, hy2, _⟩ :=
    mainValidation_canonical yst hvalid
  constructor
  · rw [mainValidatedState_fp2At_source _ _ (by decide) (by decide)]
    exact hx1
  constructor
  · rw [mainValidatedState_fp2At_source _ _ (by decide) (by decide)]
    exact hy1
  constructor
  · rw [mainValidatedState_fp2At_source _ _ (by decide) (by decide)]
    exact hx2
  · rw [mainValidatedState_fp2At_source _ _ (by decide) (by decide)]
    exact hy2

theorem run_main_unequal_matches_add (yst : EvmState)
    (hsize : yst.env.calldata.length = 512)
    (hvalid : mainValidationValue yst ≠ 0)
    (hcurve1 : mainCurve1ConditionValue yst = 0)
    (hcurve2 : mainCurve2ConditionValue yst = 0)
    (hfirst : mainInf1 yst = 0) (hsecond : mainInf2 yst = 0)
    (hxeq1 : mainFiniteXEq1 yst = 0) :
    ∃ yst', Run Challenge.Bls12381G2Add.ProofSupport.Yul.localDialect
        Compilation.referenceCompiledBlock yst [] yst' .halt ∧
      yst'.halted = some (.ret,
        (Codec.encodeG2 (G2Affine.toWire
          (G2Affine.add (G2Affine.ofWire (sourcePoint1 yst))
            (G2Affine.ofWire (sourcePoint2 yst))))).toList) := by
  obtain ⟨hx1, hy1, hx2, hy2⟩ := mainValidated_canonical yst hvalid
  have hxne : Fp2.toLawful (fp2At (mainValidatedState yst) 0) ≠
      Fp2.toLawful (fp2At (mainValidatedState yst) 256) := by
    intro heq
    exact ((mainFiniteXEq1_ne_zero_iff yst hx1 hx2).mpr heq) hxeq1
  have hxeq2 : mainFiniteXEq2 yst = 0 := by
    rcases fp2EqValue_zero_or_one (mainAfterFiniteXEq1 yst) 0 256 with hz | ho
    · exact hz
    · exfalso
      have hre := (fp2EqValue_eq_one_iff_repr
        (mainAfterFiniteXEq1 yst) 0 256).mp ho
      rw [mainAfterFiniteXEq1_fp2At, mainAfterFiniteXEq1_fp2At] at hre
      have hone : mainFiniteXEq1 yst = 1 := by
        unfold mainFiniteXEq1
        exact (fp2EqValue_eq_one_iff_repr (mainValidatedState yst) 0 256).mpr hre
      rw [hxeq1] at hone
      exact (by decide : (0 : U256) ≠ 1) hone
  have hinv := mainUnequalInvNorm_hi_lt yst hx1 hx2
  have hrun := run_main_unequal yst hsize hvalid hcurve1 hcurve2
    hfirst hsecond hxeq1 hxeq2 hinv
  refine ⟨_, hrun, ?_⟩
  have hout := mainFiniteDispatcher_unequal_returned_add yst
    hx1 hy1 hx2 hy2 hxne
  rw [mainValidatedState_fp2At_source _ 0 (by decide) (by decide),
    mainValidatedState_fp2At_source _ 128 (by decide) (by decide),
    mainValidatedState_fp2At_source _ 256 (by decide) (by decide),
    mainValidatedState_fp2At_source _ 384 (by decide) (by decide)] at hout
  simpa [sourcePoint1, sourcePoint2, hfirst, hsecond, sourceFp2,
    G2Affine.ofWire, Fp2.toLawful] using hout

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
