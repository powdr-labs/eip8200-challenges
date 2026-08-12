import Challenge.Bls12381G2Add.Reference.Proofs.SourceSpecFiniteUnequal

set_option warningAsError true

/-! # Source/spec composition for the finite G2ADD doubling path -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM
open Challenge.Bls12381.ProofSupport

theorem run_main_double_matches_add (yst : EvmState)
    (hsize : yst.env.calldata.length = 512)
    (hvalid : mainValidationValue yst ≠ 0)
    (hcurve1 : mainCurve1ConditionValue yst = 0)
    (hcurve2 : mainCurve2ConditionValue yst = 0)
    (hfirst : mainInf1 yst = 0) (hsecond : mainInf2 yst = 0)
    (hxeq1 : mainFiniteXEq1 yst ≠ 0)
    (hyeq : mainDoubleYEq yst ≠ 0)
    (hyzero : mainDoubleYZero yst = 0) :
    ∃ yst', Run Challenge.Bls12381G2Add.ProofSupport.Yul.localDialect
        Compilation.referenceCompiledBlock yst [] yst' .halt ∧
      yst'.halted = some (.ret,
        (Codec.encodeG2 (G2Affine.toWire
          (G2Affine.add (G2Affine.ofWire (sourcePoint1 yst))
            (G2Affine.ofWire (sourcePoint2 yst))))).toList) := by
  obtain ⟨hx1, hy1, hx2, hy2⟩ := mainValidated_canonical yst hvalid
  have hxEq := (mainFiniteXEq1_ne_zero_iff yst hx1 hx2).mp hxeq1
  have hyEq := (mainDoubleYEq_ne_zero_iff yst hy1 hy2).mp hyeq
  have hyne : Fp2.toLawful (fp2At (mainValidatedState yst) 128) ≠ 0 := by
    intro hy0
    exact ((mainDoubleYZero_ne_zero_iff yst hy1).mpr hy0) hyzero
  have hx1f : Fp2.Canonical (fp2At (mainDoubleFinalState yst) 0) := by
    rw [mainDoubleFinalState_fp2At_low _ _ (by decide) (by decide)]
    exact hx1
  have hx2f : Fp2.Canonical (fp2At (mainDoubleFinalState yst) 256) := by
    rw [mainDoubleFinalState_fp2At_low _ _ (by decide) (by decide)]
    exact hx2
  have heqf : Fp2.toLawful (fp2At (mainDoubleFinalState yst) 0) =
      Fp2.toLawful (fp2At (mainDoubleFinalState yst) 256) := by
    rw [mainDoubleFinalState_fp2At_low _ _ (by decide) (by decide),
      mainDoubleFinalState_fp2At_low _ _ (by decide) (by decide)]
    exact hxEq
  have hxeq2 := (mainDoubleXEq2_ne_zero_iff yst hx1f hx2f).mpr heqf
  have hinv := mainDoubleInvNorm_hi_lt yst hy1
  have hrun := run_main_double yst hsize hvalid hcurve1 hcurve2
    hfirst hsecond hxeq1 hyeq hyzero hinv hxeq2
  refine ⟨_, hrun, ?_⟩
  have hout := mainFiniteDispatcher_double_returned_add yst
    hx1 hy1 hx2 hyne hxEq.symm
  rw [mainValidatedState_fp2At_source _ 0 (by decide) (by decide),
    mainValidatedState_fp2At_source _ 128 (by decide) (by decide)] at hout
  have hxSource : Fp2.toLawful (sourceFp2 yst 0) =
      Fp2.toLawful (sourceFp2 yst 256) := by
    change Fp2.toLawful (fp2At (mainDecodedState yst) 0) =
      Fp2.toLawful (fp2At (mainDecodedState yst) 256)
    rw [← mainValidatedState_fp2At_source _ 0 (by decide) (by decide),
      ← mainValidatedState_fp2At_source _ 256 (by decide) (by decide)]
    exact hxEq
  have hySource : Fp2.toLawful (sourceFp2 yst 128) =
      Fp2.toLawful (sourceFp2 yst 384) := by
    change Fp2.toLawful (fp2At (mainDecodedState yst) 128) =
      Fp2.toLawful (fp2At (mainDecodedState yst) 384)
    rw [← mainValidatedState_fp2At_source _ 128 (by decide) (by decide),
      ← mainValidatedState_fp2At_source _ 384 (by decide) (by decide)]
    exact hyEq
  have hp2 : G2Affine.ofWire (sourcePoint2 yst) =
      G2Affine.ofWire (sourcePoint1 yst) := by
    rw [sourcePoint2, if_pos hsecond, sourcePoint1, if_pos hfirst]
    change (.affine (Fp2.toLawful (sourceFp2 yst 256))
      (Fp2.toLawful (sourceFp2 yst 384)) : G2Affine.Point) =
      .affine (Fp2.toLawful (sourceFp2 yst 0))
        (Fp2.toLawful (sourceFp2 yst 128))
    rw [← hxSource, ← hySource]
  rw [hp2]
  simpa [sourcePoint1, hfirst, sourceFp2, G2Affine.ofWire,
    Fp2.toLawful] using hout

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
