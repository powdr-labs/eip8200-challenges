import Challenge.Bls12381G2Add.Reference.Proofs.SourceSpecFiniteDouble
import Challenge.Bls12381G2Add.Reference.Proofs.SourceMainCurveLawful

set_option warningAsError true

/-! # Source/spec composition for exceptional finite G2ADD paths -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM
open Challenge.Bls12381.ProofSupport

theorem run_main_opposite_matches_add (yst : EvmState)
    (hsize : yst.env.calldata.length = 512)
    (hvalid : mainValidationValue yst ≠ 0)
    (hcurve1 : mainCurve1ConditionValue yst = 0)
    (hcurve2 : mainCurve2ConditionValue yst = 0)
    (hfirst : mainInf1 yst = 0) (hsecond : mainInf2 yst = 0)
    (hxeq : mainFiniteXEq1 yst ≠ 0)
    (hyeq : mainDoubleYEq yst = 0) :
    ∃ yst', Run Challenge.Bls12381G2Add.ProofSupport.Yul.localDialect
        Compilation.referenceCompiledBlock yst [] yst' .halt ∧
      yst'.halted = some (.ret,
        (Codec.encodeG2 (G2Affine.toWire
          (G2Affine.add (G2Affine.ofWire (sourcePoint1 yst))
            (G2Affine.ofWire (sourcePoint2 yst))))).toList) := by
  obtain ⟨hx1, hy1, hx2, hy2⟩ := mainValidated_canonical yst hvalid
  have hxEq := (mainFiniteXEq1_ne_zero_iff yst hx1 hx2).mp hxeq
  have hyne : Fp2.toLawful (fp2At (mainValidatedState yst) 128) ≠
      Fp2.toLawful (fp2At (mainValidatedState yst) 384) := by
    intro heq
    exact ((mainDoubleYEq_ne_zero_iff yst hy1 hy2).mpr heq) hyeq
  obtain ⟨⟨sx1, sy1, _⟩, sx2, sy2, _⟩ :=
    mainValidation_canonical yst hvalid
  have hon1 := (mainCurve1ConditionValue_eq_zero_iff yst sx1 sy1).mp hcurve1
    |>.resolve_left (fun hne => hne hfirst)
  have hon2 := (mainCurve2ConditionValue_eq_zero_iff yst sx2 sy2).mp hcurve2
    |>.resolve_left (fun hne => hne hsecond)
  have hxSource : Fp2.toLawful (sourceFp2 yst 0) =
      Fp2.toLawful (sourceFp2 yst 256) := by
    change Fp2.toLawful (fp2At (mainDecodedState yst) 0) =
      Fp2.toLawful (fp2At (mainDecodedState yst) 256)
    rw [← mainValidatedState_fp2At_source _ 0 (by decide) (by decide),
      ← mainValidatedState_fp2At_source _ 256 (by decide) (by decide)]
    exact hxEq
  have hyneSource : Fp2.toLawful (sourceFp2 yst 128) ≠
      Fp2.toLawful (sourceFp2 yst 384) := by
    intro heq
    apply hyne
    rw [mainValidatedState_fp2At_source _ 128 (by decide) (by decide),
      mainValidatedState_fp2At_source _ 384 (by decide) (by decide)]
    exact heq
  have hopposite : Fp2.toLawful (sourceFp2 yst 128) +
      Fp2.toLawful (sourceFp2 yst 384) = 0 := by
    have hsquares : Fp2.toLawful (sourceFp2 yst 128) ^ 2 =
        Fp2.toLawful (sourceFp2 yst 384) ^ 2 := by
      change Fp2.toLawful (sourceFp2 yst 128) ^ 2 =
          Fp2.toLawful (sourceFp2 yst 0) ^ 3 + G2Affine.curve.a *
            Fp2.toLawful (sourceFp2 yst 0) + G2Affine.curve.b at hon1
      change Fp2.toLawful (sourceFp2 yst 384) ^ 2 =
          Fp2.toLawful (sourceFp2 yst 256) ^ 3 + G2Affine.curve.a *
            Fp2.toLawful (sourceFp2 yst 256) + G2Affine.curve.b at hon2
      rw [← hxSource] at hon2
      exact hon1.trans hon2.symm
    have hprod : (Fp2.toLawful (sourceFp2 yst 128) -
        Fp2.toLawful (sourceFp2 yst 384)) *
        (Fp2.toLawful (sourceFp2 yst 128) +
          Fp2.toLawful (sourceFp2 yst 384)) = 0 := by
      calc
        _ = Fp2.toLawful (sourceFp2 yst 128) ^ 2 -
            Fp2.toLawful (sourceFp2 yst 384) ^ 2 := by ring
        _ = 0 := by rw [hsquares, sub_self]
    exact (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hyneSource)
  have hrun := run_main_opposite yst hsize hvalid hcurve1 hcurve2
    hfirst hsecond hxeq hyeq
  refine ⟨mainFiniteClearReturnState (mainAfterDoubleYEq yst), hrun, ?_⟩
  have hout := mainFiniteDispatcher_opposite_returned_add
    (mainAfterDoubleYEq yst)
    (Fp2.toLawful (sourceFp2 yst 0))
    (Fp2.toLawful (sourceFp2 yst 128))
    (Fp2.toLawful (sourceFp2 yst 384)) hopposite
  have hp1 : G2Affine.ofWire (sourcePoint1 yst) = .affine
      (Fp2.toLawful (sourceFp2 yst 0))
      (Fp2.toLawful (sourceFp2 yst 128)) := by
    rw [sourcePoint1, if_pos hfirst]
    rfl
  have hp2 : G2Affine.ofWire (sourcePoint2 yst) = .affine
      (Fp2.toLawful (sourceFp2 yst 256))
      (Fp2.toLawful (sourceFp2 yst 384)) := by
    rw [sourcePoint2, if_pos hsecond]
    rfl
  rw [hp1, hp2]
  rw [hout, ← hxSource]

theorem run_main_zeroY_matches_add (yst : EvmState)
    (hsize : yst.env.calldata.length = 512)
    (hvalid : mainValidationValue yst ≠ 0)
    (hcurve1 : mainCurve1ConditionValue yst = 0)
    (hcurve2 : mainCurve2ConditionValue yst = 0)
    (hfirst : mainInf1 yst = 0) (hsecond : mainInf2 yst = 0)
    (hxeq : mainFiniteXEq1 yst ≠ 0)
    (hyeq : mainDoubleYEq yst ≠ 0)
    (hyzero : mainDoubleYZero yst ≠ 0) :
    ∃ yst', Run Challenge.Bls12381G2Add.ProofSupport.Yul.localDialect
        Compilation.referenceCompiledBlock yst [] yst' .halt ∧
      yst'.halted = some (.ret,
        (Codec.encodeG2 (G2Affine.toWire
          (G2Affine.add (G2Affine.ofWire (sourcePoint1 yst))
            (G2Affine.ofWire (sourcePoint2 yst))))).toList) := by
  obtain ⟨hx1, hy1, hx2, hy2⟩ := mainValidated_canonical yst hvalid
  have hxEq := (mainFiniteXEq1_ne_zero_iff yst hx1 hx2).mp hxeq
  have hyEq := (mainDoubleYEq_ne_zero_iff yst hy1 hy2).mp hyeq
  have hy0 := (mainDoubleYZero_ne_zero_iff yst hy1).mp hyzero
  have hxSource : Fp2.toLawful (sourceFp2 yst 0) =
      Fp2.toLawful (sourceFp2 yst 256) := by
    change Fp2.toLawful (fp2At (mainDecodedState yst) 0) =
      Fp2.toLawful (fp2At (mainDecodedState yst) 256)
    rw [← mainValidatedState_fp2At_source _ 0 (by decide) (by decide),
      ← mainValidatedState_fp2At_source _ 256 (by decide) (by decide)]
    exact hxEq
  have hySource : Fp2.toLawful (sourceFp2 yst 128) = 0 := by
    change Fp2.toLawful (fp2At (mainDecodedState yst) 128) = 0
    rw [← mainValidatedState_fp2At_source _ 128 (by decide) (by decide)]
    exact hy0
  have hy2Source : Fp2.toLawful (sourceFp2 yst 384) = 0 := by
    change Fp2.toLawful (fp2At (mainDecodedState yst) 384) = 0
    rw [← mainValidatedState_fp2At_source _ 384 (by decide) (by decide),
      ← hyEq, hy0]
  have hrun := run_main_zeroY yst hsize hvalid hcurve1 hcurve2
    hfirst hsecond hxeq hyeq hyzero
  refine ⟨mainFiniteClearReturnState (mainAfterDoubleYZero yst), hrun, ?_⟩
  have hout := mainFiniteDispatcher_zeroY_returned_add
    (mainAfterDoubleYZero yst) (Fp2.toLawful (sourceFp2 yst 0))
  have hp1 : G2Affine.ofWire (sourcePoint1 yst) = .affine
      (Fp2.toLawful (sourceFp2 yst 0)) 0 := by
    rw [sourcePoint1, if_pos hfirst]
    change (.affine (Fp2.toLawful (sourceFp2 yst 0))
      (Fp2.toLawful (sourceFp2 yst 128)) : G2Affine.Point) = _
    rw [hySource]
  have hp2 : G2Affine.ofWire (sourcePoint2 yst) = .affine
      (Fp2.toLawful (sourceFp2 yst 0)) 0 := by
    rw [sourcePoint2, if_pos hsecond]
    change (.affine (Fp2.toLawful (sourceFp2 yst 256))
      (Fp2.toLawful (sourceFp2 yst 384)) : G2Affine.Point) = _
    rw [← hxSource, hy2Source]
  rw [hp1, hp2]
  rw [hout]

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
