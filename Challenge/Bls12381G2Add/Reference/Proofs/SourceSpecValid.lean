import Challenge.Bls12381G2Add.Reference.Proofs.SourceSpecFiniteExceptional

set_option warningAsError true

/-! # Complete valid-input source semantics for G2ADD -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM
open Challenge.Bls12381.ProofSupport

theorem run_valid_matches_decoded (yst : EvmState)
    (hsize : yst.env.calldata.length = 512)
    (hvalid : mainValidationValue yst ≠ 0)
    (hcurve1 : mainCurve1ConditionValue yst = 0)
    (hcurve2 : mainCurve2ConditionValue yst = 0) :
    ∃ yst', Run Challenge.Bls12381G2Add.ProofSupport.Yul.localDialect
        Compilation.referenceCompiledBlock yst [] yst' .halt ∧
      yst'.halted = some (.ret,
        (Codec.encodeG2 (G2Affine.toWire
          (G2Affine.add (G2Affine.ofWire (sourcePoint1 yst))
            (G2Affine.ofWire (sourcePoint2 yst))))).toList) := by
  by_cases hfirst : mainInf1 yst = 0
  · by_cases hsecond : mainInf2 yst = 0
    · by_cases hxeq : mainFiniteXEq1 yst = 0
      · exact run_main_unequal_matches_add yst hsize hvalid hcurve1 hcurve2
          hfirst hsecond hxeq
      · by_cases hyeq : mainDoubleYEq yst = 0
        · exact run_main_opposite_matches_add yst hsize hvalid hcurve1 hcurve2
            hfirst hsecond hxeq hyeq
        · by_cases hyzero : mainDoubleYZero yst = 0
          · exact run_main_double_matches_add yst hsize hvalid hcurve1 hcurve2
              hfirst hsecond hxeq hyeq hyzero
          · exact run_main_zeroY_matches_add yst hsize hvalid hcurve1 hcurve2
              hfirst hsecond hxeq hyeq hyzero
    · have hrun := run_main_secondInfinity yst hsize hvalid hcurve1 hcurve2
          hfirst hsecond
      refine ⟨_, hrun, ?_⟩
      exact mainSecondInfinity_returned_add yst hvalid hfirst hsecond
  · by_cases hsecond : mainInf2 yst = 0
    · have hrun := run_main_firstInfinity yst hsize hvalid hcurve1 hcurve2
          hfirst hsecond
      refine ⟨_, hrun, ?_⟩
      exact mainFirstInfinity_returned_add yst hvalid hfirst hsecond
    · have hf : mainInf1 yst = 1 :=
        (mainInf1_zero_or_one yst).resolve_left hfirst
      have hs : mainInf2 yst = 1 :=
        (mainInf2_zero_or_one yst).resolve_left hsecond
      have hboth : mainBothInfinityValue yst ≠ 0 := by
        rw [mainBothInfinityValue, hf, hs]
        decide
      have hrun := run_main_bothInfinity yst hsize hvalid hcurve1 hcurve2 hboth
      refine ⟨_, hrun, ?_⟩
      exact mainBothInfinity_returned_add yst hfirst hsecond

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
