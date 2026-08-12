import Challenge.Bls12381G2Add.Reference.Proofs.SourceSpecRejectCurve

set_option warningAsError true

/-! # Complete G2ADD source/spec boundary -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM
open Challenge.Bls12381.ProofSupport

/-- Complete exact source semantics for every EVM-sized calldata input. -/
theorem run_matches_spec (yst : EvmState) (input : ByteArray)
    (hcalldata : yst.env.calldata = input.toList)
    (hfit : input.size < 2 ^ 256) (_hhalted : yst.halted = none) :
    ∃ yst', Run Challenge.Bls12381G2Add.ProofSupport.Yul.localDialect
        Compilation.referenceCompiledBlock yst [] yst' .halt ∧
      match Challenge.Bls12381G2Add.spec input with
      | some output => yst'.halted = some (.ret, output.toList)
      | none => yst'.halted = some (.invalid, []) := by
  by_cases hsize : input.size = 512
  · have hlength : yst.env.calldata.length = 512 := by
      rw [hcalldata, YulEvmCompiler.ByteArray.toList_eq_data,
        Array.length_toList]
      exact hsize
    by_cases hvalid : mainValidationValue yst = 0
    · have hrun := run_main_validation_reject yst hlength hvalid
      have hnone := mainValidation_reject_decode_none yst input hcalldata
        hsize hvalid
      have hspec : Challenge.Bls12381G2Add.spec input = none := by
        apply Challenge.Bls12381G2Add.spec_eq_none_iff.mpr
        right
        exact hnone
      refine ⟨_, hrun, ?_⟩
      rw [hspec]
      rfl
    · by_cases hcurve1 : mainCurve1ConditionValue yst = 0
      · by_cases hcurve2 : mainCurve2ConditionValue yst = 0
        · obtain ⟨yst', hrun, hhalt⟩ := run_valid_matches_decoded yst
            hlength hvalid hcurve1 hcurve2
          have hleft := decodeG2_first_eq_sourcePoint yst input hcalldata
            hsize hvalid hcurve1
          have hright := decodeG2_second_eq_sourcePoint yst input hcalldata
            hsize hvalid hcurve2
          have hspec := Challenge.Bls12381G2Add.spec_success (by
              simpa [Challenge.Bls12381G2Add.inputBytes, Codec.g2Bytes]
                using hsize)
            hleft (by simpa [Codec.g2Bytes] using hright)
          refine ⟨yst', hrun, ?_⟩
          rw [hspec]
          exact hhalt
        · have hrun := run_main_curve2_reject yst hlength hvalid
              hcurve1 hcurve2
          have hnone := decodeG2_second_eq_none_of_curve yst input hcalldata
            hsize hvalid hcurve2
          have hspec : Challenge.Bls12381G2Add.spec input = none :=
            Challenge.Bls12381G2Add.spec_eq_none_iff.mpr
              (Or.inr (Or.inr (by simpa [Codec.g2Bytes] using hnone)))
          refine ⟨_, hrun, ?_⟩
          rw [hspec]
          rfl
      · have hrun := run_main_curve1_reject yst hlength hvalid hcurve1
        have hnone := decodeG2_first_eq_none_of_curve yst input hcalldata
          hsize hvalid hcurve1
        have hspec : Challenge.Bls12381G2Add.spec input = none :=
          Challenge.Bls12381G2Add.spec_eq_none_iff.mpr
            (Or.inr (Or.inl hnone))
        refine ⟨_, hrun, ?_⟩
        rw [hspec]
        rfl
  · have hlength : yst.env.calldata.length ≠ 512 := by
      simpa [hcalldata, YulEvmCompiler.ByteArray.toList_eq_data,
        Array.length_toList] using hsize
    have hfit' : yst.env.calldata.length < 2 ^ 256 := by
      simpa [hcalldata, YulEvmCompiler.ByteArray.toList_eq_data,
        Array.length_toList] using hfit
    have hrun := run_main_length_reject yst hfit' hlength
    have hspec := Challenge.Bls12381G2Add.spec_invalid_length (by
      simpa [Challenge.Bls12381G2Add.inputBytes, Codec.g2Bytes] using hsize)
    refine ⟨_, hrun, ?_⟩
    rw [hspec]
    rfl

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
