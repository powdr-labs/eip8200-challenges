import Challenge.Bls12381G1Add.Reference.Proofs.SourceRun

set_option warningAsError true

/-! # Complete G1ADD frozen-source run checks -/

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

example : Challenge.EvmProof.YulRunContract
    Challenge.Bls12381G1Add.ProofSupport.Yul.localDialect
    Compilation.referenceCompiledBlock
    MainBothInfinityPre MainBothInfinityPost :=
  main_bothInfinity_yulContract

example : Challenge.EvmProof.YulRunContract
    Challenge.Bls12381G1Add.ProofSupport.Yul.localDialect
    Compilation.referenceCompiledBlock
    MainUnequalPre MainUnequalPost :=
  main_unequal_yulContract

example (yst : YulSemantics.EVM.EvmState)
    (hsize : yst.env.calldata.length = 256)
    (hpadding : mainPaddingValue yst = 0)
    (hcanonical : mainCanonicalValue yst ≠ 0)
    (hcurve1 : mainCurve1ConditionValue yst = 0)
    (hcurve2 : mainCurve2ConditionValue yst = 0)
    (hboth : mainBothInfinityValue yst ≠ 0) :
    ∃ final, MainBothInfinityContract yst final :=
  run_main_bothInfinity_contract yst hsize hpadding hcanonical hcurve1 hcurve2 hboth

example (yst : YulSemantics.EVM.EvmState)
    (hsize : yst.env.calldata.length = 256)
    (hpadding : mainPaddingValue yst = 0)
    (hcanonical : mainCanonicalValue yst ≠ 0)
    (hcurve1 : mainCurve1ConditionValue yst = 0)
    (hcurve2 : mainCurve2ConditionValue yst = 0)
    (hfirst : mainInf1 yst ≠ 0) (hsecond : mainInf2 yst = 0) :
    ∃ final, MainFirstInfinityContract yst final :=
  run_main_firstInfinity_contract yst hsize hpadding hcanonical hcurve1 hcurve2
    hfirst hsecond

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.run_main_bothInfinity_contract' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms run_main_bothInfinity_contract

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.main_bothInfinity_yulContract' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms main_bothInfinity_yulContract

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.main_unequal_yulContract' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms main_unequal_yulContract

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.run_main_firstInfinity_contract' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms run_main_firstInfinity_contract

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.run_main_double' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms run_main_double

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.run_main_unequal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms run_main_unequal

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.run_main_opposite' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms run_main_opposite

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.run_main_zeroY' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms run_main_zeroY

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.run_main_bothInfinity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms run_main_bothInfinity

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.run_main_firstInfinity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms run_main_firstInfinity

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.run_main_secondInfinity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms run_main_secondInfinity

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.run_main_padding_reject' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms run_main_padding_reject

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.run_main_canonical_reject' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms run_main_canonical_reject

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.run_main_curve1_reject' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms run_main_curve1_reject

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.run_main_curve2_reject' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms run_main_curve2_reject

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
