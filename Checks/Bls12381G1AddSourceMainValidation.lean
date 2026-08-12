import Challenge.Bls12381G1Add.Reference.Proofs.SourceMainPrefix

set_option warningAsError true

/-! # Frozen G1ADD main-validation checks -/

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

example : mainPointValidationPrefix =
    [mainInf1Stmt, mainInf2Stmt, mainCurve1Stmt, mainCurve2Stmt] := rfl

example (yst : EvmState) (hcurve1 : mainCurve1ConditionValue yst = 0)
    (hcurve2 : mainCurve2ConditionValue yst = 0) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect mainFuns
      [] (mainAfterCanonicalReads yst) mainPointValidationPrefix
      (mainPointEnv yst) (mainValidatedState yst) .normal :=
  step_mainPointValidation_success yst hcurve1 hcurve2

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpMulFinalState_readBytes_before_scratch' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms fpMulFinalState_readBytes_before_scratch

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpMulFinalState_loadWord_before_scratch' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms fpMulFinalState_loadWord_before_scratch

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.exec_mainInf1' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms exec_mainInf1

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.exec_mainInf2' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms exec_mainInf2

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.step_curve1Call' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms step_curve1Call

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.step_curve2Call' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms step_curve2Call

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.step_curve1Condition' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms step_curve1Condition

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.step_curve2Condition' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms step_curve2Condition

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.step_mainCurve1_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms step_mainCurve1_success

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.step_mainCurve1_reject' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms step_mainCurve1_reject

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.step_mainCurve2_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms step_mainCurve2_success

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.step_mainCurve2_reject' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms step_mainCurve2_reject

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.mainCurve1ConditionValue_eq_zero_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms mainCurve1ConditionValue_eq_zero_iff

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.mainCurve2ConditionValue_eq_zero_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms mainCurve2ConditionValue_eq_zero_iff

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.step_mainDecodePrefix_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms step_mainDecodePrefix_success

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.step_mainDecodePrefix_padding_reject' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms step_mainDecodePrefix_padding_reject

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.step_mainDecodePrefix_canonical_reject' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms step_mainDecodePrefix_canonical_reject

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.step_mainPointValidation_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms step_mainPointValidation_success

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.step_mainPointValidation_curve1_reject' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms step_mainPointValidation_curve1_reject

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.step_mainPointValidation_curve2_reject' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms step_mainPointValidation_curve2_reject

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.mainPointValidation_success_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms mainPointValidation_success_iff

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
