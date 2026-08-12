import Challenge.Bls12381G1Add.Reference.Proofs.SourceOnCurveLawful

set_option warningAsError true

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

example (xHi xLo yHi yLo : U256) (yst : EvmState) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect onCurveFuns
      [("xHi", xHi), ("xLo", xLo), ("yHi", yHi), ("yLo", yLo)] yst
      (.call "\x0011" [.var "xHi", .var "xLo", .var "yHi", .var "yLo"])
    (.vals [onCurveResult yst xHi xLo yHi yLo]
      (onCurveFinalState yst xHi xLo yHi yLo)) :=
  step_onCurve xHi xLo yHi yLo yst

example (xHi xLo yHi yLo : U256) (yst : EvmState)
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
            (onCurveY yHi yLo))) :=
  onCurveResult_eq_one_iff yst xHi xLo yHi yLo hx hy

example (xHi xLo yHi yLo : U256) (yst : EvmState)
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
            (onCurveY yHi yLo))) :=
  onCurveResult_eq_zero_iff yst xHi xLo yHi yLo hx hy

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.onCurveBody_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms onCurveBody_eq

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.lookup_onCurve' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms lookup_onCurve

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.exec_onCurveStmt0' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms exec_onCurveStmt0

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.exec_onCurveStmt1' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms exec_onCurveStmt1

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.exec_onCurveStmt2' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms exec_onCurveStmt2

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.exec_onCurveStmt3' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms exec_onCurveStmt3

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.exec_onCurveStmt4' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms exec_onCurveStmt4

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.step_onCurveBody' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms step_onCurveBody

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.onCurveBodyResultEnv_yes' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms onCurveBodyResultEnv_yes

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.step_onCurve' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms step_onCurve

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.canonical_onCurveFour' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms canonical_onCurveFour

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.onCurveLhs_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms onCurveLhs_eq

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.onCurveRhs_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms onCurveRhs_eq

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.result_eq_one_iff_limbs_eq' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms result_eq_one_iff_limbs_eq

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.onCurveResult_zero_or_one' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms onCurveResult_zero_or_one

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.onCurveResult_eq_one_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms onCurveResult_eq_one_iff

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.onCurveResult_eq_zero_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms onCurveResult_eq_zero_iff

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
