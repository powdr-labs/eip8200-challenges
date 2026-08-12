import Challenge.Bls12381G1Add.Reference.Proofs.SourceMainFiniteUnequalLawful

set_option warningAsError true

/-! # G1ADD unequal-x slope checks -/

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

example : mainFiniteUnequalBody =
    [mainFiniteUnequalStmt0, mainFiniteUnequalStmt1,
      mainFiniteUnequalStmt2, mainFiniteUnequalStmt3] :=
  mainFiniteUnequalBody_eq

example : mainFiniteUnequalStmt0 =
    .letDecl ["\x00108", "\x00109"]
      (some (.call "\x005"
        [.builtin .mload [.lit (.number 192)],
          .builtin .mload [.lit (.number 224)],
          .builtin .mload [.lit (.number 64)],
          .builtin .mload [.lit (.number 96)]])) := rfl

example : mainFiniteUnequalStmt1 =
    .letDecl ["\x00110", "\x00111"]
      (some (.call "\x005"
        [.builtin .mload [.lit (.number 128)],
          .builtin .mload [.lit (.number 160)],
          .builtin .mload [.lit (.number 0)],
          .builtin .mload [.lit (.number 32)]])) := rfl

example : mainFiniteUnequalStmt2 =
    .letDecl ["\x00112", "\x00113"]
      (some (.call "\x0010" [.var "\x00110", .var "\x00111"])) := rfl

example : mainFiniteUnequalStmt3 =
    .assign ["\x0098", "\x0099"]
      (.call "\x009"
        [.var "\x00108", .var "\x00109",
          .var "\x00112", .var "\x00113"]) := rfl

example (yst : EvmState) (hxeq : mainFiniteXEqValue yst = 0)
    (hx1 : Challenge.Bls12381.ProofSupport.Fp.Canonical
      (mainFiniteUnequalX1 yst))
    (hx2 : Challenge.Bls12381.ProofSupport.Fp.Canonical
      (mainFiniteUnequalX2 yst)) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect mainFuns
      (mainFiniteEnv yst) (mainFiniteXEqArgsState yst)
      mainFiniteUnequalStmt (mainFiniteUnequalResultEnv yst)
      (mainFiniteUnequalFinalState yst) .normal :=
  step_mainFiniteUnequal_canonical yst hxeq hx1 hx2

example (yst : EvmState)
    (hx1 : Challenge.Bls12381.ProofSupport.Fp.Canonical
      (mainFiniteUnequalX1 yst))
    (hy1 : Challenge.Bls12381.ProofSupport.Fp.Canonical
      (mainFiniteUnequalY1 yst))
    (hx2 : Challenge.Bls12381.ProofSupport.Fp.Canonical
      (mainFiniteUnequalX2 yst))
    (hy2 : Challenge.Bls12381.ProofSupport.Fp.Canonical
      (mainFiniteUnequalY2 yst)) :
    Challenge.Bls12381.ProofSupport.Fp.Canonical
      (mainFiniteUnequalLambda yst) :=
  canonical_mainFiniteUnequalLambda yst hx1 hy1 hx2 hy2

example (yst : EvmState)
    (hx1 : Challenge.Bls12381.ProofSupport.Fp.Canonical
      (mainFiniteUnequalX1 yst))
    (hy1 : Challenge.Bls12381.ProofSupport.Fp.Canonical
      (mainFiniteUnequalY1 yst))
    (hx2 : Challenge.Bls12381.ProofSupport.Fp.Canonical
      (mainFiniteUnequalX2 yst))
    (hy2 : Challenge.Bls12381.ProofSupport.Fp.Canonical
      (mainFiniteUnequalY2 yst))
    (hne : Challenge.Bls12381.ProofSupport.PrimeField.finEquiv
        (Challenge.Bls12381.ProofSupport.Fp.toField
          (mainFiniteUnequalX1 yst)) ≠
      Challenge.Bls12381.ProofSupport.PrimeField.finEquiv
        (Challenge.Bls12381.ProofSupport.Fp.toField
          (mainFiniteUnequalX2 yst))) :
    Challenge.Bls12381.ProofSupport.PrimeField.finEquiv
        (Challenge.Bls12381.ProofSupport.Fp.toField
          (mainFiniteUnequalLambda yst)) =
      (Challenge.Bls12381.ProofSupport.PrimeField.finEquiv
          (Challenge.Bls12381.ProofSupport.Fp.toField
            (mainFiniteUnequalY2 yst)) -
        Challenge.Bls12381.ProofSupport.PrimeField.finEquiv
          (Challenge.Bls12381.ProofSupport.Fp.toField
            (mainFiniteUnequalY1 yst))) /
      (Challenge.Bls12381.ProofSupport.PrimeField.finEquiv
          (Challenge.Bls12381.ProofSupport.Fp.toField
            (mainFiniteUnequalX2 yst)) -
        Challenge.Bls12381.ProofSupport.PrimeField.finEquiv
          (Challenge.Bls12381.ProofSupport.Fp.toField
            (mainFiniteUnequalX1 yst))) :=
  mainFiniteUnequalLambda_toLawful yst hx1 hy1 hx2 hy2 hne

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.mainFiniteUnequalBody_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms mainFiniteUnequalBody_eq

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.step_mainFiniteUnequalBody' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms step_mainFiniteUnequalBody

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.step_mainFiniteUnequal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms step_mainFiniteUnequal

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.mainFiniteUnequalLambda_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms mainFiniteUnequalLambda_eq

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.canonical_mainFiniteUnequalLambda' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms canonical_mainFiniteUnequalLambda

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.mainFiniteUnequalLambda_toLawful' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms mainFiniteUnequalLambda_toLawful

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.step_mainFiniteUnequal_canonical' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms step_mainFiniteUnequal_canonical

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.mainFiniteXEqArgsState_loadWord' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms mainFiniteXEqArgsState_loadWord

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.mainFiniteUnequalConditionState_loadWord' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms mainFiniteUnequalConditionState_loadWord

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.mainFiniteUnequalNumeratorArgsState_loadWord' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms mainFiniteUnequalNumeratorArgsState_loadWord

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.mainFiniteUnequalDenominatorArgsState_loadWord' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms mainFiniteUnequalDenominatorArgsState_loadWord

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.eval_fpSubLoads' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms eval_fpSubLoads

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
