import Challenge.Bls12381G1Add.Reference.Proofs.SourceMainFiniteDoubleLawful

set_option warningAsError true

/-! # G1ADD equal-point doubling-slope checks -/

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

example : mainFiniteDoubleBody =
    [mainFiniteDoubleStmt0, mainFiniteDoubleStmt1,
      mainFiniteDoubleStmt2, mainFiniteDoubleStmt3,
      mainFiniteDoubleStmt4, mainFiniteDoubleStmt5] :=
  mainFiniteDoubleBody_eq

example : mainFiniteDoubleStmt0 =
    .letDecl ["\x00100", "\x00101"]
      (some (.call "\x009"
        [.builtin .mload [.lit (.number 0)],
          .builtin .mload [.lit (.number 32)],
          .builtin .mload [.lit (.number 0)],
          .builtin .mload [.lit (.number 32)]])) := rfl

example : mainFiniteDoubleStmt1 =
    .letDecl ["\x00102", "\x00103"]
      (some (.call "\x004"
        [.var "\x00100", .var "\x00101",
          .var "\x00100", .var "\x00101"])) := rfl

example : mainFiniteDoubleStmt2 =
    .assign ["\x00102", "\x00103"]
      (.call "\x004"
        [.var "\x00102", .var "\x00103",
          .var "\x00100", .var "\x00101"]) := rfl

example : mainFiniteDoubleStmt3 =
    .letDecl ["\x00104", "\x00105"]
      (some (.call "\x004"
        [.builtin .mload [.lit (.number 64)],
          .builtin .mload [.lit (.number 96)],
          .builtin .mload [.lit (.number 64)],
          .builtin .mload [.lit (.number 96)]])) := rfl

example : mainFiniteDoubleStmt4 =
    .letDecl ["\x00106", "\x00107"]
      (some (.call "\x0010" [.var "\x00104", .var "\x00105"])) := rfl

example : mainFiniteDoubleStmt5 =
    .assign ["\x0098", "\x0099"]
      (.call "\x009"
        [.var "\x00102", .var "\x00103",
          .var "\x00106", .var "\x00107"]) := rfl

example (yst : EvmState)
    (hx : Challenge.Bls12381.ProofSupport.Fp.Canonical
      (mainFiniteDoubleX yst))
    (hy : Challenge.Bls12381.ProofSupport.Fp.Canonical
      (mainFiniteDoubleY yst)) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect ([] :: mainFuns)
      (mainFiniteEnv yst) (mainFiniteYZeroArgsState yst)
      mainFiniteDoubleBody (mainFiniteDoubleEnv6 yst)
      (mainFiniteDoubleFinalState yst) .normal :=
  step_mainFiniteDoubleBody_canonical yst hx hy

example (yst : EvmState)
    (hx : Challenge.Bls12381.ProofSupport.Fp.Canonical
      (mainFiniteDoubleX yst))
    (hy : Challenge.Bls12381.ProofSupport.Fp.Canonical
      (mainFiniteDoubleY yst)) :
    Challenge.Bls12381.ProofSupport.Fp.Canonical
      (mainFiniteDoubleLambda yst) :=
  canonical_mainFiniteDoubleLambda yst hx hy

example (yst : EvmState)
    (hx : Challenge.Bls12381.ProofSupport.Fp.Canonical
      (mainFiniteDoubleX yst))
    (hy : Challenge.Bls12381.ProofSupport.Fp.Canonical
      (mainFiniteDoubleY yst)) :
    Challenge.Bls12381.ProofSupport.PrimeField.finEquiv
        (Challenge.Bls12381.ProofSupport.Fp.toField
          (mainFiniteDoubleLambda yst)) =
      (3 * Challenge.Bls12381.ProofSupport.PrimeField.finEquiv
          (Challenge.Bls12381.ProofSupport.Fp.toField
            (mainFiniteDoubleX yst)) ^ 2) /
        (2 * Challenge.Bls12381.ProofSupport.PrimeField.finEquiv
          (Challenge.Bls12381.ProofSupport.Fp.toField
            (mainFiniteDoubleY yst))) :=
  mainFiniteDoubleLambda_toLawful yst hx hy

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.mainFiniteDoubleBody_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms mainFiniteDoubleBody_eq

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.step_mainFiniteDoubleBody' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms step_mainFiniteDoubleBody

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.mainFiniteDoubleLambda_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms mainFiniteDoubleLambda_eq

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.canonical_mainFiniteDoubleLambda' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms canonical_mainFiniteDoubleLambda

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.step_mainFiniteDoubleBody_canonical' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms step_mainFiniteDoubleBody_canonical

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.mainFiniteDoubleLambda_toLawful' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms mainFiniteDoubleLambda_toLawful

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
