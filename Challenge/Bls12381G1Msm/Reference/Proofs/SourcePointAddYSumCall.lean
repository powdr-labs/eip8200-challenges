import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddYSum

set_option warningAsError true

/-! Opaque composition of the equal-x Y loads with the frozen `fpAdd` helper. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

theorem step_pointAddYSum {funs V} (yst : EvmState) (out left right : U256)
    (hlookup : lookupFun funs "\x004" = some (fpAddDecl, sourceFuns)) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect funs V
      (pointAddXEqState yst out left right) pointAddYSumExpr
      (.vals
        [(fpAddResult
          (pointAddFiniteLeftYHi yst out left right)
          (pointAddFiniteLeftYLo yst out left right)
          (pointAddFiniteRightYHi yst out left right)
          (pointAddFiniteRightYLo yst out left right)).1,
         (fpAddResult
          (pointAddFiniteLeftYHi yst out left right)
          (pointAddFiniteLeftYLo yst out left right)
          (pointAddFiniteRightYHi yst out left right)
          (pointAddFiniteRightYLo yst out left right)).2]
        (pointAddYSumState yst out left right)) := by
  rw [pointAddYSumExpr_eq]
  exact step_fpAdd_of_args
    (pointAddFiniteLeftYHi yst out left right)
    (pointAddFiniteLeftYLo yst out left right)
    (pointAddFiniteRightYHi yst out left right)
    (pointAddFiniteRightYLo yst out left right)
    (step_pointAddYSumArgs yst out left right) hlookup

theorem step_pointAddYSumStmt_of_lookup {funs} (yst : EvmState)
    (out left right : U256)
    (hlookup : lookupFun funs "\x004" = some (fpAddDecl, sourceFuns)) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect funs
      (pointAddInitialEnv out left right) (pointAddXEqState yst out left right)
      pointAddYSumStmt (pointAddYSumEnv yst out left right)
      (pointAddYSumState yst out left right) .normal := by
  rw [pointAddYSumStmt_eq]
  change ExecStmt Challenge.EvmProof.modexpExec.toDialect funs
    (pointAddInitialEnv out left right) (pointAddXEqState yst out left right)
    _ (["\x00110", "\x00111"].zip
      [(fpAddResult
        (pointAddFiniteLeftYHi yst out left right)
        (pointAddFiniteLeftYLo yst out left right)
        (pointAddFiniteRightYHi yst out left right)
        (pointAddFiniteRightYLo yst out left right)).1,
       (fpAddResult
        (pointAddFiniteLeftYHi yst out left right)
        (pointAddFiniteLeftYLo yst out left right)
        (pointAddFiniteRightYHi yst out left right)
        (pointAddFiniteRightYLo yst out left right)).2] ++
      pointAddInitialEnv out left right)
    (pointAddYSumState yst out left right) .normal
  exact Step.letVal
    (step_pointAddYSum (funs := funs)
      (V := pointAddInitialEnv out left right) yst out left right hlookup) rfl

theorem step_pointAddYSumStmt (yst : EvmState) (out left right : U256) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddInitialEnv out left right) (pointAddXEqState yst out left right)
      pointAddYSumStmt (pointAddYSumEnv yst out left right)
      (pointAddYSumState yst out left right) .normal :=
  step_pointAddYSumStmt_of_lookup yst out left right (by rfl)

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
