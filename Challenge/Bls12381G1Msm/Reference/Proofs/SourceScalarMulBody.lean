import Challenge.Bls12381G1Msm.Reference.Proofs.SourceScalarMulLoop

set_option warningAsError true

/-! Complete scalar helper execution, parameterized by its concrete 256-bit trace. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

private theorem step_append_normal
    {funs V st pre Vmid stmid suffix Vend stend outcome}
    (hpre : ExecStmts Challenge.EvmProof.modexpExec.toDialect funs V st
      pre Vmid stmid .normal)
    (hsuffix : ExecStmts Challenge.EvmProof.modexpExec.toDialect funs Vmid stmid
      suffix Vend stend outcome) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect funs V st
      (pre ++ suffix) Vend stend outcome := by
  induction pre generalizing V st Vmid stmid with
  | nil =>
    cases hpre
    simpa using hsuffix
  | cons head rest ih =>
    cases hpre with
    | seqCons hhead htail =>
      simpa using Step.seqCons hhead (ih htail hsuffix)
    | seqStop _ hnot => exact (hnot rfl).elim

theorem step_scalarMulBodyStmts (yst : EvmState) (scalar point out : U256)
    {stend : EvmState}
    (htrace : ScalarMulTrace scalar point out 256 scalarMulInitialBit
      (scalarMulInitState yst out) stend) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect scalarMulBodyFuns
      (scalarMulInitialEnv scalar point out) yst scalarMulBody
      (scalarMulLoopEnv 0 scalar point out) stend .normal := by
  rw [scalarMulBody_eq_init_loop]
  exact step_append_normal (step_scalarMulInit yst scalar point out)
    (Step.seqCons (step_scalarMulFor scalar point out htrace) Step.seqNil)

theorem step_scalarMulBody (yst : EvmState) (scalar point out : U256)
    {stend : EvmState}
    (htrace : ScalarMulTrace scalar point out 256 scalarMulInitialBit
      (scalarMulInitState yst out) stend) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect sourceFuns
      (scalarMulInitialEnv scalar point out) yst (.block scalarMulBody)
      (scalarMulInitialEnv scalar point out) stend .normal := by
  have hblock : ExecStmt Challenge.EvmProof.modexpExec.toDialect sourceFuns
      (scalarMulInitialEnv scalar point out) yst (.block scalarMulBody)
      (restore (scalarMulInitialEnv scalar point out)
        (scalarMulLoopEnv 0 scalar point out)) stend .normal := by
    apply Step.block
    rw [hoist_scalarMulBody]
    exact step_scalarMulBodyStmts yst scalar point out htrace
  simpa [restore, scalarMulInitialEnv, scalarMulLoopEnv] using hblock

theorem step_scalarMul_of_args {funs V st argState args}
    (scalar point out : U256) {stend : EvmState}
    (hargs : EvalArgs Challenge.EvmProof.modexpExec.toDialect funs V st args
      (.vals [scalar, point, out] argState))
    (hlookup : lookupFun funs "\x0017" = some (scalarMulDecl, sourceFuns))
    (htrace : ScalarMulTrace scalar point out 256 scalarMulInitialBit
      (scalarMulInitState argState out) stend) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect funs V st
      (.call "\x0017" args) (.vals [] stend) := by
  have hcall := Step.callOk hargs hlookup rfl
    (step_scalarMulBody argState scalar point out htrace) (Or.inl rfl)
  simpa [scalarMulDecl] using hcall

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
