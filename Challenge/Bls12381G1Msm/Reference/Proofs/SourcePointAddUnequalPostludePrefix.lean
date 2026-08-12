import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalPostlude
import Challenge.Bls12381G1Msm.Reference.Proofs.SourceAssignVar
import Challenge.Bls12381G1Msm.Reference.Proofs.SourceVEnvRestore

set_option warningAsError true

/-! Relational environment setup and output-pointer load for the doubling postlude. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

theorem step_pointAddUnequalPostStmt0Generic (ctx : PointAddUnequalPostContext) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      ctx.env ctx.state pointAddUnequalPostStmt0 ctx.env ctx.state .normal := by
  rw [pointAddUnequalPostStmt0_eq]
  simpa [bindZeros] using
    (Step.letZero (D := Challenge.EvmProof.modexpExec.toDialect)
      (funs := pointAddBodyFuns) (V := ctx.env) (st := ctx.state)
      (vars := []))

theorem step_pointAddUnequalPostStmt1Generic (ctx : PointAddUnequalPostContext) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      ctx.env ctx.state pointAddUnequalPostStmt1
      (pointAddUnequalPostEnv1 ctx) ctx.state .normal := by
  rw [pointAddUnequalPostStmt1_eq, pointAddUnequalPostEnv1]
  exact step_assignVar ctx.env_xLo

private theorem postEnv1_xHi (ctx : PointAddUnequalPostContext) :
    VEnv.get (pointAddUnequalPostEnv1 ctx) "\x00136" = some ctx.xHi := by
  rw [pointAddUnequalPostEnv1, venv_get_set_ne _ _ _ _ (by decide)]
  exact ctx.env_xHi

theorem step_pointAddUnequalPostStmt2Generic (ctx : PointAddUnequalPostContext) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddUnequalPostEnv1 ctx) ctx.state pointAddUnequalPostStmt2
      (pointAddUnequalPostEnv2 ctx) ctx.state .normal := by
  rw [pointAddUnequalPostStmt2_eq, pointAddUnequalPostEnv2]
  exact step_assignVar (postEnv1_xHi ctx)

private theorem step_pointAddUnequalPostLoadExpr {funs}
    (ctx : PointAddUnequalPostContext) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect funs
      (pointAddUnequalPostEnv2 ctx) ctx.state
      (.builtin .mload [.lit (.number 1536)])
      (.vals [pointAddUnequalPostOut ctx]
        (pointAddUnequalPostLoadState ctx)) := by
  have hlit : EvalExpr Challenge.EvmProof.modexpExec.toDialect funs
      (pointAddUnequalPostEnv2 ctx) ctx.state (.lit (.number 1536))
      (.vals [BitVec.ofNat 256 1536] ctx.state) := Step.lit
  have hargs : EvalArgs Challenge.EvmProof.modexpExec.toDialect funs
      (pointAddUnequalPostEnv2 ctx) ctx.state [.lit (.number 1536)]
      (.vals [BitVec.ofNat 256 1536] ctx.state) :=
    Step.argsCons Step.argsNil hlit
  have hload : EvalExpr Challenge.EvmProof.modexpExec.toDialect funs
      (pointAddUnequalPostEnv2 ctx) ctx.state
      (.builtin .mload [.lit (.number 1536)])
      (.vals [loadWord ctx.state.memory 1536]
        (touchMemory ctx.state 1536 32)) := Step.builtinOk hargs rfl
  simpa [pointAddUnequalPostOut, pointAddUnequalPostLoadState] using hload

theorem step_pointAddUnequalPostStmt3Generic (ctx : PointAddUnequalPostContext) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddUnequalPostEnv2 ctx) ctx.state pointAddUnequalPostStmt3
      (pointAddUnequalPostEnv ctx) (pointAddUnequalPostLoadState ctx) .normal := by
  rw [pointAddUnequalPostStmt3_eq, pointAddUnequalPostEnv]
  exact Step.assignVal (step_pointAddUnequalPostLoadExpr ctx) rfl

theorem step_pointAddUnequalPostPrefixGeneric (ctx : PointAddUnequalPostContext) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      ctx.env ctx.state (pointAddUnequalPostlude.take 4)
      (pointAddUnequalPostEnv ctx) (pointAddUnequalPostLoadState ctx) .normal := by
  rw [show pointAddUnequalPostlude.take 4 =
    [pointAddUnequalPostStmt0, pointAddUnequalPostStmt1,
     pointAddUnequalPostStmt2, pointAddUnequalPostStmt3] by rfl]
  exact Step.seqCons (step_pointAddUnequalPostStmt0Generic ctx)
    (Step.seqCons (step_pointAddUnequalPostStmt1Generic ctx)
      (Step.seqCons (step_pointAddUnequalPostStmt2Generic ctx)
        (Step.seqCons (step_pointAddUnequalPostStmt3Generic ctx) Step.seqNil)))

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
