import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddDoublePostlude
import Challenge.Bls12381G1Msm.Reference.Proofs.SourceAssignVar
import Challenge.Bls12381G1Msm.Reference.Proofs.SourceVEnvRestore

set_option warningAsError true

/-! Relational environment setup and output-pointer load for the doubling postlude. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

theorem step_pointAddDoublePostStmt0Generic (ctx : PointAddDoublePostContext) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      ctx.env ctx.state pointAddDoublePostStmt0 ctx.env ctx.state .normal := by
  rw [pointAddDoublePostStmt0_eq]
  simpa [bindZeros] using
    (Step.letZero (D := Challenge.EvmProof.modexpExec.toDialect)
      (funs := pointAddBodyFuns) (V := ctx.env) (st := ctx.state)
      (vars := []))

theorem step_pointAddDoublePostStmt1Generic (ctx : PointAddDoublePostContext) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      ctx.env ctx.state pointAddDoublePostStmt1
      (pointAddDoublePostEnv1 ctx) ctx.state .normal := by
  rw [pointAddDoublePostStmt1_eq, pointAddDoublePostEnv1]
  exact step_assignVar ctx.env_xLo

private theorem postEnv1_xHi (ctx : PointAddDoublePostContext) :
    VEnv.get (pointAddDoublePostEnv1 ctx) "\x00122" = some ctx.xHi := by
  rw [pointAddDoublePostEnv1, venv_get_set_ne _ _ _ _ (by decide)]
  exact ctx.env_xHi

theorem step_pointAddDoublePostStmt2Generic (ctx : PointAddDoublePostContext) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddDoublePostEnv1 ctx) ctx.state pointAddDoublePostStmt2
      (pointAddDoublePostEnv2 ctx) ctx.state .normal := by
  rw [pointAddDoublePostStmt2_eq, pointAddDoublePostEnv2]
  exact step_assignVar (postEnv1_xHi ctx)

private theorem step_pointAddDoublePostLoadExpr {funs}
    (ctx : PointAddDoublePostContext) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect funs
      (pointAddDoublePostEnv2 ctx) ctx.state
      (.builtin .mload [.lit (.number 1536)])
      (.vals [pointAddDoublePostOut ctx]
        (pointAddDoublePostLoadState ctx)) := by
  have hlit : EvalExpr Challenge.EvmProof.modexpExec.toDialect funs
      (pointAddDoublePostEnv2 ctx) ctx.state (.lit (.number 1536))
      (.vals [BitVec.ofNat 256 1536] ctx.state) := Step.lit
  have hargs : EvalArgs Challenge.EvmProof.modexpExec.toDialect funs
      (pointAddDoublePostEnv2 ctx) ctx.state [.lit (.number 1536)]
      (.vals [BitVec.ofNat 256 1536] ctx.state) :=
    Step.argsCons Step.argsNil hlit
  have hload : EvalExpr Challenge.EvmProof.modexpExec.toDialect funs
      (pointAddDoublePostEnv2 ctx) ctx.state
      (.builtin .mload [.lit (.number 1536)])
      (.vals [loadWord ctx.state.memory 1536]
        (touchMemory ctx.state 1536 32)) := Step.builtinOk hargs rfl
  simpa [pointAddDoublePostOut, pointAddDoublePostLoadState] using hload

theorem step_pointAddDoublePostStmt3Generic (ctx : PointAddDoublePostContext) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddDoublePostEnv2 ctx) ctx.state pointAddDoublePostStmt3
      (pointAddDoublePostEnv ctx) (pointAddDoublePostLoadState ctx) .normal := by
  rw [pointAddDoublePostStmt3_eq, pointAddDoublePostEnv]
  exact Step.assignVal (step_pointAddDoublePostLoadExpr ctx) rfl

theorem step_pointAddDoublePostPrefixGeneric (ctx : PointAddDoublePostContext) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      ctx.env ctx.state (pointAddDoublePostlude.take 4)
      (pointAddDoublePostEnv ctx) (pointAddDoublePostLoadState ctx) .normal := by
  rw [show pointAddDoublePostlude.take 4 =
    [pointAddDoublePostStmt0, pointAddDoublePostStmt1,
     pointAddDoublePostStmt2, pointAddDoublePostStmt3] by rfl]
  exact Step.seqCons (step_pointAddDoublePostStmt0Generic ctx)
    (Step.seqCons (step_pointAddDoublePostStmt1Generic ctx)
      (Step.seqCons (step_pointAddDoublePostStmt2Generic ctx)
        (Step.seqCons (step_pointAddDoublePostStmt3Generic ctx) Step.seqNil)))

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
