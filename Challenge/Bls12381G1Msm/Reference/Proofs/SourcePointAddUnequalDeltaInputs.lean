import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalDelta
import Challenge.Bls12381G1Msm.Reference.Proofs.SourceVEnvRestore

set_option warningAsError true

/-! Declaration, variable reads, and memory loads for the generic delta subtraction. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def pointAddUnequalDeltaInitialEnv (ctx : PointAddUnequalDeltaContext) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  bindZeros Challenge.EvmProof.modexpExec.toDialect ["fc0_95", "fc0_96"] ++
    ctx.env

def pointAddUnequalDeltaLoVarEnv (ctx : PointAddUnequalDeltaContext) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  ("fc0_97", ctx.x3Lo) :: pointAddUnequalDeltaInitialEnv ctx

def pointAddUnequalDeltaHiVarEnv (ctx : PointAddUnequalDeltaContext) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  ("fc0_98", ctx.x3Hi) :: pointAddUnequalDeltaLoVarEnv ctx

def pointAddUnequalDeltaLeftLoEnv (ctx : PointAddUnequalDeltaContext) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  ("fc0_99", pointAddUnequalDeltaLeftLo ctx) ::
    pointAddUnequalDeltaHiVarEnv ctx

def pointAddUnequalDeltaLeftHiEnv (ctx : PointAddUnequalDeltaContext) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  ("fc0_100", pointAddUnequalDeltaLeftHi ctx) ::
    pointAddUnequalDeltaLeftLoEnv ctx

theorem step_pointAddUnequalDeltaRawDeclGeneric
    (ctx : PointAddUnequalDeltaContext) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect
      ([] :: pointAddBodyFuns) ctx.env ctx.state
      pointAddUnequalDeltaRawDeclStmt
      (pointAddUnequalDeltaInitialEnv ctx) ctx.state .normal := by
  rw [pointAddUnequalDeltaRawDeclStmt_eq]
  simpa [pointAddUnequalDeltaInitialEnv] using
    (Step.letZero
      (D := Challenge.EvmProof.modexpExec.toDialect)
      (funs := [] :: pointAddBodyFuns) (V := ctx.env) (st := ctx.state)
      (vars := ["fc0_95", "fc0_96"]))

private theorem initialEnv_lo (ctx : PointAddUnequalDeltaContext) :
    VEnv.get (pointAddUnequalDeltaInitialEnv ctx) "\x00137" =
      some ctx.x3Lo := by
  rw [pointAddUnequalDeltaInitialEnv]
  rw [venv_get_append_of_names_ne _ _ _ (by simp [bindZeros])]
  exact ctx.env_lo

theorem step_pointAddUnequalDeltaLoVarGeneric
    (ctx : PointAddUnequalDeltaContext) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) (pointAddUnequalDeltaInitialEnv ctx)
      ctx.state pointAddUnequalDeltaRawStmt0
      (pointAddUnequalDeltaLoVarEnv ctx) ctx.state .normal := by
  rw [pointAddUnequalDeltaRawStmt0_eq]
  exact Step.letVal (Step.var (initialEnv_lo ctx)) rfl

private theorem loVarEnv_hi (ctx : PointAddUnequalDeltaContext) :
    VEnv.get (pointAddUnequalDeltaLoVarEnv ctx) "\x00136" =
      some ctx.x3Hi := by
  rw [pointAddUnequalDeltaLoVarEnv]
  rw [venv_get_cons_ne _ _ _ _ (by decide)]
  rw [pointAddUnequalDeltaInitialEnv]
  rw [venv_get_append_of_names_ne _ _ _ (by simp [bindZeros])]
  exact ctx.env_hi

theorem step_pointAddUnequalDeltaHiVarGeneric
    (ctx : PointAddUnequalDeltaContext) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) (pointAddUnequalDeltaLoVarEnv ctx)
      ctx.state pointAddUnequalDeltaRawStmt1
      (pointAddUnequalDeltaHiVarEnv ctx) ctx.state .normal := by
  rw [pointAddUnequalDeltaRawStmt1_eq]
  exact Step.letVal (Step.var (loVarEnv_hi ctx)) rfl

private theorem step_pointAddUnequalDeltaLeftLoExprGeneric {funs}
    (ctx : PointAddUnequalDeltaContext) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect funs
      (pointAddUnequalDeltaHiVarEnv ctx) ctx.state
      (.builtin .mload
        [.builtin .add
          [.builtin .mload [.lit (.number 1568)], .lit (.number 32)]])
      (.vals [pointAddUnequalDeltaLeftLo ctx]
        (pointAddUnequalDeltaState2 ctx)) := by
  simpa [pointAddUnequalDeltaLeftLo, pointAddUnequalDeltaPtr,
    pointAddUnequalDeltaState1, pointAddUnequalDeltaState2] using
    (step_nestedLoadAdd (funs := funs)
      (V := pointAddUnequalDeltaHiVarEnv ctx) ctx.state 1568 32)

theorem step_pointAddUnequalDeltaLeftLoGeneric
    (ctx : PointAddUnequalDeltaContext) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) (pointAddUnequalDeltaHiVarEnv ctx)
      ctx.state pointAddUnequalDeltaRawStmt2
      (pointAddUnequalDeltaLeftLoEnv ctx)
      (pointAddUnequalDeltaState2 ctx) .normal := by
  rw [pointAddUnequalDeltaRawStmt2_eq]
  exact Step.letVal (step_pointAddUnequalDeltaLeftLoExprGeneric ctx) rfl

@[simp] private theorem touchMemory_memory (yst : EvmState)
    (offset size : Nat) : (touchMemory yst offset size).memory = yst.memory := rfl

@[simp] private theorem deltaState2_memory (ctx : PointAddUnequalDeltaContext) :
    (pointAddUnequalDeltaState2 ctx).memory = ctx.state.memory := by
  simp [pointAddUnequalDeltaState2, pointAddUnequalDeltaState1]

private theorem step_pointAddUnequalDeltaLeftHiExprGeneric {funs}
    (ctx : PointAddUnequalDeltaContext) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect funs
      (pointAddUnequalDeltaLeftLoEnv ctx) (pointAddUnequalDeltaState2 ctx)
      (.builtin .mload [.builtin .mload [.lit (.number 1568)]])
      (.vals [pointAddUnequalDeltaLeftHi ctx]
        (pointAddUnequalDeltaRawState ctx)) := by
  simpa [pointAddUnequalDeltaLeftHi, pointAddUnequalDeltaPtr,
    pointAddUnequalDeltaState3, pointAddUnequalDeltaRawState] using
    (step_nestedLoad (funs := funs) (V := pointAddUnequalDeltaLeftLoEnv ctx)
      (pointAddUnequalDeltaState2 ctx) 1568)

theorem step_pointAddUnequalDeltaLeftHiGeneric
    (ctx : PointAddUnequalDeltaContext) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) (pointAddUnequalDeltaLeftLoEnv ctx)
      (pointAddUnequalDeltaState2 ctx) pointAddUnequalDeltaRawStmt3
      (pointAddUnequalDeltaLeftHiEnv ctx)
      (pointAddUnequalDeltaRawState ctx) .normal := by
  rw [pointAddUnequalDeltaRawStmt3_eq]
  exact Step.letVal (step_pointAddUnequalDeltaLeftHiExprGeneric ctx) rfl

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
