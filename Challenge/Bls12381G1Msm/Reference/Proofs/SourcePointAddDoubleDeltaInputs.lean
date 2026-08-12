import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddDoubleDelta
import Challenge.Bls12381G1Msm.Reference.Proofs.SourceVEnvRestore

set_option warningAsError true

/-! Declaration, variable reads, and memory loads for the generic delta subtraction. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def pointAddDoubleDeltaInitialEnv (ctx : PointAddDoubleDeltaContext) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  bindZeros Challenge.EvmProof.modexpExec.toDialect ["fc0_42", "fc0_43"] ++
    ctx.env

def pointAddDoubleDeltaLoVarEnv (ctx : PointAddDoubleDeltaContext) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  ("fc0_44", ctx.x3Lo) :: pointAddDoubleDeltaInitialEnv ctx

def pointAddDoubleDeltaHiVarEnv (ctx : PointAddDoubleDeltaContext) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  ("fc0_45", ctx.x3Hi) :: pointAddDoubleDeltaLoVarEnv ctx

def pointAddDoubleDeltaLeftLoEnv (ctx : PointAddDoubleDeltaContext) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  ("fc0_46", pointAddDoubleDeltaLeftLo ctx) ::
    pointAddDoubleDeltaHiVarEnv ctx

def pointAddDoubleDeltaLeftHiEnv (ctx : PointAddDoubleDeltaContext) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  ("fc0_47", pointAddDoubleDeltaLeftHi ctx) ::
    pointAddDoubleDeltaLeftLoEnv ctx

theorem step_pointAddDoubleDeltaRawDeclGeneric
    (ctx : PointAddDoubleDeltaContext) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect
      ([] :: pointAddBodyFuns) ctx.env ctx.state
      pointAddDoubleDeltaRawDeclStmt
      (pointAddDoubleDeltaInitialEnv ctx) ctx.state .normal := by
  rw [pointAddDoubleDeltaRawDeclStmt_eq]
  simpa [pointAddDoubleDeltaInitialEnv] using
    (Step.letZero
      (D := Challenge.EvmProof.modexpExec.toDialect)
      (funs := [] :: pointAddBodyFuns) (V := ctx.env) (st := ctx.state)
      (vars := ["fc0_42", "fc0_43"]))

private theorem initialEnv_lo (ctx : PointAddDoubleDeltaContext) :
    VEnv.get (pointAddDoubleDeltaInitialEnv ctx) "\x00123" =
      some ctx.x3Lo := by
  rw [pointAddDoubleDeltaInitialEnv]
  rw [venv_get_append_of_names_ne _ _ _ (by simp [bindZeros])]
  exact ctx.env_lo

theorem step_pointAddDoubleDeltaLoVarGeneric
    (ctx : PointAddDoubleDeltaContext) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) (pointAddDoubleDeltaInitialEnv ctx)
      ctx.state pointAddDoubleDeltaRawStmt0
      (pointAddDoubleDeltaLoVarEnv ctx) ctx.state .normal := by
  rw [pointAddDoubleDeltaRawStmt0_eq]
  exact Step.letVal (Step.var (initialEnv_lo ctx)) rfl

private theorem loVarEnv_hi (ctx : PointAddDoubleDeltaContext) :
    VEnv.get (pointAddDoubleDeltaLoVarEnv ctx) "\x00122" =
      some ctx.x3Hi := by
  rw [pointAddDoubleDeltaLoVarEnv]
  rw [venv_get_cons_ne _ _ _ _ (by decide)]
  rw [pointAddDoubleDeltaInitialEnv]
  rw [venv_get_append_of_names_ne _ _ _ (by simp [bindZeros])]
  exact ctx.env_hi

theorem step_pointAddDoubleDeltaHiVarGeneric
    (ctx : PointAddDoubleDeltaContext) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) (pointAddDoubleDeltaLoVarEnv ctx)
      ctx.state pointAddDoubleDeltaRawStmt1
      (pointAddDoubleDeltaHiVarEnv ctx) ctx.state .normal := by
  rw [pointAddDoubleDeltaRawStmt1_eq]
  exact Step.letVal (Step.var (loVarEnv_hi ctx)) rfl

private theorem step_pointAddDoubleDeltaLeftLoExprGeneric {funs}
    (ctx : PointAddDoubleDeltaContext) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect funs
      (pointAddDoubleDeltaHiVarEnv ctx) ctx.state
      (.builtin .mload
        [.builtin .add
          [.builtin .mload [.lit (.number 1568)], .lit (.number 32)]])
      (.vals [pointAddDoubleDeltaLeftLo ctx]
        (pointAddDoubleDeltaState2 ctx)) := by
  simpa [pointAddDoubleDeltaLeftLo, pointAddDoubleDeltaPtr,
    pointAddDoubleDeltaState1, pointAddDoubleDeltaState2] using
    (step_nestedLoadAdd (funs := funs)
      (V := pointAddDoubleDeltaHiVarEnv ctx) ctx.state 1568 32)

theorem step_pointAddDoubleDeltaLeftLoGeneric
    (ctx : PointAddDoubleDeltaContext) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) (pointAddDoubleDeltaHiVarEnv ctx)
      ctx.state pointAddDoubleDeltaRawStmt2
      (pointAddDoubleDeltaLeftLoEnv ctx)
      (pointAddDoubleDeltaState2 ctx) .normal := by
  rw [pointAddDoubleDeltaRawStmt2_eq]
  exact Step.letVal (step_pointAddDoubleDeltaLeftLoExprGeneric ctx) rfl

@[simp] private theorem touchMemory_memory (yst : EvmState)
    (offset size : Nat) : (touchMemory yst offset size).memory = yst.memory := rfl

@[simp] private theorem deltaState2_memory (ctx : PointAddDoubleDeltaContext) :
    (pointAddDoubleDeltaState2 ctx).memory = ctx.state.memory := by
  simp [pointAddDoubleDeltaState2, pointAddDoubleDeltaState1]

private theorem step_pointAddDoubleDeltaLeftHiExprGeneric {funs}
    (ctx : PointAddDoubleDeltaContext) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect funs
      (pointAddDoubleDeltaLeftLoEnv ctx) (pointAddDoubleDeltaState2 ctx)
      (.builtin .mload [.builtin .mload [.lit (.number 1568)]])
      (.vals [pointAddDoubleDeltaLeftHi ctx]
        (pointAddDoubleDeltaRawState ctx)) := by
  simpa [pointAddDoubleDeltaLeftHi, pointAddDoubleDeltaPtr,
    pointAddDoubleDeltaState3, pointAddDoubleDeltaRawState] using
    (step_nestedLoad (funs := funs) (V := pointAddDoubleDeltaLeftLoEnv ctx)
      (pointAddDoubleDeltaState2 ctx) 1568)

theorem step_pointAddDoubleDeltaLeftHiGeneric
    (ctx : PointAddDoubleDeltaContext) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) (pointAddDoubleDeltaLeftLoEnv ctx)
      (pointAddDoubleDeltaState2 ctx) pointAddDoubleDeltaRawStmt3
      (pointAddDoubleDeltaLeftHiEnv ctx)
      (pointAddDoubleDeltaRawState ctx) .normal := by
  rw [pointAddDoubleDeltaRawStmt3_eq]
  exact Step.letVal (step_pointAddDoubleDeltaLeftHiExprGeneric ctx) rfl

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
