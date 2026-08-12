import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddDoubleYSub
import Challenge.Bls12381G1Msm.Reference.Proofs.SourceVEnvRestore

set_option warningAsError true

/-! Declaration, left-y loads, and input reads for the generic final y subtraction. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def pointAddDoubleYSubInitialEnv (ctx : PointAddDoubleYSubContext) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  bindZeros Challenge.EvmProof.modexpExec.toDialect ["fc0_49", "fc0_50"] ++
    ctx.env
def pointAddDoubleYSubLeftLoEnv (ctx : PointAddDoubleYSubContext) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  ("fc0_51", pointAddDoubleYSubLeftLo ctx) :: pointAddDoubleYSubInitialEnv ctx
def pointAddDoubleYSubLeftHiEnv (ctx : PointAddDoubleYSubContext) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  ("fc0_52", pointAddDoubleYSubLeftHi ctx) :: pointAddDoubleYSubLeftLoEnv ctx
def pointAddDoubleYSubLoVarEnv (ctx : PointAddDoubleYSubContext) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  ("fc0_53", ctx.inputLo) :: pointAddDoubleYSubLeftHiEnv ctx
def pointAddDoubleYSubHiVarEnv (ctx : PointAddDoubleYSubContext) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  ("fc0_54", ctx.inputHi) :: pointAddDoubleYSubLoVarEnv ctx

theorem step_pointAddDoubleYSubRawDeclGeneric (ctx : PointAddDoubleYSubContext) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect
      ([] :: pointAddBodyFuns) ctx.env ctx.state pointAddDoubleYSubRawDeclStmt
      (pointAddDoubleYSubInitialEnv ctx) ctx.state .normal := by
  rw [pointAddDoubleYSubRawDeclStmt_eq]
  simpa [pointAddDoubleYSubInitialEnv] using
    (Step.letZero (D := Challenge.EvmProof.modexpExec.toDialect)
      (funs := [] :: pointAddBodyFuns) (V := ctx.env) (st := ctx.state)
      (vars := ["fc0_49", "fc0_50"]))

private theorem step_leftLoExpr {funs} (ctx : PointAddDoubleYSubContext) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect funs
      (pointAddDoubleYSubInitialEnv ctx) ctx.state
      (.builtin .mload
        [.builtin .add
          [.builtin .mload [.lit (.number 1568)], .lit (.number 96)]])
      (.vals [pointAddDoubleYSubLeftLo ctx]
        (pointAddDoubleYSubState2 ctx)) := by
  simpa [pointAddDoubleYSubLeftLo, pointAddDoubleYSubPtr,
    pointAddDoubleYSubState1, pointAddDoubleYSubState2] using
    (step_nestedLoadAdd (funs := funs)
      (V := pointAddDoubleYSubInitialEnv ctx) ctx.state 1568 96)

theorem step_pointAddDoubleYSubLeftLoGeneric (ctx : PointAddDoubleYSubContext) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) (pointAddDoubleYSubInitialEnv ctx)
      ctx.state pointAddDoubleYSubRawStmt0 (pointAddDoubleYSubLeftLoEnv ctx)
      (pointAddDoubleYSubState2 ctx) .normal := by
  rw [pointAddDoubleYSubRawStmt0_eq]
  exact Step.letVal (step_leftLoExpr ctx) rfl

@[simp] private theorem touchMemory_memory (yst : EvmState)
    (offset size : Nat) : (touchMemory yst offset size).memory = yst.memory := rfl

@[simp] private theorem ySubState2_memory (ctx : PointAddDoubleYSubContext) :
    (pointAddDoubleYSubState2 ctx).memory = ctx.state.memory := by
  simp [pointAddDoubleYSubState2, pointAddDoubleYSubState1]

private theorem step_leftHiExpr {funs} (ctx : PointAddDoubleYSubContext) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect funs
      (pointAddDoubleYSubLeftLoEnv ctx) (pointAddDoubleYSubState2 ctx)
      (.builtin .mload
        [.builtin .add
          [.builtin .mload [.lit (.number 1568)], .lit (.number 64)]])
      (.vals [pointAddDoubleYSubLeftHi ctx]
        (pointAddDoubleYSubRawState ctx)) := by
  simpa [pointAddDoubleYSubLeftHi, pointAddDoubleYSubPtr,
    pointAddDoubleYSubState3, pointAddDoubleYSubRawState] using
    (step_nestedLoadAdd (funs := funs) (V := pointAddDoubleYSubLeftLoEnv ctx)
      (pointAddDoubleYSubState2 ctx) 1568 64)

theorem step_pointAddDoubleYSubLeftHiGeneric (ctx : PointAddDoubleYSubContext) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) (pointAddDoubleYSubLeftLoEnv ctx)
      (pointAddDoubleYSubState2 ctx) pointAddDoubleYSubRawStmt1
      (pointAddDoubleYSubLeftHiEnv ctx) (pointAddDoubleYSubRawState ctx)
      .normal := by
  rw [pointAddDoubleYSubRawStmt1_eq]
  exact Step.letVal (step_leftHiExpr ctx) rfl

private theorem leftHiEnv_inputLo (ctx : PointAddDoubleYSubContext) :
    VEnv.get (pointAddDoubleYSubLeftHiEnv ctx) "\x00127" =
      some ctx.inputLo := by
  rw [pointAddDoubleYSubLeftHiEnv, pointAddDoubleYSubLeftLoEnv,
    pointAddDoubleYSubInitialEnv]
  rw [venv_get_cons_ne _ _ _ _ (by decide)]
  rw [venv_get_cons_ne _ _ _ _ (by decide)]
  rw [venv_get_append_of_names_ne _ _ _ (by simp [bindZeros])]
  exact ctx.env_lo

theorem step_pointAddDoubleYSubLoVarGeneric (ctx : PointAddDoubleYSubContext) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) (pointAddDoubleYSubLeftHiEnv ctx)
      (pointAddDoubleYSubRawState ctx) pointAddDoubleYSubRawStmt2
      (pointAddDoubleYSubLoVarEnv ctx) (pointAddDoubleYSubRawState ctx)
      .normal := by
  rw [pointAddDoubleYSubRawStmt2_eq]
  exact Step.letVal (Step.var (leftHiEnv_inputLo ctx)) rfl

private theorem loVarEnv_inputHi (ctx : PointAddDoubleYSubContext) :
    VEnv.get (pointAddDoubleYSubLoVarEnv ctx) "\x00126" =
      some ctx.inputHi := by
  rw [pointAddDoubleYSubLoVarEnv, pointAddDoubleYSubLeftHiEnv,
    pointAddDoubleYSubLeftLoEnv, pointAddDoubleYSubInitialEnv]
  rw [venv_get_cons_ne _ _ _ _ (by decide)]
  rw [venv_get_cons_ne _ _ _ _ (by decide)]
  rw [venv_get_cons_ne _ _ _ _ (by decide)]
  rw [venv_get_append_of_names_ne _ _ _ (by simp [bindZeros])]
  exact ctx.env_hi

theorem step_pointAddDoubleYSubHiVarGeneric (ctx : PointAddDoubleYSubContext) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) (pointAddDoubleYSubLoVarEnv ctx)
      (pointAddDoubleYSubRawState ctx) pointAddDoubleYSubRawStmt3
      (pointAddDoubleYSubHiVarEnv ctx) (pointAddDoubleYSubRawState ctx)
      .normal := by
  rw [pointAddDoubleYSubRawStmt3_eq]
  exact Step.letVal (Step.var (loVarEnv_inputHi ctx)) rfl

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
