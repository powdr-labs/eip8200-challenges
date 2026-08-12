import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalYSub
import Challenge.Bls12381G1Msm.Reference.Proofs.SourceVEnvRestore

set_option warningAsError true

/-! Declaration, left-y loads, and input reads for the generic final y subtraction. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def pointAddUnequalYSubInitialEnv (ctx : PointAddUnequalYSubContext) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  bindZeros Challenge.EvmProof.modexpExec.toDialect ["fc0_102", "fc0_103"] ++
    ctx.env
def pointAddUnequalYSubLeftLoEnv (ctx : PointAddUnequalYSubContext) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  ("fc0_104", pointAddUnequalYSubLeftLo ctx) :: pointAddUnequalYSubInitialEnv ctx
def pointAddUnequalYSubLeftHiEnv (ctx : PointAddUnequalYSubContext) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  ("fc0_105", pointAddUnequalYSubLeftHi ctx) :: pointAddUnequalYSubLeftLoEnv ctx
def pointAddUnequalYSubLoVarEnv (ctx : PointAddUnequalYSubContext) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  ("fc0_106", ctx.inputLo) :: pointAddUnequalYSubLeftHiEnv ctx
def pointAddUnequalYSubHiVarEnv (ctx : PointAddUnequalYSubContext) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  ("fc0_107", ctx.inputHi) :: pointAddUnequalYSubLoVarEnv ctx

theorem step_pointAddUnequalYSubRawDeclGeneric (ctx : PointAddUnequalYSubContext) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect
      ([] :: pointAddBodyFuns) ctx.env ctx.state pointAddUnequalYSubRawDeclStmt
      (pointAddUnequalYSubInitialEnv ctx) ctx.state .normal := by
  rw [pointAddUnequalYSubRawDeclStmt_eq]
  simpa [pointAddUnequalYSubInitialEnv] using
    (Step.letZero (D := Challenge.EvmProof.modexpExec.toDialect)
      (funs := [] :: pointAddBodyFuns) (V := ctx.env) (st := ctx.state)
      (vars := ["fc0_102", "fc0_103"]))

private theorem step_leftLoExpr {funs} (ctx : PointAddUnequalYSubContext) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect funs
      (pointAddUnequalYSubInitialEnv ctx) ctx.state
      (.builtin .mload
        [.builtin .add
          [.builtin .mload [.lit (.number 1568)], .lit (.number 96)]])
      (.vals [pointAddUnequalYSubLeftLo ctx]
        (pointAddUnequalYSubState2 ctx)) := by
  simpa [pointAddUnequalYSubLeftLo, pointAddUnequalYSubPtr,
    pointAddUnequalYSubState1, pointAddUnequalYSubState2] using
    (step_nestedLoadAdd (funs := funs)
      (V := pointAddUnequalYSubInitialEnv ctx) ctx.state 1568 96)

theorem step_pointAddUnequalYSubLeftLoGeneric (ctx : PointAddUnequalYSubContext) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) (pointAddUnequalYSubInitialEnv ctx)
      ctx.state pointAddUnequalYSubRawStmt0 (pointAddUnequalYSubLeftLoEnv ctx)
      (pointAddUnequalYSubState2 ctx) .normal := by
  rw [pointAddUnequalYSubRawStmt0_eq]
  exact Step.letVal (step_leftLoExpr ctx) rfl

@[simp] private theorem touchMemory_memory (yst : EvmState)
    (offset size : Nat) : (touchMemory yst offset size).memory = yst.memory := rfl

@[simp] private theorem ySubState2_memory (ctx : PointAddUnequalYSubContext) :
    (pointAddUnequalYSubState2 ctx).memory = ctx.state.memory := by
  simp [pointAddUnequalYSubState2, pointAddUnequalYSubState1]

private theorem step_leftHiExpr {funs} (ctx : PointAddUnequalYSubContext) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect funs
      (pointAddUnequalYSubLeftLoEnv ctx) (pointAddUnequalYSubState2 ctx)
      (.builtin .mload
        [.builtin .add
          [.builtin .mload [.lit (.number 1568)], .lit (.number 64)]])
      (.vals [pointAddUnequalYSubLeftHi ctx]
        (pointAddUnequalYSubRawState ctx)) := by
  simpa [pointAddUnequalYSubLeftHi, pointAddUnequalYSubPtr,
    pointAddUnequalYSubState3, pointAddUnequalYSubRawState] using
    (step_nestedLoadAdd (funs := funs) (V := pointAddUnequalYSubLeftLoEnv ctx)
      (pointAddUnequalYSubState2 ctx) 1568 64)

theorem step_pointAddUnequalYSubLeftHiGeneric (ctx : PointAddUnequalYSubContext) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) (pointAddUnequalYSubLeftLoEnv ctx)
      (pointAddUnequalYSubState2 ctx) pointAddUnequalYSubRawStmt1
      (pointAddUnequalYSubLeftHiEnv ctx) (pointAddUnequalYSubRawState ctx)
      .normal := by
  rw [pointAddUnequalYSubRawStmt1_eq]
  exact Step.letVal (step_leftHiExpr ctx) rfl

private theorem leftHiEnv_inputLo (ctx : PointAddUnequalYSubContext) :
    VEnv.get (pointAddUnequalYSubLeftHiEnv ctx) "\x00141" =
      some ctx.inputLo := by
  rw [pointAddUnequalYSubLeftHiEnv, pointAddUnequalYSubLeftLoEnv,
    pointAddUnequalYSubInitialEnv]
  rw [venv_get_cons_ne _ _ _ _ (by decide)]
  rw [venv_get_cons_ne _ _ _ _ (by decide)]
  rw [venv_get_append_of_names_ne _ _ _ (by simp [bindZeros])]
  exact ctx.env_lo

theorem step_pointAddUnequalYSubLoVarGeneric (ctx : PointAddUnequalYSubContext) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) (pointAddUnequalYSubLeftHiEnv ctx)
      (pointAddUnequalYSubRawState ctx) pointAddUnequalYSubRawStmt2
      (pointAddUnequalYSubLoVarEnv ctx) (pointAddUnequalYSubRawState ctx)
      .normal := by
  rw [pointAddUnequalYSubRawStmt2_eq]
  exact Step.letVal (Step.var (leftHiEnv_inputLo ctx)) rfl

private theorem loVarEnv_inputHi (ctx : PointAddUnequalYSubContext) :
    VEnv.get (pointAddUnequalYSubLoVarEnv ctx) "\x00140" =
      some ctx.inputHi := by
  rw [pointAddUnequalYSubLoVarEnv, pointAddUnequalYSubLeftHiEnv,
    pointAddUnequalYSubLeftLoEnv, pointAddUnequalYSubInitialEnv]
  rw [venv_get_cons_ne _ _ _ _ (by decide)]
  rw [venv_get_cons_ne _ _ _ _ (by decide)]
  rw [venv_get_cons_ne _ _ _ _ (by decide)]
  rw [venv_get_append_of_names_ne _ _ _ (by simp [bindZeros])]
  exact ctx.env_hi

theorem step_pointAddUnequalYSubHiVarGeneric (ctx : PointAddUnequalYSubContext) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) (pointAddUnequalYSubLoVarEnv ctx)
      (pointAddUnequalYSubRawState ctx) pointAddUnequalYSubRawStmt3
      (pointAddUnequalYSubHiVarEnv ctx) (pointAddUnequalYSubRawState ctx)
      .normal := by
  rw [pointAddUnequalYSubRawStmt3_eq]
  exact Step.letVal (Step.var (loVarEnv_inputHi ctx)) rfl

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
