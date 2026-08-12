import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalXSubRight

set_option warningAsError true

/-! Generic relational declaration and load stages of the second x subtraction. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def pointAddUnequalXSubRightInitialEnv (ctx : PointAddUnequalXSubRightContext) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  bindZeros Challenge.EvmProof.modexpExec.toDialect ["fc0_88", "fc0_89"] ++
    ctx.env

def pointAddUnequalXSubRightLoEnv (ctx : PointAddUnequalXSubRightContext) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  ("fc0_90", pointAddUnequalXSubRightLo ctx) ::
    pointAddUnequalXSubRightInitialEnv ctx

def pointAddUnequalXSubRightHiEnv (ctx : PointAddUnequalXSubRightContext) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  ("fc0_91", pointAddUnequalXSubRightHi ctx) ::
    pointAddUnequalXSubRightLoEnv ctx

theorem step_pointAddUnequalXSubRightRawDeclGeneric
    (ctx : PointAddUnequalXSubRightContext) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect
      ([] :: pointAddBodyFuns) ctx.env ctx.state
      pointAddUnequalXSubRightRawDeclStmt
      (pointAddUnequalXSubRightInitialEnv ctx) ctx.state .normal := by
  rw [pointAddUnequalXSubRightRawDeclStmt_eq]
  simpa [pointAddUnequalXSubRightInitialEnv] using
    (Step.letZero
      (D := Challenge.EvmProof.modexpExec.toDialect)
      (funs := [] :: pointAddBodyFuns) (V := ctx.env) (st := ctx.state)
      (vars := ["fc0_88", "fc0_89"]))

private theorem step_pointAddUnequalXSubRightLoExprGeneric {funs}
    (ctx : PointAddUnequalXSubRightContext) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect funs
      (pointAddUnequalXSubRightInitialEnv ctx) ctx.state
      (.builtin .mload
        [.builtin .add
          [.builtin .mload [.lit (.number 1600)], .lit (.number 32)]])
      (.vals [pointAddUnequalXSubRightLo ctx]
        (pointAddUnequalXSubRightState2 ctx)) := by
  simpa [pointAddUnequalXSubRightLo, pointAddUnequalXSubRightPtr,
    pointAddUnequalXSubRightState1, pointAddUnequalXSubRightState2] using
    (step_nestedLoadAdd (funs := funs)
      (V := pointAddUnequalXSubRightInitialEnv ctx) ctx.state 1600 32)

theorem step_pointAddUnequalXSubRightLoGeneric
    (ctx : PointAddUnequalXSubRightContext) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) (pointAddUnequalXSubRightInitialEnv ctx)
      ctx.state pointAddUnequalXSubRightRawStmt0
      (pointAddUnequalXSubRightLoEnv ctx)
      (pointAddUnequalXSubRightState2 ctx) .normal := by
  rw [pointAddUnequalXSubRightRawStmt0_eq]
  exact Step.letVal (step_pointAddUnequalXSubRightLoExprGeneric ctx) rfl

@[simp] private theorem touchMemory_memory (yst : EvmState)
    (offset size : Nat) : (touchMemory yst offset size).memory = yst.memory := rfl

@[simp] private theorem pointAddUnequalXSubRightState2_memory
    (ctx : PointAddUnequalXSubRightContext) :
    (pointAddUnequalXSubRightState2 ctx).memory = ctx.state.memory := by
  simp [pointAddUnequalXSubRightState2, pointAddUnequalXSubRightState1]

private theorem step_pointAddUnequalXSubRightHiExprGeneric {funs}
    (ctx : PointAddUnequalXSubRightContext) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect funs
      (pointAddUnequalXSubRightLoEnv ctx) (pointAddUnequalXSubRightState2 ctx)
      (.builtin .mload [.builtin .mload [.lit (.number 1600)]])
      (.vals [pointAddUnequalXSubRightHi ctx]
        (pointAddUnequalXSubRightRawState ctx)) := by
  simpa [pointAddUnequalXSubRightHi, pointAddUnequalXSubRightPtr,
    pointAddUnequalXSubRightState3, pointAddUnequalXSubRightRawState] using
    (step_nestedLoad (funs := funs) (V := pointAddUnequalXSubRightLoEnv ctx)
      (pointAddUnequalXSubRightState2 ctx) 1600)

theorem step_pointAddUnequalXSubRightHiGeneric
    (ctx : PointAddUnequalXSubRightContext) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) (pointAddUnequalXSubRightLoEnv ctx)
      (pointAddUnequalXSubRightState2 ctx) pointAddUnequalXSubRightRawStmt1
      (pointAddUnequalXSubRightHiEnv ctx)
      (pointAddUnequalXSubRightRawState ctx) .normal := by
  rw [pointAddUnequalXSubRightRawStmt1_eq]
  exact Step.letVal (step_pointAddUnequalXSubRightHiExprGeneric ctx) rfl

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
