import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddDoubleXSubRight

set_option warningAsError true

/-! Generic relational declaration and load stages of the second x subtraction. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def pointAddDoubleXSubRightInitialEnv (ctx : PointAddDoubleXSubRightContext) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  bindZeros Challenge.EvmProof.modexpExec.toDialect ["fc0_35", "fc0_36"] ++
    ctx.env

def pointAddDoubleXSubRightLoEnv (ctx : PointAddDoubleXSubRightContext) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  ("fc0_37", pointAddDoubleXSubRightLo ctx) ::
    pointAddDoubleXSubRightInitialEnv ctx

def pointAddDoubleXSubRightHiEnv (ctx : PointAddDoubleXSubRightContext) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  ("fc0_38", pointAddDoubleXSubRightHi ctx) ::
    pointAddDoubleXSubRightLoEnv ctx

theorem step_pointAddDoubleXSubRightRawDeclGeneric
    (ctx : PointAddDoubleXSubRightContext) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect
      ([] :: pointAddBodyFuns) ctx.env ctx.state
      pointAddDoubleXSubRightRawDeclStmt
      (pointAddDoubleXSubRightInitialEnv ctx) ctx.state .normal := by
  rw [pointAddDoubleXSubRightRawDeclStmt_eq]
  simpa [pointAddDoubleXSubRightInitialEnv] using
    (Step.letZero
      (D := Challenge.EvmProof.modexpExec.toDialect)
      (funs := [] :: pointAddBodyFuns) (V := ctx.env) (st := ctx.state)
      (vars := ["fc0_35", "fc0_36"]))

private theorem step_pointAddDoubleXSubRightLoExprGeneric {funs}
    (ctx : PointAddDoubleXSubRightContext) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect funs
      (pointAddDoubleXSubRightInitialEnv ctx) ctx.state
      (.builtin .mload
        [.builtin .add
          [.builtin .mload [.lit (.number 1600)], .lit (.number 32)]])
      (.vals [pointAddDoubleXSubRightLo ctx]
        (pointAddDoubleXSubRightState2 ctx)) := by
  simpa [pointAddDoubleXSubRightLo, pointAddDoubleXSubRightPtr,
    pointAddDoubleXSubRightState1, pointAddDoubleXSubRightState2] using
    (step_nestedLoadAdd (funs := funs)
      (V := pointAddDoubleXSubRightInitialEnv ctx) ctx.state 1600 32)

theorem step_pointAddDoubleXSubRightLoGeneric
    (ctx : PointAddDoubleXSubRightContext) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) (pointAddDoubleXSubRightInitialEnv ctx)
      ctx.state pointAddDoubleXSubRightRawStmt0
      (pointAddDoubleXSubRightLoEnv ctx)
      (pointAddDoubleXSubRightState2 ctx) .normal := by
  rw [pointAddDoubleXSubRightRawStmt0_eq]
  exact Step.letVal (step_pointAddDoubleXSubRightLoExprGeneric ctx) rfl

@[simp] private theorem touchMemory_memory (yst : EvmState)
    (offset size : Nat) : (touchMemory yst offset size).memory = yst.memory := rfl

@[simp] private theorem pointAddDoubleXSubRightState2_memory
    (ctx : PointAddDoubleXSubRightContext) :
    (pointAddDoubleXSubRightState2 ctx).memory = ctx.state.memory := by
  simp [pointAddDoubleXSubRightState2, pointAddDoubleXSubRightState1]

private theorem step_pointAddDoubleXSubRightHiExprGeneric {funs}
    (ctx : PointAddDoubleXSubRightContext) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect funs
      (pointAddDoubleXSubRightLoEnv ctx) (pointAddDoubleXSubRightState2 ctx)
      (.builtin .mload [.builtin .mload [.lit (.number 1600)]])
      (.vals [pointAddDoubleXSubRightHi ctx]
        (pointAddDoubleXSubRightRawState ctx)) := by
  simpa [pointAddDoubleXSubRightHi, pointAddDoubleXSubRightPtr,
    pointAddDoubleXSubRightState3, pointAddDoubleXSubRightRawState] using
    (step_nestedLoad (funs := funs) (V := pointAddDoubleXSubRightLoEnv ctx)
      (pointAddDoubleXSubRightState2 ctx) 1600)

theorem step_pointAddDoubleXSubRightHiGeneric
    (ctx : PointAddDoubleXSubRightContext) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) (pointAddDoubleXSubRightLoEnv ctx)
      (pointAddDoubleXSubRightState2 ctx) pointAddDoubleXSubRightRawStmt1
      (pointAddDoubleXSubRightHiEnv ctx)
      (pointAddDoubleXSubRightRawState ctx) .normal := by
  rw [pointAddDoubleXSubRightRawStmt1_eq]
  exact Step.letVal (step_pointAddDoubleXSubRightHiExprGeneric ctx) rfl

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
