import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddDoubleXSubLeft

set_option warningAsError true

/-! Relational repair condition of the first inlined point-double `fpSub`. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

private abbrev fpSubNeedsRepairValue :=
  Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpSubNeedsRepairValue

def pointAddDoubleXSubLeftRepairValue (yst : EvmState)
    (out left right : U256) : U256 :=
  fpSubNeedsRepairValue (pointAddDoubleXSubLeftRaw yst out left right)

def pointAddDoubleXSubLeftRepairCondition : Expr Op :=
  match pointAddDoubleXSubLeftRepairStmt with
  | .cond condition _ => condition
  | _ => .lit (.number 0)

def pointAddDoubleXSubLeftRepairBody : Block Op :=
  match pointAddDoubleXSubLeftRepairStmt with
  | .cond _ body => body
  | _ => []

theorem pointAddDoubleXSubLeftRepairStmt_parts :
    pointAddDoubleXSubLeftRepairStmt =
      .cond pointAddDoubleXSubLeftRepairCondition
        pointAddDoubleXSubLeftRepairBody := by
  rfl

theorem pointAddDoubleXSubLeftRepairCondition_eq :
    pointAddDoubleXSubLeftRepairCondition =
    .builtin .gt
      [.var "fc0_28",
       .lit (.number 34565483545414906068789196026815425751)] := by
  rfl

theorem pointAddDoubleXSubLeftRepairBody_length :
    pointAddDoubleXSubLeftRepairBody.length = 3 := by
  rfl

theorem hoist_pointAddDoubleXSubLeftRepairBody :
    hoist Challenge.EvmProof.modexpExec.toDialect
      pointAddDoubleXSubLeftRepairBody = [] := by
  rfl

theorem step_pointAddDoubleXSubLeftRepairCondition (yst : EvmState)
    (out left right : U256) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect ([] :: pointAddBodyFuns)
      (pointAddDoubleXSubLeftRawEnv yst out left right)
      (pointAddDoubleXSubLeftRawState yst out left right)
      pointAddDoubleXSubLeftRepairCondition
      (.vals [pointAddDoubleXSubLeftRepairValue yst out left right]
        (pointAddDoubleXSubLeftRawState yst out left right)) := by
  have hhi : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: pointAddBodyFuns)
      (pointAddDoubleXSubLeftRawEnv yst out left right)
      (pointAddDoubleXSubLeftRawState yst out left right) (.var "fc0_28")
      (.vals [(pointAddDoubleXSubLeftRaw yst out left right).1]
        (pointAddDoubleXSubLeftRawState yst out left right)) := Step.var rfl
  have hmod : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: pointAddBodyFuns)
      (pointAddDoubleXSubLeftRawEnv yst out left right)
      (pointAddDoubleXSubLeftRawState yst out left right)
      (.lit (.number 34565483545414906068789196026815425751))
      (.vals [BitVec.ofNat 256 34565483545414906068789196026815425751]
        (pointAddDoubleXSubLeftRawState yst out left right)) := Step.lit
  rw [pointAddDoubleXSubLeftRepairCondition_eq]
  have hgt : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: pointAddBodyFuns)
      (pointAddDoubleXSubLeftRawEnv yst out left right)
      (pointAddDoubleXSubLeftRawState yst out left right)
      (.builtin .gt
        [.var "fc0_28",
         .lit (.number 34565483545414906068789196026815425751)])
      (.vals
        [b2w (BitVec.ult
          (BitVec.ofNat 256 34565483545414906068789196026815425751)
          (pointAddDoubleXSubLeftRaw yst out left right).1)]
        (pointAddDoubleXSubLeftRawState yst out left right)) :=
    Step.builtinOk
      (Step.argsCons (Step.argsCons Step.argsNil hmod) hhi) rfl
  simpa [pointAddDoubleXSubLeftRepairValue,
    Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpSubNeedsRepairValue]
    using hgt

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
