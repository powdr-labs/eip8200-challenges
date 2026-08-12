import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalXSubLeft

set_option warningAsError true

/-! Relational repair condition of the first unequal-point x subtraction. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

private abbrev fpSubNeedsRepairValue :=
  Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpSubNeedsRepairValue

def pointAddUnequalXSubLeftRepairValue (yst : EvmState)
    (out left right : U256) : U256 :=
  fpSubNeedsRepairValue (pointAddUnequalXSubLeftRaw yst out left right)

def pointAddUnequalXSubLeftRepairCondition : Expr Op :=
  match pointAddUnequalXSubLeftRepairStmt with
  | .cond condition _ => condition
  | _ => .lit (.number 0)

def pointAddUnequalXSubLeftRepairBody : Block Op :=
  match pointAddUnequalXSubLeftRepairStmt with
  | .cond _ body => body
  | _ => []

theorem pointAddUnequalXSubLeftRepairStmt_parts :
    pointAddUnequalXSubLeftRepairStmt =
      .cond pointAddUnequalXSubLeftRepairCondition
        pointAddUnequalXSubLeftRepairBody := by
  rfl

theorem pointAddUnequalXSubLeftRepairCondition_eq :
    pointAddUnequalXSubLeftRepairCondition =
    .builtin .gt
      [.var "fc0_81",
       .lit (.number 34565483545414906068789196026815425751)] := by
  rfl

theorem pointAddUnequalXSubLeftRepairBody_length :
    pointAddUnequalXSubLeftRepairBody.length = 3 := by
  rfl

theorem hoist_pointAddUnequalXSubLeftRepairBody :
    hoist Challenge.EvmProof.modexpExec.toDialect
      pointAddUnequalXSubLeftRepairBody = [] := by
  rfl

theorem step_pointAddUnequalXSubLeftRepairCondition (yst : EvmState)
    (out left right : U256) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect ([] :: pointAddBodyFuns)
      (pointAddUnequalXSubLeftRawEnv yst out left right)
      (pointAddUnequalXSubLeftRawState yst out left right)
      pointAddUnequalXSubLeftRepairCondition
      (.vals [pointAddUnequalXSubLeftRepairValue yst out left right]
        (pointAddUnequalXSubLeftRawState yst out left right)) := by
  have hhi : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: pointAddBodyFuns)
      (pointAddUnequalXSubLeftRawEnv yst out left right)
      (pointAddUnequalXSubLeftRawState yst out left right) (.var "fc0_81")
      (.vals [(pointAddUnequalXSubLeftRaw yst out left right).1]
        (pointAddUnequalXSubLeftRawState yst out left right)) := Step.var rfl
  have hmod : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: pointAddBodyFuns)
      (pointAddUnequalXSubLeftRawEnv yst out left right)
      (pointAddUnequalXSubLeftRawState yst out left right)
      (.lit (.number 34565483545414906068789196026815425751))
      (.vals [BitVec.ofNat 256 34565483545414906068789196026815425751]
        (pointAddUnequalXSubLeftRawState yst out left right)) := Step.lit
  rw [pointAddUnequalXSubLeftRepairCondition_eq]
  have hgt : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: pointAddBodyFuns)
      (pointAddUnequalXSubLeftRawEnv yst out left right)
      (pointAddUnequalXSubLeftRawState yst out left right)
      (.builtin .gt
        [.var "fc0_81",
         .lit (.number 34565483545414906068789196026815425751)])
      (.vals
        [b2w (BitVec.ult
          (BitVec.ofNat 256 34565483545414906068789196026815425751)
          (pointAddUnequalXSubLeftRaw yst out left right).1)]
        (pointAddUnequalXSubLeftRawState yst out left right)) :=
    Step.builtinOk
      (Step.argsCons (Step.argsCons Step.argsNil hmod) hhi) rfl
  simpa [pointAddUnequalXSubLeftRepairValue,
    Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpSubNeedsRepairValue]
    using hgt

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
