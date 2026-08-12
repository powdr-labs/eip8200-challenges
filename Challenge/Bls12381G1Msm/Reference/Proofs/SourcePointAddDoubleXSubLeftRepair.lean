import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddDoubleXSubLeftTail

set_option warningAsError true

/-! Direct relational execution of the first point-double subtraction repair. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

private def modulusHi : U256 :=
  BitVec.ofNat 256 34565483545414906068789196026815425751
private def modulusLo : U256 :=
  BitVec.ofNat 256
    45442060874369865957053122457065728162598490762543039060009208264153100167851

private def pointAddDoubleXSubLeftTemp (yst : EvmState)
    (out left right : U256) : U256 :=
  (pointAddDoubleXSubLeftRaw yst out left right).2 + modulusLo

private def pointAddDoubleXSubLeftRepairedHi (yst : EvmState)
    (out left right : U256) : U256 :=
  (pointAddDoubleXSubLeftRaw yst out left right).1 +
    (modulusHi + b2w (BitVec.ult
      (pointAddDoubleXSubLeftTemp yst out left right)
      (pointAddDoubleXSubLeftRaw yst out left right).2))

def pointAddDoubleXSubLeftRepaired (yst : EvmState)
    (out left right : U256) : U256 × U256 :=
  (pointAddDoubleXSubLeftRepairedHi yst out left right,
    pointAddDoubleXSubLeftTemp yst out left right)

private def pointAddDoubleXSubLeftTempEnv (yst : EvmState)
    (out left right : U256) : VEnv Challenge.EvmProof.modexpExec.toDialect :=
  [("\x0051", pointAddDoubleXSubLeftTemp yst out left right)] ++
    pointAddDoubleXSubLeftRawEnv yst out left right

private def pointAddDoubleXSubLeftHighEnv (yst : EvmState)
    (out left right : U256) : VEnv Challenge.EvmProof.modexpExec.toDialect :=
  VEnv.set (pointAddDoubleXSubLeftTempEnv yst out left right) "fc0_28"
    (pointAddDoubleXSubLeftRepaired yst out left right).1

private def pointAddDoubleXSubLeftBodyFinalEnv (yst : EvmState)
    (out left right : U256) : VEnv Challenge.EvmProof.modexpExec.toDialect :=
  VEnv.set (pointAddDoubleXSubLeftHighEnv yst out left right) "fc0_29"
    (pointAddDoubleXSubLeftRepaired yst out left right).2

def pointAddDoubleXSubLeftRepairedEnv (yst : EvmState)
    (out left right : U256) : VEnv Challenge.EvmProof.modexpExec.toDialect :=
  ["fc0_28", "fc0_29"].zip
    [(pointAddDoubleXSubLeftRepaired yst out left right).1,
      (pointAddDoubleXSubLeftRepaired yst out left right).2] ++
    pointAddDoubleX3Env yst out left right

theorem pointAddDoubleXSubLeftRepairedEnv_hi (yst : EvmState)
    (out left right : U256) :
    VEnv.get (pointAddDoubleXSubLeftRepairedEnv yst out left right) "fc0_28" =
      some (pointAddDoubleXSubLeftRepaired yst out left right).1 := by
  rfl

theorem pointAddDoubleXSubLeftRepairedEnv_lo (yst : EvmState)
    (out left right : U256) :
    VEnv.get (pointAddDoubleXSubLeftRepairedEnv yst out left right) "fc0_29" =
      some (pointAddDoubleXSubLeftRepaired yst out left right).2 := by
  rfl

private theorem restore_pointAddDoubleXSubLeftBodyFinalEnv
    (yst : EvmState) (out left right : U256) :
    restore (pointAddDoubleXSubLeftRawEnv yst out left right)
      (pointAddDoubleXSubLeftBodyFinalEnv yst out left right) =
    pointAddDoubleXSubLeftRepairedEnv yst out left right := by
  simp [pointAddDoubleXSubLeftBodyFinalEnv,
    pointAddDoubleXSubLeftHighEnv, pointAddDoubleXSubLeftTempEnv,
    pointAddDoubleXSubLeftRawEnv, pointAddDoubleXSubLeftRepairedEnv,
    restore, VEnv.set]

private theorem step_repairBody (yst : EvmState) (out left right : U256) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns)
      (pointAddDoubleXSubLeftRawEnv yst out left right)
      (pointAddDoubleXSubLeftRawState yst out left right)
      pointAddDoubleXSubLeftRepairBody
      (pointAddDoubleXSubLeftBodyFinalEnv yst out left right)
      (pointAddDoubleXSubLeftRawState yst out left right) .normal := by
  let raw := pointAddDoubleXSubLeftRaw yst out left right
  let temp := pointAddDoubleXSubLeftTemp yst out left right
  have hrawLo : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns)
      (pointAddDoubleXSubLeftRawEnv yst out left right)
      (pointAddDoubleXSubLeftRawState yst out left right) (.var "fc0_29")
      (.vals [raw.2] (pointAddDoubleXSubLeftRawState yst out left right)) :=
    Step.var rfl
  have hmodLo : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns)
      (pointAddDoubleXSubLeftRawEnv yst out left right)
      (pointAddDoubleXSubLeftRawState yst out left right)
      (.lit (.number
        45442060874369865957053122457065728162598490762543039060009208264153100167851))
      (.vals [modulusLo]
        (pointAddDoubleXSubLeftRawState yst out left right)) := Step.lit
  have htempExpr : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns)
      (pointAddDoubleXSubLeftRawEnv yst out left right)
      (pointAddDoubleXSubLeftRawState yst out left right)
      (.builtin .add
        [.var "fc0_29",
         .lit (.number
          45442060874369865957053122457065728162598490762543039060009208264153100167851)])
      (.vals [temp] (pointAddDoubleXSubLeftRawState yst out left right)) := by
    dsimp [temp, pointAddDoubleXSubLeftTemp]
    exact Step.builtinOk
      (Step.argsCons (Step.argsCons Step.argsNil hmodLo) hrawLo) rfl
  have htemp : ExecStmt Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns)
      (pointAddDoubleXSubLeftRawEnv yst out left right)
      (pointAddDoubleXSubLeftRawState yst out left right)
      pointAddDoubleXSubLeftRepairBody[0]!
      (pointAddDoubleXSubLeftTempEnv yst out left right)
      (pointAddDoubleXSubLeftRawState yst out left right) .normal := by
    rw [show pointAddDoubleXSubLeftRepairBody[0]! =
      .letDecl ["\x0051"]
        (some (.builtin .add
          [.var "fc0_29",
           .lit (.number
            45442060874369865957053122457065728162598490762543039060009208264153100167851)])) by
        rfl]
    exact Step.letVal htempExpr rfl
  have hrawHi : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns)
      (pointAddDoubleXSubLeftTempEnv yst out left right)
      (pointAddDoubleXSubLeftRawState yst out left right) (.var "fc0_28")
      (.vals [raw.1] (pointAddDoubleXSubLeftRawState yst out left right)) :=
    Step.var rfl
  have htempVar : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns)
      (pointAddDoubleXSubLeftTempEnv yst out left right)
      (pointAddDoubleXSubLeftRawState yst out left right) (.var "\x0051")
      (.vals [temp] (pointAddDoubleXSubLeftRawState yst out left right)) :=
    Step.var rfl
  have hrawLo' : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns)
      (pointAddDoubleXSubLeftTempEnv yst out left right)
      (pointAddDoubleXSubLeftRawState yst out left right) (.var "fc0_29")
      (.vals [raw.2] (pointAddDoubleXSubLeftRawState yst out left right)) :=
    Step.var rfl
  have hcarry : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns)
      (pointAddDoubleXSubLeftTempEnv yst out left right)
      (pointAddDoubleXSubLeftRawState yst out left right)
      (.builtin .lt [.var "\x0051", .var "fc0_29"])
      (.vals [b2w (BitVec.ult temp raw.2)]
        (pointAddDoubleXSubLeftRawState yst out left right)) :=
    Step.builtinOk
      (Step.argsCons (Step.argsCons Step.argsNil hrawLo') htempVar) rfl
  have hmodHi : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns)
      (pointAddDoubleXSubLeftTempEnv yst out left right)
      (pointAddDoubleXSubLeftRawState yst out left right)
      (.lit (.number 34565483545414906068789196026815425751))
      (.vals [modulusHi]
        (pointAddDoubleXSubLeftRawState yst out left right)) := Step.lit
  have hinner : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns)
      (pointAddDoubleXSubLeftTempEnv yst out left right)
      (pointAddDoubleXSubLeftRawState yst out left right)
      (.builtin .add
        [.lit (.number 34565483545414906068789196026815425751),
         .builtin .lt [.var "\x0051", .var "fc0_29"]])
      (.vals [modulusHi + b2w (BitVec.ult temp raw.2)]
        (pointAddDoubleXSubLeftRawState yst out left right)) :=
    Step.builtinOk
      (Step.argsCons (Step.argsCons Step.argsNil hcarry) hmodHi) rfl
  have hhighExpr : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns)
      (pointAddDoubleXSubLeftTempEnv yst out left right)
      (pointAddDoubleXSubLeftRawState yst out left right)
      (.builtin .add
        [.var "fc0_28",
         .builtin .add
          [.lit (.number 34565483545414906068789196026815425751),
           .builtin .lt [.var "\x0051", .var "fc0_29"]]])
      (.vals [pointAddDoubleXSubLeftRepairedHi yst out left right]
        (pointAddDoubleXSubLeftRawState yst out left right)) := by
    exact Step.builtinOk
      (Step.argsCons (Step.argsCons Step.argsNil hinner) hrawHi) rfl
  have hhigh : ExecStmt Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns)
      (pointAddDoubleXSubLeftTempEnv yst out left right)
      (pointAddDoubleXSubLeftRawState yst out left right)
      pointAddDoubleXSubLeftRepairBody[1]!
      (pointAddDoubleXSubLeftHighEnv yst out left right)
      (pointAddDoubleXSubLeftRawState yst out left right) .normal := by
    rw [show pointAddDoubleXSubLeftRepairBody[1]! =
      .assign ["fc0_28"]
        (.builtin .add
          [.var "fc0_28",
           .builtin .add
            [.lit (.number 34565483545414906068789196026815425751),
             .builtin .lt [.var "\x0051", .var "fc0_29"]]]) by rfl]
    exact Step.assignVal hhighExpr rfl
  have hloExpr : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns)
      (pointAddDoubleXSubLeftHighEnv yst out left right)
      (pointAddDoubleXSubLeftRawState yst out left right) (.var "\x0051")
      (.vals [(pointAddDoubleXSubLeftRepaired yst out left right).2]
        (pointAddDoubleXSubLeftRawState yst out left right)) := by
    have hvar : EvalExpr Challenge.EvmProof.modexpExec.toDialect
        ([] :: [] :: pointAddBodyFuns)
        (pointAddDoubleXSubLeftHighEnv yst out left right)
        (pointAddDoubleXSubLeftRawState yst out left right) (.var "\x0051")
        (.vals [temp]
          (pointAddDoubleXSubLeftRawState yst out left right)) := Step.var rfl
    simpa [pointAddDoubleXSubLeftRepaired,
      Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpSubRepairValue,
      temp, pointAddDoubleXSubLeftTemp, modulusLo, raw] using hvar
  have hlo : ExecStmt Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns)
      (pointAddDoubleXSubLeftHighEnv yst out left right)
      (pointAddDoubleXSubLeftRawState yst out left right)
      pointAddDoubleXSubLeftRepairBody[2]!
      (pointAddDoubleXSubLeftBodyFinalEnv yst out left right)
      (pointAddDoubleXSubLeftRawState yst out left right) .normal := by
    rw [show pointAddDoubleXSubLeftRepairBody[2]! =
      .assign ["fc0_29"] (.var "\x0051") by rfl]
    exact Step.assignVal hloExpr rfl
  rw [show pointAddDoubleXSubLeftRepairBody =
      [pointAddDoubleXSubLeftRepairBody[0]!,
       pointAddDoubleXSubLeftRepairBody[1]!,
       pointAddDoubleXSubLeftRepairBody[2]!] by rfl]
  exact Step.seqCons htemp (Step.seqCons hhigh (Step.seqCons hlo Step.seqNil))

theorem step_pointAddDoubleXSubLeftRepair (yst : EvmState)
    (out left right : U256)
    (hrepair : pointAddDoubleXSubLeftRepairValue yst out left right ≠ 0) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect ([] :: pointAddBodyFuns)
      (pointAddDoubleXSubLeftRawEnv yst out left right)
      (pointAddDoubleXSubLeftRawState yst out left right)
      pointAddDoubleXSubLeftRepairStmt
      (pointAddDoubleXSubLeftRepairedEnv yst out left right)
      (pointAddDoubleXSubLeftRawState yst out left right) .normal := by
  rw [pointAddDoubleXSubLeftRepairStmt_parts]
  have hbody := Step.block
    (D := Challenge.EvmProof.modexpExec.toDialect)
    (body := pointAddDoubleXSubLeftRepairBody)
    (step_repairBody yst out left right)
  exact Step.ifTrue (step_pointAddDoubleXSubLeftRepairCondition yst out left right)
    hrepair (by
      rw [restore_pointAddDoubleXSubLeftBodyFinalEnv] at hbody
      exact hbody)

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
