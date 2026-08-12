import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalXSubLeftTail

set_option warningAsError true

/-! Direct relational execution of the first unequal-point subtraction repair. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

private def modulusHi : U256 :=
  BitVec.ofNat 256 34565483545414906068789196026815425751
private def modulusLo : U256 :=
  BitVec.ofNat 256
    45442060874369865957053122457065728162598490762543039060009208264153100167851

private def pointAddUnequalXSubLeftTemp (yst : EvmState)
    (out left right : U256) : U256 :=
  (pointAddUnequalXSubLeftRaw yst out left right).2 + modulusLo

private def pointAddUnequalXSubLeftRepairedHi (yst : EvmState)
    (out left right : U256) : U256 :=
  (pointAddUnequalXSubLeftRaw yst out left right).1 +
    (modulusHi + b2w (BitVec.ult
      (pointAddUnequalXSubLeftTemp yst out left right)
      (pointAddUnequalXSubLeftRaw yst out left right).2))

def pointAddUnequalXSubLeftRepaired (yst : EvmState)
    (out left right : U256) : U256 × U256 :=
  (pointAddUnequalXSubLeftRepairedHi yst out left right,
    pointAddUnequalXSubLeftTemp yst out left right)

theorem pointAddUnequalXSubLeftRepaired_eq_fpSubRepairValue
    (yst : EvmState) (out left right : U256) :
    pointAddUnequalXSubLeftRepaired yst out left right =
      Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpSubRepairValue
        (pointAddUnequalXSubLeftRaw yst out left right) := by
  simp only [pointAddUnequalXSubLeftRepaired,
    pointAddUnequalXSubLeftRepairedHi, pointAddUnequalXSubLeftTemp,
    modulusHi, modulusLo,
    Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpSubRepairValue,
    add_assoc]

private def pointAddUnequalXSubLeftTempEnv (yst : EvmState)
    (out left right : U256) : VEnv Challenge.EvmProof.modexpExec.toDialect :=
  [("\x0051", pointAddUnequalXSubLeftTemp yst out left right)] ++
    pointAddUnequalXSubLeftRawEnv yst out left right

private def pointAddUnequalXSubLeftHighEnv (yst : EvmState)
    (out left right : U256) : VEnv Challenge.EvmProof.modexpExec.toDialect :=
  VEnv.set (pointAddUnequalXSubLeftTempEnv yst out left right) "fc0_81"
    (pointAddUnequalXSubLeftRepaired yst out left right).1

private def pointAddUnequalXSubLeftBodyFinalEnv (yst : EvmState)
    (out left right : U256) : VEnv Challenge.EvmProof.modexpExec.toDialect :=
  VEnv.set (pointAddUnequalXSubLeftHighEnv yst out left right) "fc0_82"
    (pointAddUnequalXSubLeftRepaired yst out left right).2

def pointAddUnequalXSubLeftRepairedEnv (yst : EvmState)
    (out left right : U256) : VEnv Challenge.EvmProof.modexpExec.toDialect :=
  ["fc0_81", "fc0_82"].zip
    [(pointAddUnequalXSubLeftRepaired yst out left right).1,
      (pointAddUnequalXSubLeftRepaired yst out left right).2] ++
    pointAddUnequalX3Env yst out left right

theorem pointAddUnequalXSubLeftRepairedEnv_hi (yst : EvmState)
    (out left right : U256) :
    VEnv.get (pointAddUnequalXSubLeftRepairedEnv yst out left right) "fc0_81" =
      some (pointAddUnequalXSubLeftRepaired yst out left right).1 := by
  rfl

theorem pointAddUnequalXSubLeftRepairedEnv_lo (yst : EvmState)
    (out left right : U256) :
    VEnv.get (pointAddUnequalXSubLeftRepairedEnv yst out left right) "fc0_82" =
      some (pointAddUnequalXSubLeftRepaired yst out left right).2 := by
  rfl

private theorem restore_pointAddUnequalXSubLeftBodyFinalEnv
    (yst : EvmState) (out left right : U256) :
    restore (pointAddUnequalXSubLeftRawEnv yst out left right)
      (pointAddUnequalXSubLeftBodyFinalEnv yst out left right) =
    pointAddUnequalXSubLeftRepairedEnv yst out left right := by
  simp [pointAddUnequalXSubLeftBodyFinalEnv,
    pointAddUnequalXSubLeftHighEnv, pointAddUnequalXSubLeftTempEnv,
    pointAddUnequalXSubLeftRawEnv, pointAddUnequalXSubLeftRepairedEnv,
    restore, VEnv.set]

private theorem step_repairBody (yst : EvmState) (out left right : U256) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns)
      (pointAddUnequalXSubLeftRawEnv yst out left right)
      (pointAddUnequalXSubLeftRawState yst out left right)
      pointAddUnequalXSubLeftRepairBody
      (pointAddUnequalXSubLeftBodyFinalEnv yst out left right)
      (pointAddUnequalXSubLeftRawState yst out left right) .normal := by
  let raw := pointAddUnequalXSubLeftRaw yst out left right
  let temp := pointAddUnequalXSubLeftTemp yst out left right
  have hrawLo : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns)
      (pointAddUnequalXSubLeftRawEnv yst out left right)
      (pointAddUnequalXSubLeftRawState yst out left right) (.var "fc0_82")
      (.vals [raw.2] (pointAddUnequalXSubLeftRawState yst out left right)) :=
    Step.var rfl
  have hmodLo : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns)
      (pointAddUnequalXSubLeftRawEnv yst out left right)
      (pointAddUnequalXSubLeftRawState yst out left right)
      (.lit (.number
        45442060874369865957053122457065728162598490762543039060009208264153100167851))
      (.vals [modulusLo]
        (pointAddUnequalXSubLeftRawState yst out left right)) := Step.lit
  have htempExpr : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns)
      (pointAddUnequalXSubLeftRawEnv yst out left right)
      (pointAddUnequalXSubLeftRawState yst out left right)
      (.builtin .add
        [.var "fc0_82",
         .lit (.number
          45442060874369865957053122457065728162598490762543039060009208264153100167851)])
      (.vals [temp] (pointAddUnequalXSubLeftRawState yst out left right)) := by
    dsimp [temp, pointAddUnequalXSubLeftTemp]
    exact Step.builtinOk
      (Step.argsCons (Step.argsCons Step.argsNil hmodLo) hrawLo) rfl
  have htemp : ExecStmt Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns)
      (pointAddUnequalXSubLeftRawEnv yst out left right)
      (pointAddUnequalXSubLeftRawState yst out left right)
      pointAddUnequalXSubLeftRepairBody[0]!
      (pointAddUnequalXSubLeftTempEnv yst out left right)
      (pointAddUnequalXSubLeftRawState yst out left right) .normal := by
    rw [show pointAddUnequalXSubLeftRepairBody[0]! =
      .letDecl ["\x0051"]
        (some (.builtin .add
          [.var "fc0_82",
           .lit (.number
            45442060874369865957053122457065728162598490762543039060009208264153100167851)])) by
        rfl]
    exact Step.letVal htempExpr rfl
  have hrawHi : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns)
      (pointAddUnequalXSubLeftTempEnv yst out left right)
      (pointAddUnequalXSubLeftRawState yst out left right) (.var "fc0_81")
      (.vals [raw.1] (pointAddUnequalXSubLeftRawState yst out left right)) :=
    Step.var rfl
  have htempVar : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns)
      (pointAddUnequalXSubLeftTempEnv yst out left right)
      (pointAddUnequalXSubLeftRawState yst out left right) (.var "\x0051")
      (.vals [temp] (pointAddUnequalXSubLeftRawState yst out left right)) :=
    Step.var rfl
  have hrawLo' : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns)
      (pointAddUnequalXSubLeftTempEnv yst out left right)
      (pointAddUnequalXSubLeftRawState yst out left right) (.var "fc0_82")
      (.vals [raw.2] (pointAddUnequalXSubLeftRawState yst out left right)) :=
    Step.var rfl
  have hcarry : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns)
      (pointAddUnequalXSubLeftTempEnv yst out left right)
      (pointAddUnequalXSubLeftRawState yst out left right)
      (.builtin .lt [.var "\x0051", .var "fc0_82"])
      (.vals [b2w (BitVec.ult temp raw.2)]
        (pointAddUnequalXSubLeftRawState yst out left right)) :=
    Step.builtinOk
      (Step.argsCons (Step.argsCons Step.argsNil hrawLo') htempVar) rfl
  have hmodHi : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns)
      (pointAddUnequalXSubLeftTempEnv yst out left right)
      (pointAddUnequalXSubLeftRawState yst out left right)
      (.lit (.number 34565483545414906068789196026815425751))
      (.vals [modulusHi]
        (pointAddUnequalXSubLeftRawState yst out left right)) := Step.lit
  have hinner : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns)
      (pointAddUnequalXSubLeftTempEnv yst out left right)
      (pointAddUnequalXSubLeftRawState yst out left right)
      (.builtin .add
        [.lit (.number 34565483545414906068789196026815425751),
         .builtin .lt [.var "\x0051", .var "fc0_82"]])
      (.vals [modulusHi + b2w (BitVec.ult temp raw.2)]
        (pointAddUnequalXSubLeftRawState yst out left right)) :=
    Step.builtinOk
      (Step.argsCons (Step.argsCons Step.argsNil hcarry) hmodHi) rfl
  have hhighExpr : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns)
      (pointAddUnequalXSubLeftTempEnv yst out left right)
      (pointAddUnequalXSubLeftRawState yst out left right)
      (.builtin .add
        [.var "fc0_81",
         .builtin .add
          [.lit (.number 34565483545414906068789196026815425751),
           .builtin .lt [.var "\x0051", .var "fc0_82"]]])
      (.vals [pointAddUnequalXSubLeftRepairedHi yst out left right]
        (pointAddUnequalXSubLeftRawState yst out left right)) := by
    exact Step.builtinOk
      (Step.argsCons (Step.argsCons Step.argsNil hinner) hrawHi) rfl
  have hhigh : ExecStmt Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns)
      (pointAddUnequalXSubLeftTempEnv yst out left right)
      (pointAddUnequalXSubLeftRawState yst out left right)
      pointAddUnequalXSubLeftRepairBody[1]!
      (pointAddUnequalXSubLeftHighEnv yst out left right)
      (pointAddUnequalXSubLeftRawState yst out left right) .normal := by
    rw [show pointAddUnequalXSubLeftRepairBody[1]! =
      .assign ["fc0_81"]
        (.builtin .add
          [.var "fc0_81",
           .builtin .add
            [.lit (.number 34565483545414906068789196026815425751),
             .builtin .lt [.var "\x0051", .var "fc0_82"]]]) by rfl]
    exact Step.assignVal hhighExpr rfl
  have hloExpr : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns)
      (pointAddUnequalXSubLeftHighEnv yst out left right)
      (pointAddUnequalXSubLeftRawState yst out left right) (.var "\x0051")
      (.vals [(pointAddUnequalXSubLeftRepaired yst out left right).2]
        (pointAddUnequalXSubLeftRawState yst out left right)) := by
    have hvar : EvalExpr Challenge.EvmProof.modexpExec.toDialect
        ([] :: [] :: pointAddBodyFuns)
        (pointAddUnequalXSubLeftHighEnv yst out left right)
        (pointAddUnequalXSubLeftRawState yst out left right) (.var "\x0051")
        (.vals [temp]
          (pointAddUnequalXSubLeftRawState yst out left right)) := Step.var rfl
    simpa [pointAddUnequalXSubLeftRepaired,
      Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpSubRepairValue,
      temp, pointAddUnequalXSubLeftTemp, modulusLo, raw] using hvar
  have hlo : ExecStmt Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns)
      (pointAddUnequalXSubLeftHighEnv yst out left right)
      (pointAddUnequalXSubLeftRawState yst out left right)
      pointAddUnequalXSubLeftRepairBody[2]!
      (pointAddUnequalXSubLeftBodyFinalEnv yst out left right)
      (pointAddUnequalXSubLeftRawState yst out left right) .normal := by
    rw [show pointAddUnequalXSubLeftRepairBody[2]! =
      .assign ["fc0_82"] (.var "\x0051") by rfl]
    exact Step.assignVal hloExpr rfl
  rw [show pointAddUnequalXSubLeftRepairBody =
      [pointAddUnequalXSubLeftRepairBody[0]!,
       pointAddUnequalXSubLeftRepairBody[1]!,
       pointAddUnequalXSubLeftRepairBody[2]!] by rfl]
  exact Step.seqCons htemp (Step.seqCons hhigh (Step.seqCons hlo Step.seqNil))

theorem step_pointAddUnequalXSubLeftRepair (yst : EvmState)
    (out left right : U256)
    (hrepair : pointAddUnequalXSubLeftRepairValue yst out left right ≠ 0) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect ([] :: pointAddBodyFuns)
      (pointAddUnequalXSubLeftRawEnv yst out left right)
      (pointAddUnequalXSubLeftRawState yst out left right)
      pointAddUnequalXSubLeftRepairStmt
      (pointAddUnequalXSubLeftRepairedEnv yst out left right)
      (pointAddUnequalXSubLeftRawState yst out left right) .normal := by
  rw [pointAddUnequalXSubLeftRepairStmt_parts]
  have hbody := Step.block
    (D := Challenge.EvmProof.modexpExec.toDialect)
    (body := pointAddUnequalXSubLeftRepairBody)
    (step_repairBody yst out left right)
  exact Step.ifTrue (step_pointAddUnequalXSubLeftRepairCondition yst out left right)
    hrepair (by
      rw [restore_pointAddUnequalXSubLeftBodyFinalEnv] at hbody
      exact hbody)

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
