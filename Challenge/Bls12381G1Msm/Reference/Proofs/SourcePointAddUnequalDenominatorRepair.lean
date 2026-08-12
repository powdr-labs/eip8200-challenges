import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalDenominatorRaw
import Challenge.EvmProof.ExecSound

set_option warningAsError true

/-! Conditional modulus repair for the unequal denominator. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

private abbrev fpSubNeedsRepairValue :=
  Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpSubNeedsRepairValue

def pointAddUnequalDenominatorRepairValue (yst : EvmState)
    (out left right : U256) : U256 :=
  fpSubNeedsRepairValue (pointAddUnequalDenominatorRaw yst out left right)

def pointAddUnequalDenominatorRepaired (yst : EvmState)
    (out left right : U256) : U256 × U256 :=
  let raw := pointAddUnequalDenominatorRaw yst out left right
  let newLo := raw.2 + BitVec.ofNat 256
    45442060874369865957053122457065728162598490762543039060009208264153100167851
  (raw.1 + (BitVec.ofNat 256 34565483545414906068789196026815425751 +
      b2w (BitVec.ult newLo raw.2)), newLo)

def pointAddUnequalDenominatorResult (yst : EvmState)
    (out left right : U256) : U256 × U256 :=
  if pointAddUnequalDenominatorRepairValue yst out left right = 0 then
    pointAddUnequalDenominatorRaw yst out left right
  else pointAddUnequalDenominatorRepaired yst out left right

def pointAddUnequalDenominatorSelectedEnv (yst : EvmState)
    (out left right : U256) : VEnv Challenge.EvmProof.modexpExec.toDialect :=
  [("fc0_74", (pointAddUnequalDenominatorResult yst out left right).1),
   ("fc0_75", (pointAddUnequalDenominatorResult yst out left right).2)] ++
    pointAddUnequalDenominatorInitialEnv yst out left right

private theorem rawEnv_eq (yst : EvmState) (out left right : U256) :
    pointAddUnequalDenominatorRawEnv yst out left right =
      [("fc0_74", (pointAddUnequalDenominatorRaw yst out left right).1),
       ("fc0_75", (pointAddUnequalDenominatorRaw yst out left right).2)] ++
        pointAddUnequalDenominatorInitialEnv yst out left right := by
  rfl

private theorem exec_pointAddUnequalDenominatorRepair (yst : EvmState)
    (out left right : U256) :
    Interp.execStmt Challenge.EvmProof.modexpExec 40
      ([] :: pointAddBodyFuns)
      (pointAddUnequalDenominatorRawEnv yst out left right)
      (pointAddUnequalDenominatorInputsState yst out left right)
      pointAddUnequalDenominatorRepairStmt =
    .ok (pointAddUnequalDenominatorSelectedEnv yst out left right,
      pointAddUnequalDenominatorInputsState yst out left right, .normal) := by
  rw [pointAddUnequalDenominatorRepairStmt_eq]
  by_cases h : pointAddUnequalDenominatorRepairValue yst out left right = 0
  · have h' : b2w (BitVec.ult
        (BitVec.ofNat 256 34565483545414906068789196026815425751)
        (pointAddUnequalDenominatorRaw yst out left right).1) = (0 : U256) := by
      simpa [pointAddUnequalDenominatorRepairValue,
        Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpSubNeedsRepairValue]
        using h
    rw [pointAddUnequalDenominatorSelectedEnv,
      pointAddUnequalDenominatorResult, if_pos h]
    simp [Interp.execStmt, Interp.execStmts, Interp.evalExpr, Interp.evalArgs,
      Challenge.EvmProof.modexpExec, Challenge.EvmProof.modexpBuiltinFn,
      stepOp, bin, EVM.litValue, Dialect.zero, VEnv.get, VEnv.setMany,
      VEnv.set, restore, rawEnv_eq, h']
  · have h' : b2w (BitVec.ult
        (BitVec.ofNat 256 34565483545414906068789196026815425751)
        (pointAddUnequalDenominatorRaw yst out left right).1) ≠ (0 : U256) := by
      simpa [pointAddUnequalDenominatorRepairValue,
        Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpSubNeedsRepairValue]
        using h
    rw [pointAddUnequalDenominatorSelectedEnv,
      pointAddUnequalDenominatorResult, if_neg h]
    simp [Interp.execStmt, Interp.execStmts, Interp.evalExpr, Interp.evalArgs,
      Challenge.EvmProof.modexpExec, Challenge.EvmProof.modexpBuiltinFn,
      stepOp, bin, EVM.litValue, Dialect.zero, VEnv.get, VEnv.setMany,
      VEnv.set, restore, rawEnv_eq, pointAddUnequalDenominatorRepaired]
    exact h'

theorem step_pointAddUnequalDenominatorRepair (yst : EvmState)
    (out left right : U256) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect
      ([] :: pointAddBodyFuns)
      (pointAddUnequalDenominatorRawEnv yst out left right)
      (pointAddUnequalDenominatorInputsState yst out left right)
      pointAddUnequalDenominatorRepairStmt
      (pointAddUnequalDenominatorSelectedEnv yst out left right)
      (pointAddUnequalDenominatorInputsState yst out left right) .normal :=
  (Interp.sound_all_of (E := Challenge.EvmProof.modexpExec)
    (fun _ _ _ _ hb => Challenge.EvmProof.modexpBuiltinFn_sound hb) 40).2.2.1
    _ _ _ _ _ _ _ (exec_pointAddUnequalDenominatorRepair yst out left right)

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
