import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalNumeratorRaw
import Challenge.EvmProof.ExecSound

set_option warningAsError true

/-! Conditional modulus repair for the unequal numerator. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

private abbrev fpSubNeedsRepairValue :=
  Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpSubNeedsRepairValue

def pointAddUnequalNumeratorRepairValue (yst : EvmState)
    (out left right : U256) : U256 :=
  fpSubNeedsRepairValue (pointAddUnequalNumeratorRaw yst out left right)

def pointAddUnequalNumeratorRepaired (yst : EvmState)
    (out left right : U256) : U256 × U256 :=
  let raw := pointAddUnequalNumeratorRaw yst out left right
  let newLo := raw.2 + BitVec.ofNat 256
    45442060874369865957053122457065728162598490762543039060009208264153100167851
  (raw.1 + (BitVec.ofNat 256 34565483545414906068789196026815425751 +
      b2w (BitVec.ult newLo raw.2)), newLo)

def pointAddUnequalNumeratorResult (yst : EvmState)
    (out left right : U256) : U256 × U256 :=
  if pointAddUnequalNumeratorRepairValue yst out left right = 0 then
    pointAddUnequalNumeratorRaw yst out left right
  else pointAddUnequalNumeratorRepaired yst out left right

def pointAddUnequalNumeratorSelectedEnv (yst : EvmState)
    (out left right : U256) : VEnv Challenge.EvmProof.modexpExec.toDialect :=
  [("fc0_67", (pointAddUnequalNumeratorResult yst out left right).1),
   ("fc0_68", (pointAddUnequalNumeratorResult yst out left right).2)] ++
    pointAddUnequalNumeratorInitialEnv out left right

private theorem rawEnv_eq (yst : EvmState) (out left right : U256) :
    pointAddUnequalNumeratorRawEnv yst out left right =
      [("fc0_67", (pointAddUnequalNumeratorRaw yst out left right).1),
       ("fc0_68", (pointAddUnequalNumeratorRaw yst out left right).2)] ++
        pointAddUnequalNumeratorInitialEnv out left right := by
  rfl

private theorem exec_pointAddUnequalNumeratorRepair (yst : EvmState)
    (out left right : U256) :
    Interp.execStmt Challenge.EvmProof.modexpExec 40
      ([] :: pointAddBodyFuns)
      (pointAddUnequalNumeratorRawEnv yst out left right)
      (pointAddUnequalNumeratorInputsState yst out left right)
      pointAddUnequalNumeratorRepairStmt =
    .ok (pointAddUnequalNumeratorSelectedEnv yst out left right,
      pointAddUnequalNumeratorInputsState yst out left right, .normal) := by
  rw [pointAddUnequalNumeratorRepairStmt_eq]
  by_cases h : pointAddUnequalNumeratorRepairValue yst out left right = 0
  · have h' : b2w (BitVec.ult
        (BitVec.ofNat 256 34565483545414906068789196026815425751)
        (pointAddUnequalNumeratorRaw yst out left right).1) = (0 : U256) := by
      simpa [pointAddUnequalNumeratorRepairValue,
        Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpSubNeedsRepairValue]
        using h
    rw [pointAddUnequalNumeratorSelectedEnv,
      pointAddUnequalNumeratorResult, if_pos h]
    simp [Interp.execStmt, Interp.execStmts, Interp.evalExpr, Interp.evalArgs,
      Challenge.EvmProof.modexpExec, Challenge.EvmProof.modexpBuiltinFn,
      stepOp, bin, EVM.litValue, Dialect.zero, VEnv.get, VEnv.setMany,
      VEnv.set, restore, rawEnv_eq, h']
  · have h' : b2w (BitVec.ult
        (BitVec.ofNat 256 34565483545414906068789196026815425751)
        (pointAddUnequalNumeratorRaw yst out left right).1) ≠ (0 : U256) := by
      simpa [pointAddUnequalNumeratorRepairValue,
        Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpSubNeedsRepairValue]
        using h
    rw [pointAddUnequalNumeratorSelectedEnv,
      pointAddUnequalNumeratorResult, if_neg h]
    simp [Interp.execStmt, Interp.execStmts, Interp.evalExpr, Interp.evalArgs,
      Challenge.EvmProof.modexpExec, Challenge.EvmProof.modexpBuiltinFn,
      stepOp, bin, EVM.litValue, Dialect.zero, VEnv.get, VEnv.setMany,
      VEnv.set, restore, rawEnv_eq, pointAddUnequalNumeratorRepaired]
    exact h'

theorem step_pointAddUnequalNumeratorRepair (yst : EvmState)
    (out left right : U256) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect
      ([] :: pointAddBodyFuns)
      (pointAddUnequalNumeratorRawEnv yst out left right)
      (pointAddUnequalNumeratorInputsState yst out left right)
      pointAddUnequalNumeratorRepairStmt
      (pointAddUnequalNumeratorSelectedEnv yst out left right)
      (pointAddUnequalNumeratorInputsState yst out left right) .normal :=
  (Interp.sound_all_of (E := Challenge.EvmProof.modexpExec)
    (fun _ _ _ _ hb => Challenge.EvmProof.modexpBuiltinFn_sound hb) 40).2.2.1
    _ _ _ _ _ _ _ (exec_pointAddUnequalNumeratorRepair yst out left right)

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
