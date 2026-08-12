import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddDoubleYSubRaw
import Challenge.EvmProof.ExecSound

set_option warningAsError true

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

private abbrev fpSubNeedsRepairValue :=
  Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpSubNeedsRepairValue

def pointAddDoubleYSubRepairValue (ctx : PointAddDoubleYSubContext) : U256 :=
  fpSubNeedsRepairValue (pointAddDoubleYSubRaw ctx)
def pointAddDoubleYSubRepaired (ctx : PointAddDoubleYSubContext) : U256 × U256 :=
  let newLo := (pointAddDoubleYSubRaw ctx).2 + BitVec.ofNat 256
    45442060874369865957053122457065728162598490762543039060009208264153100167851
  ((pointAddDoubleYSubRaw ctx).1 +
      (BitVec.ofNat 256 34565483545414906068789196026815425751 +
        b2w (BitVec.ult newLo (pointAddDoubleYSubRaw ctx).2)), newLo)
def pointAddDoubleYSubResult (ctx : PointAddDoubleYSubContext) : U256 × U256 :=
  if pointAddDoubleYSubRepairValue ctx = 0 then pointAddDoubleYSubRaw ctx
  else pointAddDoubleYSubRepaired ctx
def pointAddDoubleYSubSelectedEnv (ctx : PointAddDoubleYSubContext) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  [("fc0_49", (pointAddDoubleYSubResult ctx).1),
   ("fc0_50", (pointAddDoubleYSubResult ctx).2)] ++ ctx.env

theorem pointAddDoubleYSubSelectedEnv_hi (ctx : PointAddDoubleYSubContext) :
    VEnv.get (pointAddDoubleYSubSelectedEnv ctx) "fc0_49" =
      some (pointAddDoubleYSubResult ctx).1 := by rfl
theorem pointAddDoubleYSubSelectedEnv_lo (ctx : PointAddDoubleYSubContext) :
    VEnv.get (pointAddDoubleYSubSelectedEnv ctx) "fc0_50" =
      some (pointAddDoubleYSubResult ctx).2 := by rfl

theorem exec_pointAddDoubleYSubRepairGeneric (ctx : PointAddDoubleYSubContext) :
    Interp.execStmt Challenge.EvmProof.modexpExec 40
      ([] :: pointAddBodyFuns) (pointAddDoubleYSubRawEnv ctx)
      (pointAddDoubleYSubRawState ctx) pointAddDoubleYSubRepairStmt =
    .ok (pointAddDoubleYSubSelectedEnv ctx, pointAddDoubleYSubRawState ctx,
      .normal) := by
  rw [pointAddDoubleYSubRepairStmt_eq]
  by_cases h : pointAddDoubleYSubRepairValue ctx = 0
  · have h' : b2w (BitVec.ult
        (BitVec.ofNat 256 34565483545414906068789196026815425751)
        (pointAddDoubleYSubRaw ctx).1) = (0 : U256) := by
      simpa [pointAddDoubleYSubRepairValue,
        Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpSubNeedsRepairValue]
        using h
    rw [pointAddDoubleYSubSelectedEnv, pointAddDoubleYSubResult, if_pos h]
    simp [Interp.execStmt, Interp.execStmts, Interp.evalExpr, Interp.evalArgs,
      Challenge.EvmProof.modexpExec, Challenge.EvmProof.modexpBuiltinFn,
      stepOp, bin, EVM.litValue, Dialect.zero, VEnv.get, VEnv.setMany,
      VEnv.set, restore, pointAddDoubleYSubRawEnv, h']
  · have h' : b2w (BitVec.ult
        (BitVec.ofNat 256 34565483545414906068789196026815425751)
        (pointAddDoubleYSubRaw ctx).1) ≠ (0 : U256) := by
      simpa [pointAddDoubleYSubRepairValue,
        Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpSubNeedsRepairValue]
        using h
    rw [pointAddDoubleYSubSelectedEnv, pointAddDoubleYSubResult, if_neg h]
    simp [Interp.execStmt, Interp.execStmts, Interp.evalExpr, Interp.evalArgs,
      Challenge.EvmProof.modexpExec, Challenge.EvmProof.modexpBuiltinFn,
      stepOp, bin, EVM.litValue, Dialect.zero, VEnv.get, VEnv.setMany,
      VEnv.set, restore, pointAddDoubleYSubRawEnv, pointAddDoubleYSubRepaired]
    exact h'

theorem step_pointAddDoubleYSubRepairGeneric (ctx : PointAddDoubleYSubContext) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect
      ([] :: pointAddBodyFuns) (pointAddDoubleYSubRawEnv ctx)
      (pointAddDoubleYSubRawState ctx) pointAddDoubleYSubRepairStmt
      (pointAddDoubleYSubSelectedEnv ctx) (pointAddDoubleYSubRawState ctx)
      .normal :=
  (Interp.sound_all_of (E := Challenge.EvmProof.modexpExec)
    (fun _ _ _ _ hb => Challenge.EvmProof.modexpBuiltinFn_sound hb) 40).2.2.1
    _ _ _ _ _ _ _ (exec_pointAddDoubleYSubRepairGeneric ctx)

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
