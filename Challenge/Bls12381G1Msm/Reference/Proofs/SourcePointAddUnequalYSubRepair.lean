import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalYSubRaw
import Challenge.EvmProof.ExecSound

set_option warningAsError true

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

private abbrev fpSubNeedsRepairValue :=
  Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpSubNeedsRepairValue

def pointAddUnequalYSubRepairValue (ctx : PointAddUnequalYSubContext) : U256 :=
  fpSubNeedsRepairValue (pointAddUnequalYSubRaw ctx)
def pointAddUnequalYSubRepaired (ctx : PointAddUnequalYSubContext) : U256 × U256 :=
  let newLo := (pointAddUnequalYSubRaw ctx).2 + BitVec.ofNat 256
    45442060874369865957053122457065728162598490762543039060009208264153100167851
  ((pointAddUnequalYSubRaw ctx).1 +
      (BitVec.ofNat 256 34565483545414906068789196026815425751 +
        b2w (BitVec.ult newLo (pointAddUnequalYSubRaw ctx).2)), newLo)
def pointAddUnequalYSubResult (ctx : PointAddUnequalYSubContext) : U256 × U256 :=
  if pointAddUnequalYSubRepairValue ctx = 0 then pointAddUnequalYSubRaw ctx
  else pointAddUnequalYSubRepaired ctx
def pointAddUnequalYSubSelectedEnv (ctx : PointAddUnequalYSubContext) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  [("fc0_102", (pointAddUnequalYSubResult ctx).1),
   ("fc0_103", (pointAddUnequalYSubResult ctx).2)] ++ ctx.env

theorem pointAddUnequalYSubSelectedEnv_hi (ctx : PointAddUnequalYSubContext) :
    VEnv.get (pointAddUnequalYSubSelectedEnv ctx) "fc0_102" =
      some (pointAddUnequalYSubResult ctx).1 := by rfl
theorem pointAddUnequalYSubSelectedEnv_lo (ctx : PointAddUnequalYSubContext) :
    VEnv.get (pointAddUnequalYSubSelectedEnv ctx) "fc0_103" =
      some (pointAddUnequalYSubResult ctx).2 := by rfl

theorem exec_pointAddUnequalYSubRepairGeneric (ctx : PointAddUnequalYSubContext) :
    Interp.execStmt Challenge.EvmProof.modexpExec 40
      ([] :: pointAddBodyFuns) (pointAddUnequalYSubRawEnv ctx)
      (pointAddUnequalYSubRawState ctx) pointAddUnequalYSubRepairStmt =
    .ok (pointAddUnequalYSubSelectedEnv ctx, pointAddUnequalYSubRawState ctx,
      .normal) := by
  rw [pointAddUnequalYSubRepairStmt_eq]
  by_cases h : pointAddUnequalYSubRepairValue ctx = 0
  · have h' : b2w (BitVec.ult
        (BitVec.ofNat 256 34565483545414906068789196026815425751)
        (pointAddUnequalYSubRaw ctx).1) = (0 : U256) := by
      simpa [pointAddUnequalYSubRepairValue,
        Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpSubNeedsRepairValue]
        using h
    rw [pointAddUnequalYSubSelectedEnv, pointAddUnequalYSubResult, if_pos h]
    simp [Interp.execStmt, Interp.execStmts, Interp.evalExpr, Interp.evalArgs,
      Challenge.EvmProof.modexpExec, Challenge.EvmProof.modexpBuiltinFn,
      stepOp, bin, EVM.litValue, Dialect.zero, VEnv.get, VEnv.setMany,
      VEnv.set, restore, pointAddUnequalYSubRawEnv, h']
  · have h' : b2w (BitVec.ult
        (BitVec.ofNat 256 34565483545414906068789196026815425751)
        (pointAddUnequalYSubRaw ctx).1) ≠ (0 : U256) := by
      simpa [pointAddUnequalYSubRepairValue,
        Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpSubNeedsRepairValue]
        using h
    rw [pointAddUnequalYSubSelectedEnv, pointAddUnequalYSubResult, if_neg h]
    simp [Interp.execStmt, Interp.execStmts, Interp.evalExpr, Interp.evalArgs,
      Challenge.EvmProof.modexpExec, Challenge.EvmProof.modexpBuiltinFn,
      stepOp, bin, EVM.litValue, Dialect.zero, VEnv.get, VEnv.setMany,
      VEnv.set, restore, pointAddUnequalYSubRawEnv, pointAddUnequalYSubRepaired]
    exact h'

theorem step_pointAddUnequalYSubRepairGeneric (ctx : PointAddUnequalYSubContext) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect
      ([] :: pointAddBodyFuns) (pointAddUnequalYSubRawEnv ctx)
      (pointAddUnequalYSubRawState ctx) pointAddUnequalYSubRepairStmt
      (pointAddUnequalYSubSelectedEnv ctx) (pointAddUnequalYSubRawState ctx)
      .normal :=
  (Interp.sound_all_of (E := Challenge.EvmProof.modexpExec)
    (fun _ _ _ _ hb => Challenge.EvmProof.modexpBuiltinFn_sound hb) 40).2.2.1
    _ _ _ _ _ _ _ (exec_pointAddUnequalYSubRepairGeneric ctx)

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
