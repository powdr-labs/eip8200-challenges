import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddDoubleXSubRightRaw
import Challenge.EvmProof.ExecSound

set_option warningAsError true

/-! Generic conditional modulus repair of the second point-double x subtraction. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

private abbrev fpSubNeedsRepairValue :=
  Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpSubNeedsRepairValue

def pointAddDoubleXSubRightRepairValue (ctx : PointAddDoubleXSubRightContext) :
    U256 :=
  fpSubNeedsRepairValue (pointAddDoubleXSubRightRaw ctx)

def pointAddDoubleXSubRightRepaired (ctx : PointAddDoubleXSubRightContext) :
    U256 × U256 :=
  let newLo := (pointAddDoubleXSubRightRaw ctx).2 + BitVec.ofNat 256
    45442060874369865957053122457065728162598490762543039060009208264153100167851
  ((pointAddDoubleXSubRightRaw ctx).1 +
      (BitVec.ofNat 256 34565483545414906068789196026815425751 +
        b2w (BitVec.ult newLo (pointAddDoubleXSubRightRaw ctx).2)),
    newLo)

def pointAddDoubleXSubRightResult (ctx : PointAddDoubleXSubRightContext) :
    U256 × U256 :=
  if pointAddDoubleXSubRightRepairValue ctx = 0 then
    pointAddDoubleXSubRightRaw ctx
  else pointAddDoubleXSubRightRepaired ctx

def pointAddDoubleXSubRightSelectedEnv (ctx : PointAddDoubleXSubRightContext) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  [("fc0_35", (pointAddDoubleXSubRightResult ctx).1),
   ("fc0_36", (pointAddDoubleXSubRightResult ctx).2)] ++ ctx.env

theorem pointAddDoubleXSubRightSelectedEnv_hi
    (ctx : PointAddDoubleXSubRightContext) :
    VEnv.get (pointAddDoubleXSubRightSelectedEnv ctx) "fc0_35" =
      some (pointAddDoubleXSubRightResult ctx).1 := by rfl

theorem pointAddDoubleXSubRightSelectedEnv_lo
    (ctx : PointAddDoubleXSubRightContext) :
    VEnv.get (pointAddDoubleXSubRightSelectedEnv ctx) "fc0_36" =
      some (pointAddDoubleXSubRightResult ctx).2 := by rfl

theorem exec_pointAddDoubleXSubRightRepairGeneric
    (ctx : PointAddDoubleXSubRightContext) :
    Interp.execStmt Challenge.EvmProof.modexpExec 40
      ([] :: pointAddBodyFuns) (pointAddDoubleXSubRightRawEnv ctx)
      (pointAddDoubleXSubRightRawState ctx) pointAddDoubleXSubRightRepairStmt =
    .ok (pointAddDoubleXSubRightSelectedEnv ctx,
      pointAddDoubleXSubRightRawState ctx, .normal) := by
  rw [pointAddDoubleXSubRightRepairStmt_eq]
  by_cases h : pointAddDoubleXSubRightRepairValue ctx = 0
  · have h' : b2w (BitVec.ult
        (BitVec.ofNat 256 34565483545414906068789196026815425751)
        (pointAddDoubleXSubRightRaw ctx).1) = (0 : U256) := by
      simpa [pointAddDoubleXSubRightRepairValue,
        Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpSubNeedsRepairValue]
        using h
    rw [pointAddDoubleXSubRightSelectedEnv,
      pointAddDoubleXSubRightResult, if_pos h]
    simp [Interp.execStmt, Interp.execStmts, Interp.evalExpr, Interp.evalArgs,
      Challenge.EvmProof.modexpExec, Challenge.EvmProof.modexpBuiltinFn,
      stepOp, bin, EVM.litValue, Dialect.zero, VEnv.get, VEnv.setMany,
      VEnv.set, restore, pointAddDoubleXSubRightRawEnv, h']
  · have h' : b2w (BitVec.ult
        (BitVec.ofNat 256 34565483545414906068789196026815425751)
        (pointAddDoubleXSubRightRaw ctx).1) ≠ (0 : U256) := by
      simpa [pointAddDoubleXSubRightRepairValue,
        Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpSubNeedsRepairValue]
        using h
    rw [pointAddDoubleXSubRightSelectedEnv,
      pointAddDoubleXSubRightResult, if_neg h]
    simp [Interp.execStmt, Interp.execStmts, Interp.evalExpr, Interp.evalArgs,
      Challenge.EvmProof.modexpExec, Challenge.EvmProof.modexpBuiltinFn,
      stepOp, bin, EVM.litValue, Dialect.zero, VEnv.get, VEnv.setMany,
      VEnv.set, restore, pointAddDoubleXSubRightRawEnv,
      pointAddDoubleXSubRightRepaired]
    exact h'

theorem step_pointAddDoubleXSubRightRepairGeneric
    (ctx : PointAddDoubleXSubRightContext) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect
      ([] :: pointAddBodyFuns) (pointAddDoubleXSubRightRawEnv ctx)
      (pointAddDoubleXSubRightRawState ctx) pointAddDoubleXSubRightRepairStmt
      (pointAddDoubleXSubRightSelectedEnv ctx)
      (pointAddDoubleXSubRightRawState ctx) .normal :=
  (Interp.sound_all_of (E := Challenge.EvmProof.modexpExec)
    (fun _ _ _ _ hb => Challenge.EvmProof.modexpBuiltinFn_sound hb) 40).2.2.1
    _ _ _ _ _ _ _ (exec_pointAddDoubleXSubRightRepairGeneric ctx)

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
