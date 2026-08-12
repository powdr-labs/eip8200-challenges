import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalDeltaRaw
import Challenge.EvmProof.ExecSound

set_option warningAsError true

/-! Conditional modulus repair for the generic delta subtraction. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

private abbrev fpSubNeedsRepairValue :=
  Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpSubNeedsRepairValue

def pointAddUnequalDeltaRepairValue (ctx : PointAddUnequalDeltaContext) : U256 :=
  fpSubNeedsRepairValue (pointAddUnequalDeltaRaw ctx)

def pointAddUnequalDeltaRepaired (ctx : PointAddUnequalDeltaContext) : U256 × U256 :=
  let newLo := (pointAddUnequalDeltaRaw ctx).2 + BitVec.ofNat 256
    45442060874369865957053122457065728162598490762543039060009208264153100167851
  ((pointAddUnequalDeltaRaw ctx).1 +
      (BitVec.ofNat 256 34565483545414906068789196026815425751 +
        b2w (BitVec.ult newLo (pointAddUnequalDeltaRaw ctx).2)),
    newLo)

def pointAddUnequalDeltaResult (ctx : PointAddUnequalDeltaContext) : U256 × U256 :=
  if pointAddUnequalDeltaRepairValue ctx = 0 then pointAddUnequalDeltaRaw ctx
  else pointAddUnequalDeltaRepaired ctx

def pointAddUnequalDeltaSelectedEnv (ctx : PointAddUnequalDeltaContext) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  [("fc0_95", (pointAddUnequalDeltaResult ctx).1),
   ("fc0_96", (pointAddUnequalDeltaResult ctx).2)] ++ ctx.env

theorem pointAddUnequalDeltaSelectedEnv_hi (ctx : PointAddUnequalDeltaContext) :
    VEnv.get (pointAddUnequalDeltaSelectedEnv ctx) "fc0_95" =
      some (pointAddUnequalDeltaResult ctx).1 := by rfl

theorem pointAddUnequalDeltaSelectedEnv_lo (ctx : PointAddUnequalDeltaContext) :
    VEnv.get (pointAddUnequalDeltaSelectedEnv ctx) "fc0_96" =
      some (pointAddUnequalDeltaResult ctx).2 := by rfl

theorem exec_pointAddUnequalDeltaRepairGeneric
    (ctx : PointAddUnequalDeltaContext) :
    Interp.execStmt Challenge.EvmProof.modexpExec 40
      ([] :: pointAddBodyFuns) (pointAddUnequalDeltaRawEnv ctx)
      (pointAddUnequalDeltaRawState ctx) pointAddUnequalDeltaRepairStmt =
    .ok (pointAddUnequalDeltaSelectedEnv ctx,
      pointAddUnequalDeltaRawState ctx, .normal) := by
  rw [pointAddUnequalDeltaRepairStmt_eq]
  by_cases h : pointAddUnequalDeltaRepairValue ctx = 0
  · have h' : b2w (BitVec.ult
        (BitVec.ofNat 256 34565483545414906068789196026815425751)
        (pointAddUnequalDeltaRaw ctx).1) = (0 : U256) := by
      simpa [pointAddUnequalDeltaRepairValue,
        Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpSubNeedsRepairValue]
        using h
    rw [pointAddUnequalDeltaSelectedEnv, pointAddUnequalDeltaResult, if_pos h]
    simp [Interp.execStmt, Interp.execStmts, Interp.evalExpr, Interp.evalArgs,
      Challenge.EvmProof.modexpExec, Challenge.EvmProof.modexpBuiltinFn,
      stepOp, bin, EVM.litValue, Dialect.zero, VEnv.get, VEnv.setMany,
      VEnv.set, restore, pointAddUnequalDeltaRawEnv, h']
  · have h' : b2w (BitVec.ult
        (BitVec.ofNat 256 34565483545414906068789196026815425751)
        (pointAddUnequalDeltaRaw ctx).1) ≠ (0 : U256) := by
      simpa [pointAddUnequalDeltaRepairValue,
        Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpSubNeedsRepairValue]
        using h
    rw [pointAddUnequalDeltaSelectedEnv, pointAddUnequalDeltaResult, if_neg h]
    simp [Interp.execStmt, Interp.execStmts, Interp.evalExpr, Interp.evalArgs,
      Challenge.EvmProof.modexpExec, Challenge.EvmProof.modexpBuiltinFn,
      stepOp, bin, EVM.litValue, Dialect.zero, VEnv.get, VEnv.setMany,
      VEnv.set, restore, pointAddUnequalDeltaRawEnv,
      pointAddUnequalDeltaRepaired]
    exact h'

theorem step_pointAddUnequalDeltaRepairGeneric
    (ctx : PointAddUnequalDeltaContext) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect
      ([] :: pointAddBodyFuns) (pointAddUnequalDeltaRawEnv ctx)
      (pointAddUnequalDeltaRawState ctx) pointAddUnequalDeltaRepairStmt
      (pointAddUnequalDeltaSelectedEnv ctx)
      (pointAddUnequalDeltaRawState ctx) .normal :=
  (Interp.sound_all_of (E := Challenge.EvmProof.modexpExec)
    (fun _ _ _ _ hb => Challenge.EvmProof.modexpBuiltinFn_sound hb) 40).2.2.1
    _ _ _ _ _ _ _ (exec_pointAddUnequalDeltaRepairGeneric ctx)

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
