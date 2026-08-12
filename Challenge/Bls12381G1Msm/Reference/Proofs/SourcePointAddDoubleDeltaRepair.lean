import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddDoubleDeltaRaw
import Challenge.EvmProof.ExecSound

set_option warningAsError true

/-! Conditional modulus repair for the generic delta subtraction. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

private abbrev fpSubNeedsRepairValue :=
  Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpSubNeedsRepairValue

def pointAddDoubleDeltaRepairValue (ctx : PointAddDoubleDeltaContext) : U256 :=
  fpSubNeedsRepairValue (pointAddDoubleDeltaRaw ctx)

def pointAddDoubleDeltaRepaired (ctx : PointAddDoubleDeltaContext) : U256 × U256 :=
  let newLo := (pointAddDoubleDeltaRaw ctx).2 + BitVec.ofNat 256
    45442060874369865957053122457065728162598490762543039060009208264153100167851
  ((pointAddDoubleDeltaRaw ctx).1 +
      (BitVec.ofNat 256 34565483545414906068789196026815425751 +
        b2w (BitVec.ult newLo (pointAddDoubleDeltaRaw ctx).2)),
    newLo)

def pointAddDoubleDeltaResult (ctx : PointAddDoubleDeltaContext) : U256 × U256 :=
  if pointAddDoubleDeltaRepairValue ctx = 0 then pointAddDoubleDeltaRaw ctx
  else pointAddDoubleDeltaRepaired ctx

def pointAddDoubleDeltaSelectedEnv (ctx : PointAddDoubleDeltaContext) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  [("fc0_42", (pointAddDoubleDeltaResult ctx).1),
   ("fc0_43", (pointAddDoubleDeltaResult ctx).2)] ++ ctx.env

theorem pointAddDoubleDeltaSelectedEnv_hi (ctx : PointAddDoubleDeltaContext) :
    VEnv.get (pointAddDoubleDeltaSelectedEnv ctx) "fc0_42" =
      some (pointAddDoubleDeltaResult ctx).1 := by rfl

theorem pointAddDoubleDeltaSelectedEnv_lo (ctx : PointAddDoubleDeltaContext) :
    VEnv.get (pointAddDoubleDeltaSelectedEnv ctx) "fc0_43" =
      some (pointAddDoubleDeltaResult ctx).2 := by rfl

theorem exec_pointAddDoubleDeltaRepairGeneric
    (ctx : PointAddDoubleDeltaContext) :
    Interp.execStmt Challenge.EvmProof.modexpExec 40
      ([] :: pointAddBodyFuns) (pointAddDoubleDeltaRawEnv ctx)
      (pointAddDoubleDeltaRawState ctx) pointAddDoubleDeltaRepairStmt =
    .ok (pointAddDoubleDeltaSelectedEnv ctx,
      pointAddDoubleDeltaRawState ctx, .normal) := by
  rw [pointAddDoubleDeltaRepairStmt_eq]
  by_cases h : pointAddDoubleDeltaRepairValue ctx = 0
  · have h' : b2w (BitVec.ult
        (BitVec.ofNat 256 34565483545414906068789196026815425751)
        (pointAddDoubleDeltaRaw ctx).1) = (0 : U256) := by
      simpa [pointAddDoubleDeltaRepairValue,
        Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpSubNeedsRepairValue]
        using h
    rw [pointAddDoubleDeltaSelectedEnv, pointAddDoubleDeltaResult, if_pos h]
    simp [Interp.execStmt, Interp.execStmts, Interp.evalExpr, Interp.evalArgs,
      Challenge.EvmProof.modexpExec, Challenge.EvmProof.modexpBuiltinFn,
      stepOp, bin, EVM.litValue, Dialect.zero, VEnv.get, VEnv.setMany,
      VEnv.set, restore, pointAddDoubleDeltaRawEnv, h']
  · have h' : b2w (BitVec.ult
        (BitVec.ofNat 256 34565483545414906068789196026815425751)
        (pointAddDoubleDeltaRaw ctx).1) ≠ (0 : U256) := by
      simpa [pointAddDoubleDeltaRepairValue,
        Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpSubNeedsRepairValue]
        using h
    rw [pointAddDoubleDeltaSelectedEnv, pointAddDoubleDeltaResult, if_neg h]
    simp [Interp.execStmt, Interp.execStmts, Interp.evalExpr, Interp.evalArgs,
      Challenge.EvmProof.modexpExec, Challenge.EvmProof.modexpBuiltinFn,
      stepOp, bin, EVM.litValue, Dialect.zero, VEnv.get, VEnv.setMany,
      VEnv.set, restore, pointAddDoubleDeltaRawEnv,
      pointAddDoubleDeltaRepaired]
    exact h'

theorem step_pointAddDoubleDeltaRepairGeneric
    (ctx : PointAddDoubleDeltaContext) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect
      ([] :: pointAddBodyFuns) (pointAddDoubleDeltaRawEnv ctx)
      (pointAddDoubleDeltaRawState ctx) pointAddDoubleDeltaRepairStmt
      (pointAddDoubleDeltaSelectedEnv ctx)
      (pointAddDoubleDeltaRawState ctx) .normal :=
  (Interp.sound_all_of (E := Challenge.EvmProof.modexpExec)
    (fun _ _ _ _ hb => Challenge.EvmProof.modexpBuiltinFn_sound hb) 40).2.2.1
    _ _ _ _ _ _ _ (exec_pointAddDoubleDeltaRepairGeneric ctx)

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
