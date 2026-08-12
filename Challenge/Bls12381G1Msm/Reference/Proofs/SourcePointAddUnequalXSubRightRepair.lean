import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalXSubRightRaw
import Challenge.EvmProof.ExecSound

set_option warningAsError true

/-! Generic conditional modulus repair of the second unequal-point x subtraction. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM
open Challenge.Bls12381.ProofSupport

private abbrev fpSubNeedsRepairValue :=
  Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpSubNeedsRepairValue

def pointAddUnequalXSubRightRepairValue (ctx : PointAddUnequalXSubRightContext) :
    U256 :=
  fpSubNeedsRepairValue (pointAddUnequalXSubRightRaw ctx)

def pointAddUnequalXSubRightRepaired (ctx : PointAddUnequalXSubRightContext) :
    U256 × U256 :=
  let newLo := (pointAddUnequalXSubRightRaw ctx).2 + BitVec.ofNat 256
    45442060874369865957053122457065728162598490762543039060009208264153100167851
  ((pointAddUnequalXSubRightRaw ctx).1 +
      (BitVec.ofNat 256 34565483545414906068789196026815425751 +
        b2w (BitVec.ult newLo (pointAddUnequalXSubRightRaw ctx).2)),
    newLo)

def pointAddUnequalXSubRightResult (ctx : PointAddUnequalXSubRightContext) :
    U256 × U256 :=
  if pointAddUnequalXSubRightRepairValue ctx = 0 then
    pointAddUnequalXSubRightRaw ctx
  else pointAddUnequalXSubRightRepaired ctx

theorem pointAddUnequalXSubRightResult_eq_fpSubValue
    (ctx : PointAddUnequalXSubRightContext) :
    pointAddUnequalXSubRightResult ctx =
      Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpSubValue
        ctx.x3Hi ctx.x3Lo (pointAddUnequalXSubRightHi ctx)
        (pointAddUnequalXSubRightLo ctx) := by
  simp only [pointAddUnequalXSubRightResult,
    pointAddUnequalXSubRightRepairValue,
    pointAddUnequalXSubRightRepaired,
    pointAddUnequalXSubRightRaw,
    pointAddUnequalXSubRightRawHi,
    pointAddUnequalXSubRightRawLo,
    Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpSubValue,
    Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpSubRawValue,
    Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpSubRepairValue,
    Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpSubNeedsRepairValue,
    add_assoc]

def pointAddUnequalXSubRightResultLimbs
    (ctx : PointAddUnequalXSubRightContext) : Fp.Limbs :=
  { hi := YulEvmCompiler.conv (pointAddUnequalXSubRightResult ctx).1
    lo := YulEvmCompiler.conv (pointAddUnequalXSubRightResult ctx).2 }

def pointAddUnequalXSubRightLeftLimbs
    (ctx : PointAddUnequalXSubRightContext) : Fp.Limbs :=
  { hi := YulEvmCompiler.conv ctx.x3Hi
    lo := YulEvmCompiler.conv ctx.x3Lo }

def pointAddUnequalXSubRightOperandLimbs
    (ctx : PointAddUnequalXSubRightContext) : Fp.Limbs :=
  { hi := YulEvmCompiler.conv (pointAddUnequalXSubRightHi ctx)
    lo := YulEvmCompiler.conv (pointAddUnequalXSubRightLo ctx) }

theorem pointAddUnequalXSubRightResultLimbs_eq (ctx :
    PointAddUnequalXSubRightContext) :
    pointAddUnequalXSubRightResultLimbs ctx =
      Fp.subSource (pointAddUnequalXSubRightLeftLimbs ctx)
        (pointAddUnequalXSubRightOperandLimbs ctx) := by
  rw [pointAddUnequalXSubRightResultLimbs,
    pointAddUnequalXSubRightResult_eq_fpSubValue]
  simpa only [pointAddUnequalXSubRightLeftLimbs,
    pointAddUnequalXSubRightOperandLimbs,
    Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.convPair]
    using Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.conv_fpSubValue
      ctx.x3Hi ctx.x3Lo (pointAddUnequalXSubRightHi ctx)
      (pointAddUnequalXSubRightLo ctx)

def pointAddUnequalXSubRightSelectedEnv (ctx : PointAddUnequalXSubRightContext) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  [("fc0_88", (pointAddUnequalXSubRightResult ctx).1),
   ("fc0_89", (pointAddUnequalXSubRightResult ctx).2)] ++ ctx.env

theorem pointAddUnequalXSubRightSelectedEnv_hi
    (ctx : PointAddUnequalXSubRightContext) :
    VEnv.get (pointAddUnequalXSubRightSelectedEnv ctx) "fc0_88" =
      some (pointAddUnequalXSubRightResult ctx).1 := by rfl

theorem pointAddUnequalXSubRightSelectedEnv_lo
    (ctx : PointAddUnequalXSubRightContext) :
    VEnv.get (pointAddUnequalXSubRightSelectedEnv ctx) "fc0_89" =
      some (pointAddUnequalXSubRightResult ctx).2 := by rfl

theorem exec_pointAddUnequalXSubRightRepairGeneric
    (ctx : PointAddUnequalXSubRightContext) :
    Interp.execStmt Challenge.EvmProof.modexpExec 40
      ([] :: pointAddBodyFuns) (pointAddUnequalXSubRightRawEnv ctx)
      (pointAddUnequalXSubRightRawState ctx) pointAddUnequalXSubRightRepairStmt =
    .ok (pointAddUnequalXSubRightSelectedEnv ctx,
      pointAddUnequalXSubRightRawState ctx, .normal) := by
  rw [pointAddUnequalXSubRightRepairStmt_eq]
  by_cases h : pointAddUnequalXSubRightRepairValue ctx = 0
  · have h' : b2w (BitVec.ult
        (BitVec.ofNat 256 34565483545414906068789196026815425751)
        (pointAddUnequalXSubRightRaw ctx).1) = (0 : U256) := by
      simpa [pointAddUnequalXSubRightRepairValue,
        Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpSubNeedsRepairValue]
        using h
    rw [pointAddUnequalXSubRightSelectedEnv,
      pointAddUnequalXSubRightResult, if_pos h]
    simp [Interp.execStmt, Interp.execStmts, Interp.evalExpr, Interp.evalArgs,
      Challenge.EvmProof.modexpExec, Challenge.EvmProof.modexpBuiltinFn,
      stepOp, bin, EVM.litValue, Dialect.zero, VEnv.get, VEnv.setMany,
      VEnv.set, restore, pointAddUnequalXSubRightRawEnv, h']
  · have h' : b2w (BitVec.ult
        (BitVec.ofNat 256 34565483545414906068789196026815425751)
        (pointAddUnequalXSubRightRaw ctx).1) ≠ (0 : U256) := by
      simpa [pointAddUnequalXSubRightRepairValue,
        Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpSubNeedsRepairValue]
        using h
    rw [pointAddUnequalXSubRightSelectedEnv,
      pointAddUnequalXSubRightResult, if_neg h]
    simp [Interp.execStmt, Interp.execStmts, Interp.evalExpr, Interp.evalArgs,
      Challenge.EvmProof.modexpExec, Challenge.EvmProof.modexpBuiltinFn,
      stepOp, bin, EVM.litValue, Dialect.zero, VEnv.get, VEnv.setMany,
      VEnv.set, restore, pointAddUnequalXSubRightRawEnv,
      pointAddUnequalXSubRightRepaired]
    exact h'

theorem step_pointAddUnequalXSubRightRepairGeneric
    (ctx : PointAddUnequalXSubRightContext) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect
      ([] :: pointAddBodyFuns) (pointAddUnequalXSubRightRawEnv ctx)
      (pointAddUnequalXSubRightRawState ctx) pointAddUnequalXSubRightRepairStmt
      (pointAddUnequalXSubRightSelectedEnv ctx)
      (pointAddUnequalXSubRightRawState ctx) .normal :=
  (Interp.sound_all_of (E := Challenge.EvmProof.modexpExec)
    (fun _ _ _ _ hb => Challenge.EvmProof.modexpBuiltinFn_sound hb) 40).2.2.1
    _ _ _ _ _ _ _ (exec_pointAddUnequalXSubRightRepairGeneric ctx)

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
