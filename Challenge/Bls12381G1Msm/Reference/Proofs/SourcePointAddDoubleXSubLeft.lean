import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddDoubleX3
import Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

set_option warningAsError true

/-! Raw-word prefix of the first inlined `fpSub` in point doubling. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

private abbrev fpSubRawValue :=
  Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpSubRawValue

def pointAddDoubleXSubLeftPtr (yst : EvmState) (out left right : U256) : U256 :=
  loadWord (pointAddDoubleX3State yst out left right).memory 1568

def pointAddDoubleXSubLeftHi (yst : EvmState) (out left right : U256) : U256 :=
  loadWord (pointAddDoubleX3State yst out left right).memory
    (pointAddDoubleXSubLeftPtr yst out left right).toNat

def pointAddDoubleXSubLeftLo (yst : EvmState) (out left right : U256) : U256 :=
  loadWord (pointAddDoubleX3State yst out left right).memory
    (pointAddDoubleXSubLeftPtr yst out left right + 32).toNat

def pointAddDoubleXSubLeftRaw (yst : EvmState) (out left right : U256) :
    U256 × U256 :=
  fpSubRawValue
    (pointAddDoubleX3Result yst out left right).1
    (pointAddDoubleX3Result yst out left right).2
    (pointAddDoubleXSubLeftHi yst out left right)
    (pointAddDoubleXSubLeftLo yst out left right)

def pointAddDoubleXSubLeftState1 (yst : EvmState) (out left right : U256) :=
  touchMemory (pointAddDoubleX3State yst out left right) 1568 32

def pointAddDoubleXSubLeftState2 (yst : EvmState) (out left right : U256) :=
  touchMemory (pointAddDoubleXSubLeftState1 yst out left right)
    (pointAddDoubleXSubLeftPtr yst out left right + 32).toNat 32

def pointAddDoubleXSubLeftState3 (yst : EvmState) (out left right : U256) :=
  touchMemory (pointAddDoubleXSubLeftState2 yst out left right) 1568 32

def pointAddDoubleXSubLeftRawState (yst : EvmState) (out left right : U256) :=
  touchMemory (pointAddDoubleXSubLeftState3 yst out left right)
    (pointAddDoubleXSubLeftPtr yst out left right).toNat 32

def pointAddDoubleXSubLeftRawEnv (yst : EvmState) (out left right : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  ["fc0_28", "fc0_29"].zip
    [(pointAddDoubleXSubLeftRaw yst out left right).1,
      (pointAddDoubleXSubLeftRaw yst out left right).2] ++
    pointAddDoubleX3Env yst out left right

theorem pointAddDoubleXSubLeftRawEnv_hi (yst : EvmState)
    (out left right : U256) :
    VEnv.get (pointAddDoubleXSubLeftRawEnv yst out left right) "fc0_28" =
      some (pointAddDoubleXSubLeftRaw yst out left right).1 := by
  rfl

theorem pointAddDoubleXSubLeftRawEnv_lo (yst : EvmState)
    (out left right : U256) :
    VEnv.get (pointAddDoubleXSubLeftRawEnv yst out left right) "fc0_29" =
      some (pointAddDoubleXSubLeftRaw yst out left right).2 := by
  rfl

theorem exec_pointAddDoubleXSubLeftRaw (yst : EvmState)
    (out left right : U256) :
    Interp.execStmts Challenge.EvmProof.modexpExec 70
      ([] :: pointAddBodyFuns) (pointAddDoubleX3Env yst out left right)
      (pointAddDoubleX3State yst out left right)
      (pointAddDoubleXSubLeftBody.take 2) =
    .ok (pointAddDoubleXSubLeftRawEnv yst out left right,
      pointAddDoubleXSubLeftRawState yst out left right, .normal) := by
  rw [pointAddDoubleXSubLeftRawPrefix_shape]
  simp [Interp.execStmts, Interp.execStmt, Interp.evalExpr, Interp.evalArgs,
    Challenge.EvmProof.modexpExec, Challenge.EvmProof.modexpBuiltinFn,
    EVM.litValue, stepOp, bin, Dialect.zero, VEnv.get, VEnv.setMany,
    VEnv.set, bindZeros, restore, pointAddDoubleX3Env,
    pointAddDoubleXSubLeftRawEnv,
    pointAddDoubleXSubLeftRaw, pointAddDoubleXSubLeftHi,
    pointAddDoubleXSubLeftLo, pointAddDoubleXSubLeftPtr,
    pointAddDoubleXSubLeftRawState, pointAddDoubleXSubLeftState1,
    pointAddDoubleXSubLeftState2, pointAddDoubleXSubLeftState3,
    Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpSubRawValue]

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
