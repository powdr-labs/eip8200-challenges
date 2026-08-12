import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalXSubDefs
import Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

set_option warningAsError true

/-! Raw-word prefix of the first unequal-point x subtraction. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

private abbrev fpSubRawValue :=
  Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpSubRawValue

def pointAddUnequalXSubLeftPtr (yst : EvmState)
    (out left right : U256) : U256 :=
  loadWord (pointAddUnequalX3State yst out left right).memory 1568

def pointAddUnequalXSubLeftHi (yst : EvmState)
    (out left right : U256) : U256 :=
  loadWord (pointAddUnequalX3State yst out left right).memory
    (pointAddUnequalXSubLeftPtr yst out left right).toNat

def pointAddUnequalXSubLeftLo (yst : EvmState)
    (out left right : U256) : U256 :=
  loadWord (pointAddUnequalX3State yst out left right).memory
    (pointAddUnequalXSubLeftPtr yst out left right + 32).toNat

def pointAddUnequalXSubLeftRaw (yst : EvmState)
    (out left right : U256) : U256 × U256 :=
  fpSubRawValue
    (pointAddUnequalX3Result yst out left right).1
    (pointAddUnequalX3Result yst out left right).2
    (pointAddUnequalXSubLeftHi yst out left right)
    (pointAddUnequalXSubLeftLo yst out left right)

theorem pointAddUnequalXSubLeftRaw_eq_fpSubRawValue (yst : EvmState)
    (out left right : U256) :
    pointAddUnequalXSubLeftRaw yst out left right =
      Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpSubRawValue
        (pointAddUnequalX3Result yst out left right).1
        (pointAddUnequalX3Result yst out left right).2
        (pointAddUnequalXSubLeftHi yst out left right)
        (pointAddUnequalXSubLeftLo yst out left right) := by
  rfl

def pointAddUnequalXSubLeftState1 (yst : EvmState)
    (out left right : U256) :=
  touchMemory (pointAddUnequalX3State yst out left right) 1568 32

def pointAddUnequalXSubLeftState2 (yst : EvmState)
    (out left right : U256) :=
  touchMemory (pointAddUnequalXSubLeftState1 yst out left right)
    (pointAddUnequalXSubLeftPtr yst out left right + 32).toNat 32

def pointAddUnequalXSubLeftState3 (yst : EvmState)
    (out left right : U256) :=
  touchMemory (pointAddUnequalXSubLeftState2 yst out left right) 1568 32

def pointAddUnequalXSubLeftRawState (yst : EvmState)
    (out left right : U256) :=
  touchMemory (pointAddUnequalXSubLeftState3 yst out left right)
    (pointAddUnequalXSubLeftPtr yst out left right).toNat 32

def pointAddUnequalXSubLeftRawEnv (yst : EvmState)
    (out left right : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  ["fc0_81", "fc0_82"].zip
    [(pointAddUnequalXSubLeftRaw yst out left right).1,
      (pointAddUnequalXSubLeftRaw yst out left right).2] ++
    pointAddUnequalX3Env yst out left right

theorem pointAddUnequalXSubLeftRawEnv_hi (yst : EvmState)
    (out left right : U256) :
    VEnv.get (pointAddUnequalXSubLeftRawEnv yst out left right) "fc0_81" =
      some (pointAddUnequalXSubLeftRaw yst out left right).1 := by
  rfl

theorem pointAddUnequalXSubLeftRawEnv_lo (yst : EvmState)
    (out left right : U256) :
    VEnv.get (pointAddUnequalXSubLeftRawEnv yst out left right) "fc0_82" =
      some (pointAddUnequalXSubLeftRaw yst out left right).2 := by
  rfl

theorem exec_pointAddUnequalXSubLeftRaw (yst : EvmState)
    (out left right : U256) :
    Interp.execStmts Challenge.EvmProof.modexpExec 70
      ([] :: pointAddBodyFuns) (pointAddUnequalX3Env yst out left right)
      (pointAddUnequalX3State yst out left right)
      (pointAddUnequalXSubLeftBody.take 2) =
    .ok (pointAddUnequalXSubLeftRawEnv yst out left right,
      pointAddUnequalXSubLeftRawState yst out left right, .normal) := by
  rw [pointAddUnequalXSubLeftRawPrefix_shape]
  simp [Interp.execStmts, Interp.execStmt, Interp.evalExpr, Interp.evalArgs,
    Challenge.EvmProof.modexpExec, Challenge.EvmProof.modexpBuiltinFn,
    EVM.litValue, stepOp, bin, Dialect.zero, VEnv.get, VEnv.setMany,
    VEnv.set, bindZeros, restore, pointAddUnequalX3Env,
    pointAddUnequalXSubLeftRawEnv, pointAddUnequalXSubLeftRaw,
    pointAddUnequalXSubLeftHi, pointAddUnequalXSubLeftLo,
    pointAddUnequalXSubLeftPtr, pointAddUnequalXSubLeftRawState,
    pointAddUnequalXSubLeftState1, pointAddUnequalXSubLeftState2,
    pointAddUnequalXSubLeftState3,
    Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpSubRawValue]

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
