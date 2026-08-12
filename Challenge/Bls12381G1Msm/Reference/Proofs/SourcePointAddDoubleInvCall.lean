import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddDoubleInv

set_option warningAsError true

/-! Successful MODEXP call of the optimizer-inlined point-double inversion. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open EvmSemantics EvmSemantics.EVM
open YulSemantics YulSemantics.EVM

def pointAddDoubleInvCallState (yst : EvmState) (out left right : U256) : EvmState :=
  Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpInvCallState
    (pointAddDoubleDenArgsState yst out left right)
    (pointAddDoubleDenResult yst out left right).1
    (pointAddDoubleDenResult yst out left right).2

theorem exec_pointAddDoubleInvCall (yst : EvmState) (out left right : U256)
    (hhi : (pointAddDoubleDenResult yst out left right).1.toNat < 2 ^ 128) :
    Interp.execStmt Challenge.EvmProof.modexpExec 70
      ([] :: pointAddBodyFuns)
      (pointAddDoubleInvWorkEnv yst out left right)
      (pointAddDoubleInvInputState yst out left right)
      pointAddDoubleInvStmt9 =
    .ok (pointAddDoubleInvWorkEnv yst out left right,
      pointAddDoubleInvCallState yst out left right, .normal) := by
  have hrun :=
    Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpInvInput_runModexp
      (pointAddDoubleDenResult yst out left right).1
      (pointAddDoubleDenResult yst out left right).2
      (pointAddDoubleDenArgsState yst out left right) hhi
  change Precompile.runModexp .Osaka
      ⟨(readBytes (pointAddDoubleInvInputState yst out left right).memory
        1024 240).toArray⟩ 36576 =
    .success (Precompile.natToBytes
      (Precompile.modPow
        ((pointAddDoubleDenResult yst out left right).1.toNat *
          Challenge.EvmProof.Limbs.radix +
          (pointAddDoubleDenResult yst out left right).2.toNat)
        (EvmSemantics.Crypto.Bls12381.p - 2)
        EvmSemantics.Crypto.Bls12381.p) 48) 36576 at hrun
  rw [pointAddDoubleInvStmt9_eq, Interp.execStmt]
  simp [Interp.evalExpr, Interp.evalArgs,
    Challenge.EvmProof.modexpExec, Challenge.EvmProof.modexpBuiltinFn,
    hrun, pointAddDoubleInvCallState,
    Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpInvCallState,
    Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpInvResponse,
    Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpInvOutputBytes,
    Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpInvReducedValue,
    EVM.litValue, stepOp, un, Dialect.zero]
  rfl

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
