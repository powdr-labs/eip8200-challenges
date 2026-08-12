import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalInvInputBridge

set_option warningAsError true

/-! Successful MODEXP call of the inlined unequal-denominator inversion. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open EvmSemantics EvmSemantics.EVM
open YulSemantics YulSemantics.EVM

def pointAddUnequalInvCallState (yst : EvmState)
    (out left right : U256) : EvmState :=
  Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpInvCallState
    (pointAddUnequalNumeratorInputsState yst out left right)
    (pointAddUnequalDenominatorResult yst out left right).1
    (pointAddUnequalDenominatorResult yst out left right).2

theorem exec_pointAddUnequalInvCall (yst : EvmState)
    (out left right : U256)
    (hhi : (pointAddUnequalDenominatorResult yst out left right).1.toNat <
      2 ^ 128) :
    Interp.execStmt Challenge.EvmProof.modexpExec 70
      ([] :: pointAddBodyFuns)
      (pointAddUnequalInvWorkEnv yst out left right)
      (pointAddUnequalInvInputState yst out left right)
      pointAddUnequalInvStmt9 =
    .ok (pointAddUnequalInvWorkEnv yst out left right,
      pointAddUnequalInvCallState yst out left right, .normal) := by
  have hrun :=
    Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpInvInput_runModexp
      (pointAddUnequalDenominatorResult yst out left right).1
      (pointAddUnequalDenominatorResult yst out left right).2
      (pointAddUnequalNumeratorInputsState yst out left right) hhi
  change Precompile.runModexp .Osaka
      ⟨(readBytes (pointAddUnequalInvInputState yst out left right).memory
        1024 240).toArray⟩ 36576 =
    .success (Precompile.natToBytes
      (Precompile.modPow
        ((pointAddUnequalDenominatorResult yst out left right).1.toNat *
          Challenge.EvmProof.Limbs.radix +
          (pointAddUnequalDenominatorResult yst out left right).2.toNat)
        (EvmSemantics.Crypto.Bls12381.p - 2)
        EvmSemantics.Crypto.Bls12381.p) 48) 36576 at hrun
  rw [pointAddUnequalInvStmt9_eq, Interp.execStmt]
  simp [Interp.evalExpr, Interp.evalArgs,
    Challenge.EvmProof.modexpExec, Challenge.EvmProof.modexpBuiltinFn,
    hrun, pointAddUnequalInvCallState,
    Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpInvCallState,
    Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpInvResponse,
    Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpInvOutputBytes,
    Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpInvReducedValue,
    EVM.litValue, stepOp, un, Dialect.zero]
  rfl

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
