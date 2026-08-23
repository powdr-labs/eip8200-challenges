import Challenge.Bls12381G1Add.Reference.Proofs.SourceFpInvStores

set_option warningAsError true

/-! # Frozen G1ADD `fpInv` MODEXP call -/

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open EvmSemantics EvmSemantics.EVM
open YulSemantics YulSemantics.EVM

private theorem fpInvStmt6_shape : fpInvStmt6 =
    .cond
      (.builtin .iszero
        [.builtin .staticcall
          [.lit (.number 36576), .lit (.number 5), .lit (.number 1024),
            .lit (.number 240), .lit (.number 1280), .lit (.number 48)]])
      [.exprStmt (.builtin .invalid [])] := by
  rfl

/-- The literal-36576 MODEXP call succeeds on the exact 240-byte inversion
input, so the source failure branch is skipped and the residue is copied. -/
theorem exec_fpInvCall (hi lo : U256) (yst : EvmState)
    (hhi : hi.toNat < 2 ^ 128) :
    Interp.execStmt Challenge.EvmProof.modexpExec 60 fpInvBodyFuns
      (fpInvInitialEnv hi lo) (fpInvInputState yst hi lo) fpInvStmt6 =
    .ok (fpInvInitialEnv hi lo, fpInvCallState yst hi lo, .normal) := by
  have hrun := fpInvInput_runModexp hi lo yst hhi
  change Precompile.runModexp .Osaka
      ⟨(readBytes (fpInvInputState yst hi lo).memory 1024 240).toArray⟩
      36576 =
    .success (Precompile.natToBytes
      (Precompile.modPow
        (hi.toNat * Challenge.EvmProof.Limbs.radix + lo.toNat)
        (EvmSemantics.Crypto.Bls12381.p - 2)
        EvmSemantics.Crypto.Bls12381.p) 48) 36576 at hrun
  rw [fpInvStmt6_shape, Interp.execStmt]
  simp [Interp.evalExpr, Interp.evalArgs,
    Challenge.EvmProof.modexpExec, Challenge.EvmProof.modexpBuiltinFn,
    hrun, fpInvCallState, fpInvResponse, fpInvOutputBytes,
    fpInvReducedValue, EVM.litValue, stepOp, un, Dialect.zero]
  rfl

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
