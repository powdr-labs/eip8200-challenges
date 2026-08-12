import Challenge.Bls12381G2Add.Reference.Proofs.SourceFpModexpDefs

set_option warningAsError true

/-! # Frozen G2ADD `fpInv` stores and MODEXP call -/

namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open EvmSemantics EvmSemantics.EVM
open YulSemantics YulSemantics.EVM

theorem exec_fpInvStores (hi lo : U256) (yst : EvmState) :
    Interp.execStmts Challenge.EvmProof.modexpExec 66 fpInvBodyFuns
      (fpInvInitialEnv hi lo) yst
      [fpInvStmt0, fpInvStmt1, fpInvStmt2, fpInvStmt3, fpInvStmt4,
        fpInvStmt5] =
    .ok (fpInvInitialEnv hi lo, fpInvInputState yst hi lo, .normal) := by
  rfl

private theorem fpInvStmt6_shape : fpInvStmt6 =
    .cond
      (.builtin .iszero
        [.builtin .staticcall
          [.lit (.number 36576), .lit (.number 5), .lit (.number 1024),
            .lit (.number 240), .lit (.number 1280), .lit (.number 48)]])
      [.exprStmt (.builtin .invalid [])] := by
  rfl

/-- The fixed-gas MODEXP inversion call succeeds on the exact input. -/
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
    hrun, fpInvCallState, EVM.litValue, stepOp, un, Dialect.zero]
  rfl

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

