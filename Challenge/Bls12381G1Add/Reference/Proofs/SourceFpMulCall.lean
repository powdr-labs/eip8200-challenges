import Challenge.Bls12381G1Add.Reference.Proofs.SourceFpMulModulus

set_option warningAsError true

/-! # Frozen G1ADD `fpMul` MODEXP call -/

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open EvmSemantics EvmSemantics.EVM
open YulSemantics YulSemantics.EVM

private theorem fpMulStmt9_shape : fpMulStmt9 =
    .cond
      (.builtin .iszero
        [.builtin .staticcall
          [.lit (.number 500), .lit (.number 5), .lit (.number 1024),
            .lit (.number 241), .lit (.number 1280), .lit (.number 48)]])
      [.exprStmt (.builtin .invalid [])] := by
  rfl

/-- The literal-500 MODEXP call succeeds on the exact 241-byte input, so the
source `iszero` failure branch is skipped and the 48-byte result is copied. -/
theorem exec_fpMulCall (ahi alo bhi blo : U256) (yst : EvmState) :
    Interp.execStmt Challenge.EvmProof.modexpExec 56 fpMulBodyFuns
      (fpMulProductEnv ahi alo bhi blo)
      (fpMulInputState yst ahi alo bhi blo) fpMulStmt9 =
    .ok (fpMulProductEnv ahi alo bhi blo,
      fpMulCallState yst ahi alo bhi blo, .normal) := by
  have hrun := fpMulInput_runModexp_raw ahi alo bhi blo yst
  change Precompile.runModexp .Osaka
      ⟨(readBytes (fpMulInputState yst ahi alo bhi blo).memory 1024 241).toArray⟩
      500 =
    .success (Precompile.natToBytes
      ((convFullMul (fullMulValue ahi alo bhi blo)).value %
        EvmSemantics.Crypto.Bls12381.p) 48) 500 at hrun
  rw [fpMulStmt9_shape, Interp.execStmt]
  simp [Interp.evalExpr, Interp.evalArgs,
    Challenge.EvmProof.modexpExec, Challenge.EvmProof.modexpBuiltinFn,
    hrun,
    fpMulCallState, fpMulResponse, fpMulOutputBytes, fpMulReducedValue,
    EVM.litValue, stepOp, un, Dialect.zero]
  rfl

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
