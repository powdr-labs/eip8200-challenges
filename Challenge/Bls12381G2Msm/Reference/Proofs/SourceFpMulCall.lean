import Challenge.Bls12381G2Msm.Reference.Proofs.SourceFpMulStart

set_option warningAsError true

/-! Frozen G2MSM `fpMul` modulus store and MODEXP call. -/

namespace Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics

open EvmSemantics EvmSemantics.EVM
open YulSemantics YulSemantics.EVM

theorem exec_fpMulModulus (ahi alo bhi blo : U256) (yst : EvmState) :
    Interp.execStmt Challenge.EvmProof.modexpExec 57 fpMulBodyFuns
      (fpMulProductEnv ahi alo bhi blo)
      (fpMulPreModulusState yst ahi alo bhi blo) fpMulStmt8 =
    .ok (fpMulProductEnv ahi alo bhi blo,
      fpMulInputState yst ahi alo bhi blo, .normal) := by
  rfl

private theorem fpMulStmt9_shape : fpMulStmt9 =
    .cond
      (.builtin .iszero
        [.builtin .staticcall
          [.lit (.number 500), .lit (.number 5), .lit (.number 1024),
            .lit (.number 241), .lit (.number 1280), .lit (.number 48)]])
      [.exprStmt (.builtin .invalid [])] := by
  rfl

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
    hrun, fpMulCallState, EVM.litValue, stepOp, un, Dialect.zero]
  rfl

end Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics
