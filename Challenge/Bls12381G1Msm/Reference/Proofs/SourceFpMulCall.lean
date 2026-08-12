import Challenge.Bls12381G1Msm.Reference.Proofs.SourceFpMulInput

set_option warningAsError true

/-! Frozen G1MSM `fpMul` MODEXP call. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open EvmSemantics EvmSemantics.EVM
open YulSemantics YulSemantics.EVM

def fpMulReducedValue (ahi alo bhi blo : U256) : Nat :=
  (convFullMul (fullMulValue ahi alo bhi blo)).value %
    EvmSemantics.Crypto.Bls12381.p

def fpMulOutputBytes (ahi alo bhi blo : U256) : ByteArray :=
  Precompile.natToBytes (fpMulReducedValue ahi alo bhi blo) 48

def fpMulResponse (yst : EvmState) (ahi alo bhi blo : U256) : CallResponse :=
  { success := true
    returndata := (fpMulOutputBytes ahi alo bhi blo).toList
    world := CallWorld.ofState (fpMulInputState yst ahi alo bhi blo) }

def fpMulCallState (yst : EvmState) (ahi alo bhi blo : U256) : EvmState :=
  finishCall .staticcall (fpMulInputState yst ahi alo bhi blo)
    (fpMulResponse yst ahi alo bhi blo) 1024 241 1280 48

private theorem fpMulStmt6_shape : fpMulStmt6 =
    .cond
      (.builtin .iszero
        [.builtin .staticcall
          [.lit (.number 500), .lit (.number 5), .lit (.number 1024),
            .lit (.number 241), .lit (.number 1280), .lit (.number 48)]])
      [.exprStmt (.builtin .invalid [])] := by
  rfl

theorem exec_fpMulCall (ahi alo bhi blo : U256) (yst : EvmState) :
    Interp.execStmt Challenge.EvmProof.modexpExec 56 fpMulBodyFuns
      (fpMulInitialEnv ahi alo bhi blo)
      (fpMulInputState yst ahi alo bhi blo) fpMulStmt6 =
    .ok (fpMulInitialEnv ahi alo bhi blo,
      fpMulCallState yst ahi alo bhi blo, .normal) := by
  have hrun := fpMulInput_runModexp_raw ahi alo bhi blo yst
  change Precompile.runModexp .Osaka
      ⟨(readBytes (fpMulInputState yst ahi alo bhi blo).memory
        1024 241).toArray⟩ 500 =
    .success (Precompile.natToBytes
      ((convFullMul (fullMulValue ahi alo bhi blo)).value %
        EvmSemantics.Crypto.Bls12381.p) 48) 500 at hrun
  rw [fpMulStmt6_shape, Interp.execStmt]
  simp [Interp.evalExpr, Interp.evalArgs,
    Challenge.EvmProof.modexpExec, Challenge.EvmProof.modexpBuiltinFn,
    hrun, fpMulCallState, fpMulResponse, fpMulOutputBytes,
    fpMulReducedValue, EVM.litValue, stepOp, un, Dialect.zero]
  rfl

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
