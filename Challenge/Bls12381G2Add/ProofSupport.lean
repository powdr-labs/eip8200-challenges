import Challenge.Bls12381G2Add.Spec

set_option warningAsError true

namespace Challenge.Bls12381G2Add

open EvmSemantics EvmSemantics.EVM

@[simp] theorem initialState_pc (code calldata : ByteArray) (gas : Nat) :
    (initialState code calldata gas).pc = UInt256.ofNat 0 := rfl

@[simp] theorem initialState_calldata (code calldata : ByteArray) (gas : Nat) :
    (initialState code calldata gas).executionEnv.calldata = calldata := rfl

theorem deployAddress_not_precompile :
    Precompile.isPrecompileWithConfig executionConfig .Osaka deployAddress = false := by
  decide

theorem incumbent_disabled :
    Precompile.isPrecompileWithConfig executionConfig .Osaka
      Precompile.blsG2AddAddress = false := by
  decide

end Challenge.Bls12381G2Add
