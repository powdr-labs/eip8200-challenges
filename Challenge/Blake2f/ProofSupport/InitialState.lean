import Challenge.Blake2f.Spec

set_option warningAsError true

namespace Challenge.Blake2f

open EvmSemantics
open EvmSemantics.EVM

@[simp] theorem initialState_pc (code calldata : ByteArray) (gas : Nat) :
    (initialState code calldata gas).pc = UInt256.ofNat 0 := rfl

@[simp] theorem initialState_stack (code calldata : ByteArray) (gas : Nat) :
    (initialState code calldata gas).stack = [] := rfl

@[simp] theorem initialState_gas (code calldata : ByteArray) (gas : Nat) :
    (initialState code calldata gas).gasAvailable = gas := rfl

@[simp] theorem initialState_calldata (code calldata : ByteArray) (gas : Nat) :
    (initialState code calldata gas).executionEnv.calldata = calldata := rfl

theorem deployAddress_not_precompile :
    Precompile.isPrecompileWithConfig executionConfig .Osaka deployAddress = false := by
  decide

theorem incumbent_blake2f_disabled :
    Precompile.isPrecompileWithConfig executionConfig .Osaka
      Precompile.blake2fAddress = false := by
  decide

end Challenge.Blake2f
