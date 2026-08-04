import Challenge.Modexp.Spec
set_option warningAsError true

namespace Challenge.Modexp

open EvmSemantics
open EvmSemantics.EVM

theorem initialState_pc (code calldata : ByteArray) (gas : Nat) :
    (initialState code calldata gas).pc = UInt256.ofNat 0 := rfl

theorem initialState_stack (code calldata : ByteArray) (gas : Nat) :
    (initialState code calldata gas).stack = [] := rfl

theorem initialState_gas (code calldata : ByteArray) (gas : Nat) :
    (initialState code calldata gas).gasAvailable = gas := rfl

theorem initialState_calldata (code calldata : ByteArray) (gas : Nat) :
    (initialState code calldata gas).executionEnv.calldata = calldata := rfl

theorem deployAddress_not_precompile :
    Precompile.isPrecompileWithConfig executionConfig .Osaka deployAddress = false := by
  decide

end Challenge.Modexp
