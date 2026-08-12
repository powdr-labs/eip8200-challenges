import Challenge.Bls12381Pairing.Spec
import Challenge.Bls12381.ProofSupport

set_option warningAsError true

namespace Challenge.Bls12381Pairing

open EvmSemantics EvmSemantics.EVM

@[simp] theorem initialState_pc (code calldata : ByteArray) (gas : Nat) :
    (initialState code calldata gas).pc = UInt256.ofNat 0 := rfl

theorem deployAddress_not_precompile :
    Precompile.isPrecompileWithConfig executionConfig .Osaka deployAddress = false := by
  decide

theorem incumbent_disabled :
    Precompile.isPrecompileWithConfig executionConfig .Osaka
      Precompile.blsPairingAddress = false := by
  decide

end Challenge.Bls12381Pairing

