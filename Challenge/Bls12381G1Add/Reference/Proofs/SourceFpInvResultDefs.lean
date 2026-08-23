import Challenge.Bls12381G1Add.Reference.Proofs.SourceFpInvInput

set_option warningAsError true

/-! # Frozen G1ADD `fpInv` result state -/

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open EvmSemantics EvmSemantics.EVM
open YulSemantics YulSemantics.EVM

def fpInvReducedValue (hi lo : U256) : Nat :=
  Precompile.modPow
    (hi.toNat * Challenge.EvmProof.Limbs.radix + lo.toNat)
    (EvmSemantics.Crypto.Bls12381.p - 2)
    EvmSemantics.Crypto.Bls12381.p

def fpInvOutputBytes (hi lo : U256) : ByteArray :=
  Precompile.natToBytes (fpInvReducedValue hi lo) 48

def fpInvResponse (yst : EvmState) (hi lo : U256) : CallResponse :=
  { success := true
    returndata := (fpInvOutputBytes hi lo).toList
    world := CallWorld.ofState (fpInvInputState yst hi lo) }

def fpInvCallState (yst : EvmState) (hi lo : U256) : EvmState :=
  finishCall .staticcall (fpInvInputState yst hi lo)
    (fpInvResponse yst hi lo) 1024 240 1280 48

def fpInvResult (yst : EvmState) (hi lo : U256) : U256 × U256 :=
  (loadWord (fpInvCallState yst hi lo).memory 1280 >>> 128,
    loadWord (fpInvCallState yst hi lo).memory 1296)

def fpInvFinalState (yst : EvmState) (hi lo : U256) : EvmState :=
  touchMemory (touchMemory (fpInvCallState yst hi lo) 1280 32) 1296 32

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
