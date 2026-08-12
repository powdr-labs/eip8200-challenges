import Challenge.Bls12381G1Msm.Reference.Proofs.SourceFpMulInputStores
import Challenge.Bls12381G1Add.Reference.Proofs.SourceFpMulInput

set_option warningAsError true

/-! Reuse of the certified MODEXP-one input boundary for G1MSM `fpMul`. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open EvmSemantics EvmSemantics.EVM
open YulSemantics YulSemantics.EVM

theorem fpMulInputState_eq_shared (yst : EvmState) (ahi alo bhi blo : U256) :
    fpMulInputState yst ahi alo bhi blo =
      Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpMulInputState
        yst ahi alo bhi blo := by
  rfl

def fpMulInput (yst : EvmState) (ahi alo bhi blo : U256) : ByteArray :=
  Challenge.EvmProof.ModexpMemory.readWindow
    (fpMulInputState yst ahi alo bhi blo).memory 1024 241

theorem fpMulInput_runModexp_raw (ahi alo bhi blo : U256) (yst : EvmState) :
    Precompile.runModexp .Osaka (fpMulInput yst ahi alo bhi blo) 500 =
      .success (Precompile.natToBytes
        ((convFullMul (fullMulValue ahi alo bhi blo)).value %
          EvmSemantics.Crypto.Bls12381.p) 48) 500 := by
  simpa [fpMulInput,
    Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpMulInput,
    fpMulInputState_eq_shared] using
    Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpMulInput_runModexp_raw
      ahi alo bhi blo yst

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
