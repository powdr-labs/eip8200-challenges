import Challenge.Bls12381G1Add.Reference.Proofs.SourceFpInvInputDefs
import Challenge.Bls12381.ProofSupport.FpInvConstants
import Challenge.EvmProof.ModexpFixed

set_option warningAsError true

/-! # Frozen G1ADD `fpInv` MODEXP input refinement -/

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open EvmSemantics EvmSemantics.EVM
open YulSemantics YulSemantics.EVM

private theorem storeFpState_memory_eq (ptr hi lo : U256) (yst : EvmState) :
    (storeFpState yst ptr hi lo).memory =
      storeWord
        (storeWord yst.memory ptr.toNat (hi <<< 128))
        (ptr + BitVec.ofNat 256 16).toNat lo := by
  funext address
  exact storeFpState_memory ptr hi lo yst address

theorem fpInvInput_baseSize (yst : EvmState) (hi lo : U256) :
    Precompile.bytesToNatPadded (fpInvInput yst hi lo) 0 32 = 48 := by
  unfold fpInvInput
  rw [Challenge.EvmProof.ModexpMemory.bytesToNatPadded_readWindow32
    _ 1024 240 0 (by omega)]
  simp only [Nat.add_zero]
  rw [fpInvInputState_memory]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 1024 32 1232 _ (by omega)]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 1024 32 1216 _ (by omega)]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 1024 32 1184 _ (by omega)]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 1024 32 1168 _ (by omega)]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 1024 32 1136 _ (by omega)]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 1024 32 1120 _ (by omega)]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 1024 32 1088 _ (by omega)]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 1024 32 1056 _ (by omega)]
  rw [Challenge.EvmProof.ModexpMemory.bytesNat_readBytes_storeWord]
  norm_num [YulEvmCompiler.toNat_u256_ofNat]

theorem fpInvInput_exponentSize (yst : EvmState) (hi lo : U256) :
    Precompile.bytesToNatPadded (fpInvInput yst hi lo) 32 32 = 48 := by
  unfold fpInvInput
  rw [Challenge.EvmProof.ModexpMemory.bytesToNatPadded_readWindow32
    _ 1024 240 32 (by omega)]
  norm_num only
  rw [fpInvInputState_memory]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 1056 32 1232 _ (by omega)]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 1056 32 1216 _ (by omega)]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 1056 32 1184 _ (by omega)]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 1056 32 1168 _ (by omega)]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 1056 32 1136 _ (by omega)]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 1056 32 1120 _ (by omega)]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 1056 32 1088 _ (by omega)]
  rw [Challenge.EvmProof.ModexpMemory.bytesNat_readBytes_storeWord]
  norm_num [YulEvmCompiler.toNat_u256_ofNat]

theorem fpInvInput_modulusSize (yst : EvmState) (hi lo : U256) :
    Precompile.bytesToNatPadded (fpInvInput yst hi lo) 64 32 = 48 := by
  unfold fpInvInput
  rw [Challenge.EvmProof.ModexpMemory.bytesToNatPadded_readWindow32
    _ 1024 240 64 (by omega)]
  norm_num only
  rw [fpInvInputState_memory]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 1088 32 1232 _ (by omega)]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 1088 32 1216 _ (by omega)]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 1088 32 1184 _ (by omega)]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 1088 32 1168 _ (by omega)]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 1088 32 1136 _ (by omega)]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 1088 32 1120 _ (by omega)]
  rw [Challenge.EvmProof.ModexpMemory.bytesNat_readBytes_storeWord]
  norm_num [YulEvmCompiler.toNat_u256_ofNat]

theorem fpInvInput_base (yst : EvmState) (hi lo : U256)
    (hhi : hi.toNat < 2 ^ 128) :
    Precompile.bytesToNatPadded (fpInvInput yst hi lo) 96 48 =
      hi.toNat * Challenge.EvmProof.Limbs.radix + lo.toNat := by
  unfold fpInvInput
  rw [Challenge.EvmProof.ModexpMemory.bytesToNatPadded_readWindow48
    _ 1024 240 96 (by omega)]
  norm_num only
  rw [fpInvInputState, storeFpState_memory_eq]
  norm_num [YulEvmCompiler.toNat_u256_ofNat]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 1120 48 1232 _ (by omega)]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 1120 48 1216 _ (by omega)]
  rw [fpInvExponentState, storeFpState_memory_eq]
  norm_num [YulEvmCompiler.toNat_u256_ofNat]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 1120 48 1184 _ (by omega)]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 1120 48 1168 _ (by omega)]
  unfold fpInvBaseState
  change Challenge.EvmProof.Bytes.bytesNat
      (readBytes
        (storeFpState (fpInvHeaderState yst) (BitVec.ofNat 256 1120) hi lo).memory
        (BitVec.ofNat 256 1120).toNat 48) = hi.toNat * 2 ^ 256 + lo.toNat
  exact bytesNat_readBytes_storeFpState
    (BitVec.ofNat 256 1120) hi lo (fpInvHeaderState yst)
    (by norm_num [YulEvmCompiler.toNat_u256_ofNat]) hhi

theorem fpInvInput_exponent (yst : EvmState) (hi lo : U256) :
    Precompile.bytesToNatPadded (fpInvInput yst hi lo) 144 48 =
      EvmSemantics.Crypto.Bls12381.p - 2 := by
  unfold fpInvInput
  rw [Challenge.EvmProof.ModexpMemory.bytesToNatPadded_readWindow48
    _ 1024 240 144 (by omega)]
  norm_num only
  rw [fpInvInputState, storeFpState_memory_eq]
  norm_num [YulEvmCompiler.toNat_u256_ofNat]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 1168 48 1232 _ (by omega)]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 1168 48 1216 _ (by omega)]
  unfold fpInvExponentState
  have hstore := bytesNat_readBytes_storeFpState
      (BitVec.ofNat 256 1168) fpModulusHiValue
      (BitVec.ofNat 256
        45442060874369865957053122457065728162598490762543039060009208264153100167849)
      (fpInvBaseState yst hi lo)
      (by norm_num [YulEvmCompiler.toNat_u256_ofNat])
      (by norm_num [fpModulusHiValue, YulEvmCompiler.toNat_u256_ofNat])
  change Challenge.EvmProof.Bytes.bytesNat
      (readBytes
        (storeFpState (fpInvBaseState yst hi lo) (BitVec.ofNat 256 1168)
          fpModulusHiValue
          (BitVec.ofNat 256
            45442060874369865957053122457065728162598490762543039060009208264153100167849)).memory
        (BitVec.ofNat 256 1168).toNat 48) = _
  rw [hstore]
  norm_num [fpModulusHiValue, YulEvmCompiler.toNat_u256_ofNat,
    EvmSemantics.Crypto.Bls12381.p, EvmSemantics.Crypto.Bls12381.absU]

theorem fpInvInput_modulus (yst : EvmState) (hi lo : U256) :
    Precompile.bytesToNatPadded (fpInvInput yst hi lo) 192 48 =
      EvmSemantics.Crypto.Bls12381.p := by
  unfold fpInvInput
  rw [Challenge.EvmProof.ModexpMemory.bytesToNatPadded_readWindow48
    _ 1024 240 192 (by omega)]
  norm_num only
  unfold fpInvInputState
  have hstore := bytesNat_readBytes_storeFpState
      (BitVec.ofNat 256 1216) fpModulusHiValue fpModulusLoValue
      (fpInvExponentState yst hi lo)
      (by norm_num [YulEvmCompiler.toNat_u256_ofNat])
      (by norm_num [fpModulusHiValue, YulEvmCompiler.toNat_u256_ofNat])
  change Challenge.EvmProof.Bytes.bytesNat
      (readBytes
        (storeFpState (fpInvExponentState yst hi lo) (BitVec.ofNat 256 1216)
          fpModulusHiValue fpModulusLoValue).memory
        (BitVec.ofNat 256 1216).toNat 48) = _
  rw [hstore]
  norm_num [fpModulusHiValue, fpModulusLoValue,
    YulEvmCompiler.toNat_u256_ofNat, EvmSemantics.Crypto.Bls12381.p,
    EvmSemantics.Crypto.Bls12381.absU]

theorem fpInvInput_exponentHead (yst : EvmState) (hi lo : U256) :
    Precompile.bytesToNatPadded (fpInvInput yst hi lo) 144 32 =
      (EvmSemantics.Crypto.Bls12381.p - 2) / 256 ^ 16 := by
  rw [← fpInvInput_exponent yst hi lo]
  exact (Challenge.EvmProof.Bytes.bytesToNatPadded_prefix_eq_div
    (fpInvInput yst hi lo) 144 32 16).symm

theorem fpInvInput_gas :
    Precompile.modexpGas .Osaka 48 48 48
        ((EvmSemantics.Crypto.Bls12381.p - 2) / 256 ^ 16) =
      36576 := by
  rw [show (EvmSemantics.Crypto.Bls12381.p - 2) / 256 ^ 16 =
      11762024554600535993938308040068522740004954473970332044491888924109355152932 by
    norm_num [EvmSemantics.Crypto.Bls12381.p,
      EvmSemantics.Crypto.Bls12381.absU]]
  have hlog : Nat.log2
      11762024554600535993938308040068522740004954473970332044491888924109355152932 =
      252 := by decide
  unfold Precompile.modexpGas
  rw [if_pos (by decide : EvmSemantics.Fork.Osaka ≥ EvmSemantics.Fork.Osaka)]
  simp only [Precompile.modexpGasOsaka, Precompile.adjustedExpLen]
  rw [hlog]
  norm_num

theorem fpInvInput_runModexp (hi lo : U256) (yst : EvmState)
    (hhi : hi.toNat < 2 ^ 128) :
    Precompile.runModexp .Osaka (fpInvInput yst hi lo) 36576 =
      .success (Precompile.natToBytes
        (Precompile.modPow
          (hi.toNat * Challenge.EvmProof.Limbs.radix + lo.toNat)
          (EvmSemantics.Crypto.Bls12381.p - 2)
          EvmSemantics.Crypto.Bls12381.p) 48) 36576 := by
  exact Challenge.EvmProof.ModexpFixed.runModexp_48_48_48
    (fpInvInput_baseSize yst hi lo)
    (fpInvInput_exponentSize yst hi lo)
    (fpInvInput_modulusSize yst hi lo)
    (fpInvInput_base yst hi lo hhi)
    (fpInvInput_exponent yst hi lo)
    (fpInvInput_modulus yst hi lo)
    (fpInvInput_exponentHead yst hi lo)
    fpInvInput_gas

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
