import Challenge.Bls12381G1Add.Reference.Proofs.SourceFpMulInputDefs
import Challenge.EvmProof.ModexpOne

set_option warningAsError true

/-! # Frozen G1ADD `fpMul` MODEXP input refinement -/

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open EvmSemantics EvmSemantics.EVM
open YulSemantics YulSemantics.EVM

/-- Exact 241-byte MODEXP input window assembled by `fpMul`. -/
def fpMulInput (yst : EvmState) (ahi alo bhi blo : U256) : ByteArray :=
  Challenge.EvmProof.ModexpMemory.readWindow
    (fpMulInputState yst ahi alo bhi blo).memory 1024 241

theorem fpMulInput_baseSize (yst : EvmState) (ahi alo bhi blo : U256) :
    Precompile.bytesToNatPadded (fpMulInput yst ahi alo bhi blo) 0 32 = 96 := by
  unfold fpMulInput
  rw [Challenge.EvmProof.ModexpMemory.bytesToNatPadded_readWindow32
    _ 1024 241 0 (by omega)]
  simp only [Nat.add_zero]
  rw [fpMulInputState_memory]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 1024 32 1233 _ (by omega)]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 1024 32 1217 _ (by omega)]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeByte_disjoint
    _ 1024 32 1216 _ (by omega)]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 1024 32 1184 _ (by omega)]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 1024 32 1152 _ (by omega)]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 1024 32 1120 _ (by omega)]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 1024 32 1088 _ (by omega)]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 1024 32 1056 _ (by omega)]
  rw [Challenge.EvmProof.ModexpMemory.bytesNat_readBytes_storeWord]
  norm_num [YulEvmCompiler.toNat_u256_ofNat]

theorem fpMulInput_exponentSize (yst : EvmState) (ahi alo bhi blo : U256) :
    Precompile.bytesToNatPadded (fpMulInput yst ahi alo bhi blo) 32 32 = 1 := by
  unfold fpMulInput
  rw [Challenge.EvmProof.ModexpMemory.bytesToNatPadded_readWindow32
    _ 1024 241 32 (by omega)]
  norm_num only
  rw [fpMulInputState_memory]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 1056 32 1233 _ (by omega)]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 1056 32 1217 _ (by omega)]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeByte_disjoint
    _ 1056 32 1216 _ (by omega)]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 1056 32 1184 _ (by omega)]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 1056 32 1152 _ (by omega)]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 1056 32 1120 _ (by omega)]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 1056 32 1088 _ (by omega)]
  rw [Challenge.EvmProof.ModexpMemory.bytesNat_readBytes_storeWord]
  norm_num [YulEvmCompiler.toNat_u256_ofNat]

theorem fpMulInput_modulusSize (yst : EvmState) (ahi alo bhi blo : U256) :
    Precompile.bytesToNatPadded (fpMulInput yst ahi alo bhi blo) 64 32 = 48 := by
  unfold fpMulInput
  rw [Challenge.EvmProof.ModexpMemory.bytesToNatPadded_readWindow32
    _ 1024 241 64 (by omega)]
  norm_num only
  rw [fpMulInputState_memory]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 1088 32 1233 _ (by omega)]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 1088 32 1217 _ (by omega)]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeByte_disjoint
    _ 1088 32 1216 _ (by omega)]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 1088 32 1184 _ (by omega)]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 1088 32 1152 _ (by omega)]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 1088 32 1120 _ (by omega)]
  rw [Challenge.EvmProof.ModexpMemory.bytesNat_readBytes_storeWord]
  norm_num [YulEvmCompiler.toNat_u256_ofNat]

theorem fpMulInput_exponent (yst : EvmState) (ahi alo bhi blo : U256) :
    Precompile.bytesToNatPadded (fpMulInput yst ahi alo bhi blo) 192 1 = 1 := by
  unfold fpMulInput
  rw [Challenge.EvmProof.ModexpMemory.bytesToNatPadded_readWindow
    _ 1024 241 192 1 (by omega)]
  norm_num only
  rw [fpMulInputState_memory]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 1216 1 1233 _ (by omega)]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 1216 1 1217 _ (by omega)]
  rw [Challenge.EvmProof.ModexpMemory.bytesNat_readBytes_storeByte]
  norm_num [YulEvmCompiler.byteAt_eq, YulEvmCompiler.toNat_u256_ofNat]
  rfl

private theorem bytesNat_readBytes_storeFpState_at (ptr hi lo : U256)
    (yst : EvmState) (start : Nat) (hstart : start = ptr.toNat)
    (hptr : ptr.toNat + 16 < 2 ^ 256)
    (hhi : hi.toNat < 2 ^ 128) :
    Challenge.EvmProof.Bytes.bytesNat
        (readBytes (storeFpState yst ptr hi lo).memory start 48) =
      hi.toNat * 2 ^ 256 + lo.toNat := by
  subst start
  exact bytesNat_readBytes_storeFpState ptr hi lo yst hptr hhi

theorem fpMulInput_modulus (yst : EvmState) (ahi alo bhi blo : U256) :
    Precompile.bytesToNatPadded (fpMulInput yst ahi alo bhi blo) 193 48 =
      EvmSemantics.Crypto.Bls12381.p := by
  unfold fpMulInput
  rw [Challenge.EvmProof.ModexpMemory.bytesToNatPadded_readWindow48
    _ 1024 241 193 (by omega)]
  norm_num only
  have hstore := bytesNat_readBytes_storeFpState_at
    (BitVec.ofNat 256 1217) fpModulusHiValue fpModulusLoValue
    (fpMulPreModulusState yst ahi alo bhi blo) 1217
    (by norm_num [YulEvmCompiler.toNat_u256_ofNat])
    (by norm_num [YulEvmCompiler.toNat_u256_ofNat])
    (by norm_num [fpModulusHiValue, YulEvmCompiler.toNat_u256_ofNat])
  change Challenge.EvmProof.Bytes.bytesNat
      (readBytes
        (storeFpState (fpMulPreModulusState yst ahi alo bhi blo)
          (BitVec.ofNat 256 1217) fpModulusHiValue fpModulusLoValue).memory
        1217 48) = EvmSemantics.Crypto.Bls12381.p
  rw [hstore]
  norm_num [fpModulusHiValue, fpModulusLoValue,
    YulEvmCompiler.toNat_u256_ofNat, EvmSemantics.Crypto.Bls12381.p,
    EvmSemantics.Crypto.Bls12381.absU]

private theorem fpMulInput_r2 (yst : EvmState) (ahi alo bhi blo : U256) :
    Challenge.EvmProof.Bytes.bytesNat
        (readBytes (fpMulInputState yst ahi alo bhi blo).memory 1120 32) =
      (fullMulValue ahi alo bhi blo).r2.toNat := by
  rw [fpMulInputState_memory]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 1120 32 1233 _ (by omega)]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 1120 32 1217 _ (by omega)]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeByte_disjoint
    _ 1120 32 1216 _ (by omega)]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 1120 32 1184 _ (by omega)]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 1120 32 1152 _ (by omega)]
  exact Challenge.EvmProof.ModexpMemory.bytesNat_readBytes_storeWord _ _ _

private theorem fpMulInput_r1 (yst : EvmState) (ahi alo bhi blo : U256) :
    Challenge.EvmProof.Bytes.bytesNat
        (readBytes (fpMulInputState yst ahi alo bhi blo).memory 1152 32) =
      (fullMulValue ahi alo bhi blo).r1.toNat := by
  rw [fpMulInputState_memory]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 1152 32 1233 _ (by omega)]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 1152 32 1217 _ (by omega)]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeByte_disjoint
    _ 1152 32 1216 _ (by omega)]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 1152 32 1184 _ (by omega)]
  exact Challenge.EvmProof.ModexpMemory.bytesNat_readBytes_storeWord _ _ _

private theorem fpMulInput_r0 (yst : EvmState) (ahi alo bhi blo : U256) :
    Challenge.EvmProof.Bytes.bytesNat
        (readBytes (fpMulInputState yst ahi alo bhi blo).memory 1184 32) =
      (fullMulValue ahi alo bhi blo).r0.toNat := by
  rw [fpMulInputState_memory]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 1184 32 1233 _ (by omega)]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 1184 32 1217 _ (by omega)]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeByte_disjoint
    _ 1184 32 1216 _ (by omega)]
  exact Challenge.EvmProof.ModexpMemory.bytesNat_readBytes_storeWord _ _ _

theorem fpMulInput_base (yst : EvmState) (ahi alo bhi blo : U256) :
    Precompile.bytesToNatPadded (fpMulInput yst ahi alo bhi blo) 96 96 =
      (convFullMul (fullMulValue ahi alo bhi blo)).value := by
  unfold fpMulInput
  rw [Challenge.EvmProof.ModexpMemory.bytesToNatPadded_readWindow96
    _ 1024 241 96 (by omega)]
  norm_num only
  rw [show 96 = 32 + 64 by omega,
    Challenge.EvmProof.ModexpMemory.readBytes_add]
  norm_num only
  rw [show 64 = 32 + 32 by omega,
    Challenge.EvmProof.ModexpMemory.readBytes_add]
  repeat rw [Challenge.EvmProof.Bytes.bytesNat_append]
  rw [fpMulInput_r2, fpMulInput_r1, fpMulInput_r0]
  simp only [readBytes, List.length_map, List.length_range,
    List.length_append, Nat.reduceAdd]
  have hword : 256 ^ 32 = Challenge.EvmProof.Limbs.radix := by
    norm_num [Challenge.EvmProof.Limbs.radix, ← pow_mul]
  have hdouble : 256 ^ 64 = Challenge.EvmProof.Limbs.radix ^ 2 := by
    norm_num [Challenge.EvmProof.Limbs.radix, ← pow_mul]
  rw [hword, hdouble]
  unfold Challenge.Bls12381.ProofSupport.Fp.SchoolbookProduct.value
    convFullMul
  simp only [YulEvmCompiler.conv_toNat]
  ring

theorem fpMulInput_runModexp_raw (ahi alo bhi blo : U256) (yst : EvmState) :
    Precompile.runModexp .Osaka (fpMulInput yst ahi alo bhi blo) 500 =
      .success (Precompile.natToBytes
        ((convFullMul (fullMulValue ahi alo bhi blo)).value %
          EvmSemantics.Crypto.Bls12381.p) 48) 500 := by
  exact Challenge.EvmProof.ModexpOne.runModexp_96_1_48
    (fpMulInput_baseSize yst ahi alo bhi blo)
    (fpMulInput_exponentSize yst ahi alo bhi blo)
    (fpMulInput_modulusSize yst ahi alo bhi blo)
    (fpMulInput_base yst ahi alo bhi blo)
    (fpMulInput_exponent yst ahi alo bhi blo)
    (fpMulInput_modulus yst ahi alo bhi blo)
    (by norm_num [EvmSemantics.Crypto.Bls12381.p,
      EvmSemantics.Crypto.Bls12381.absU])

/-- The exact 241-byte source input makes the literal-500-gas MODEXP call
reduce the full schoolbook product modulo the BLS base-field modulus. -/
theorem fpMulInput_runModexp (ahi alo bhi blo : U256) (yst : EvmState)
    (ha : Challenge.Bls12381.ProofSupport.Fp.Canonical
      { hi := YulEvmCompiler.conv ahi, lo := YulEvmCompiler.conv alo })
    (hb : Challenge.Bls12381.ProofSupport.Fp.Canonical
      { hi := YulEvmCompiler.conv bhi, lo := YulEvmCompiler.conv blo }) :
    Precompile.runModexp .Osaka (fpMulInput yst ahi alo bhi blo) 500 =
      .success (Precompile.natToBytes
        ((Challenge.Bls12381.ProofSupport.Fp.value
            { hi := YulEvmCompiler.conv ahi, lo := YulEvmCompiler.conv alo } *
          Challenge.Bls12381.ProofSupport.Fp.value
            { hi := YulEvmCompiler.conv bhi, lo := YulEvmCompiler.conv blo }) %
          EvmSemantics.Crypto.Bls12381.p) 48) 500 := by
  rw [fpMulInput_runModexp_raw]
  rw [conv_fullMulValue,
    Challenge.Bls12381.ProofSupport.Fp.value_schoolbookProduct ha hb]

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
