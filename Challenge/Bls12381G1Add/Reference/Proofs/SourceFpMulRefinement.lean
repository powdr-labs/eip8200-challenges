import Challenge.Bls12381G1Add.Reference.Proofs.SourceFpMulExec
import Challenge.Bls12381.ProofSupport.FpRepresentation
import Challenge.EvmProof.Bytes
import Challenge.EvmProof.CallMemory
import Challenge.EvmProof.Memory

set_option warningAsError true

/-! # Frozen G1ADD `fpMul` result refinement -/

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open EvmSemantics EvmSemantics.EVM
open YulSemantics YulSemantics.EVM

def fpMulOutputLimbs (yst : EvmState) (ahi alo bhi blo : U256) :
    Challenge.Bls12381.ProofSupport.Fp.Limbs :=
  { hi := YulEvmCompiler.conv (fpMulResult yst ahi alo bhi blo).1
    lo := YulEvmCompiler.conv (fpMulResult yst ahi alo bhi blo).2 }

def fpMulLeft (ahi alo : U256) :
    Challenge.Bls12381.ProofSupport.Fp.Limbs :=
  { hi := YulEvmCompiler.conv ahi, lo := YulEvmCompiler.conv alo }

def fpMulRight (bhi blo : U256) :
    Challenge.Bls12381.ProofSupport.Fp.Limbs :=
  { hi := YulEvmCompiler.conv bhi, lo := YulEvmCompiler.conv blo }

private theorem fpMulOutputBytes_size (ahi alo bhi blo : U256) :
    (fpMulOutputBytes ahi alo bhi blo).size = 48 := by
  simp [fpMulOutputBytes, Precompile.natToBytes,
    YulEvmCompiler.BytesLemmas.natToBytesPadded_size]

private theorem fpMulOutputBytes_list_length (ahi alo bhi blo : U256) :
    (fpMulOutputBytes ahi alo bhi blo).toList.length = 48 := by
  rw [YulEvmCompiler.ByteArray.toList_eq_data, Array.length_toList]
  exact fpMulOutputBytes_size ahi alo bhi blo

private theorem fpMulLoad_high (yst : EvmState) (ahi alo bhi blo : U256) :
    loadWord (fpMulCallState yst ahi alo bhi blo).memory 1280 =
      wordFrom (fpMulOutputBytes ahi alo bhi blo).toList 0 := by
  have h := Challenge.EvmProof.loadWord_copyReturn
    (fpMulInputState yst ahi alo bhi blo).memory 1280 48
    (fpMulOutputBytes ahi alo bhi blo).toList 0
    (by norm_num) (by rw [fpMulOutputBytes_list_length]; norm_num)
  simpa [fpMulCallState, fpMulResponse, finishCall] using h

private theorem fpMulLoad_low (yst : EvmState) (ahi alo bhi blo : U256) :
    loadWord (fpMulCallState yst ahi alo bhi blo).memory 1296 =
      wordFrom (fpMulOutputBytes ahi alo bhi blo).toList 16 := by
  have h := Challenge.EvmProof.loadWord_copyReturn
    (fpMulInputState yst ahi alo bhi blo).memory 1280 48
    (fpMulOutputBytes ahi alo bhi blo).toList 16
    (by omega) (by rw [fpMulOutputBytes_list_length])
  simpa [fpMulCallState, fpMulResponse, finishCall] using h

private theorem fpMulHigh_toNat (yst : EvmState) (ahi alo bhi blo : U256) :
    (YulEvmCompiler.conv (fpMulResult yst ahi alo bhi blo).1).toNat =
      Precompile.bytesToNatPadded (fpMulOutputBytes ahi alo bhi blo) 0 16 := by
  let output := fpMulOutputBytes ahi alo bhi blo
  have hmatch := Challenge.EvmProof.MemMatch.byteFrom_toList output
  have hword := hmatch.loadWord 0
  change YulEvmCompiler.conv (wordFrom output.toList 0) =
    MachineState.readWord output 0 at hword
  have hwordNat := congrArg UInt256.toNat hword
  rw [YulEvmCompiler.conv_toNat] at hwordNat
  calc
    (YulEvmCompiler.conv (fpMulResult yst ahi alo bhi blo).1).toNat =
        (loadWord (fpMulCallState yst ahi alo bhi blo).memory 1280).toNat >>>
          128 := by
      rw [YulEvmCompiler.conv_toNat]
      rfl
    _ = (wordFrom output.toList 0).toNat >>> 128 := by
      rw [fpMulLoad_high]
    _ = (MachineState.readWord output 0).toNat >>> 128 := by
      rw [hwordNat]
    _ = Precompile.bytesToNatPadded output 0 16 := by
      simpa using Challenge.EvmProof.Bytes.readWord_shift_toNat output 0 16
        (by omega)

private theorem fpMulLow_toNat (yst : EvmState) (ahi alo bhi blo : U256) :
    (YulEvmCompiler.conv (fpMulResult yst ahi alo bhi blo).2).toNat =
      Precompile.bytesToNatPadded (fpMulOutputBytes ahi alo bhi blo) 16 32 := by
  let output := fpMulOutputBytes ahi alo bhi blo
  have hmatch := Challenge.EvmProof.MemMatch.byteFrom_toList output
  have hword := hmatch.loadWord 16
  change YulEvmCompiler.conv (wordFrom output.toList 16) =
    MachineState.readWord output 16 at hword
  have hwordNat := congrArg UInt256.toNat hword
  rw [YulEvmCompiler.conv_toNat] at hwordNat
  calc
    (YulEvmCompiler.conv (fpMulResult yst ahi alo bhi blo).2).toNat =
        (loadWord (fpMulCallState yst ahi alo bhi blo).memory 1296).toNat := by
      rw [YulEvmCompiler.conv_toNat]
      rfl
    _ = (wordFrom output.toList 16).toNat := by
      rw [fpMulLoad_low]
    _ = (MachineState.readWord output 16).toNat := hwordNat
    _ = Precompile.bytesToNatPadded output 16 32 :=
      Challenge.EvmProof.Bytes.readWord_toNat output 16

private theorem fpMulOutputBytes_value (ahi alo bhi blo : U256) :
    Precompile.bytesToNatPadded (fpMulOutputBytes ahi alo bhi blo) 0 48 =
      fpMulReducedValue ahi alo bhi blo := by
  have hlt : fpMulReducedValue ahi alo bhi blo < 256 ^ 48 := by
    have hp : 0 < EvmSemantics.Crypto.Bls12381.p := by
      norm_num [EvmSemantics.Crypto.Bls12381.p,
        EvmSemantics.Crypto.Bls12381.absU]
    have hmod := Nat.mod_lt
      (convFullMul (fullMulValue ahi alo bhi blo)).value hp
    exact hmod.trans (by
      norm_num [EvmSemantics.Crypto.Bls12381.p,
        EvmSemantics.Crypto.Bls12381.absU])
  have hencoded := Challenge.EvmProof.Memory.bytesToBigEndianNat_natToBytesPadded
    (fpMulReducedValue ahi alo bhi blo) 48 hlt
  change Data.Bytes.bytesToBigEndianNat
      (MachineState.readPadded (fpMulOutputBytes ahi alo bhi blo) 0 48) = _
  rw [show 48 = (fpMulOutputBytes ahi alo bhi blo).size by
    symm; exact fpMulOutputBytes_size ahi alo bhi blo]
  rw [Challenge.EvmProof.Memory.readPadded_zero_size]
  simpa [fpMulOutputBytes, Precompile.natToBytes] using hencoded

/-- The two loaded output words reconstruct the exact MODEXP residue. -/
theorem fpMulOutput_value (yst : EvmState) (ahi alo bhi blo : U256) :
    Challenge.Bls12381.ProofSupport.Fp.value
        (fpMulOutputLimbs yst ahi alo bhi blo) =
      (convFullMul (fullMulValue ahi alo bhi blo)).value %
        EvmSemantics.Crypto.Bls12381.p := by
  have hsplit := Challenge.EvmProof.Bytes.bytesToNatPadded_add
    (fpMulOutputBytes ahi alo bhi blo) 0 16 32
  rw [show 16 + 32 = 48 by omega, fpMulOutputBytes_value,
    ← fpMulHigh_toNat yst ahi alo bhi blo,
    ← fpMulLow_toNat yst ahi alo bhi blo] at hsplit
  change
    (YulEvmCompiler.conv (fpMulResult yst ahi alo bhi blo).2).toNat +
        Challenge.EvmProof.Limbs.radix *
          (YulEvmCompiler.conv (fpMulResult yst ahi alo bhi blo).1).toNat = _
  rw [show Challenge.EvmProof.Limbs.radix = 256 ^ 32 by
    norm_num [Challenge.EvmProof.Limbs.radix]]
  unfold fpMulReducedValue at hsplit
  omega

/-- The executable helper always returns a canonical BLS base-field value. -/
theorem canonical_fpMulOutput (yst : EvmState) (ahi alo bhi blo : U256) :
    Challenge.Bls12381.ProofSupport.Fp.Canonical
      (fpMulOutputLimbs yst ahi alo bhi blo) := by
  apply Challenge.Bls12381.ProofSupport.Fp.canonical_of_value_lt
  rw [fpMulOutput_value]
  exact Nat.mod_lt _ (by
    norm_num [EvmSemantics.Crypto.Bls12381.p,
      EvmSemantics.Crypto.Bls12381.absU])

/-- On canonical decoded operands, the executable helper refines lawful field
multiplication at the existing `Fin p` boundary. -/
theorem fpMulOutput_toField (yst : EvmState) (ahi alo bhi blo : U256)
    (ha : Challenge.Bls12381.ProofSupport.Fp.Canonical
      (fpMulLeft ahi alo))
    (hb : Challenge.Bls12381.ProofSupport.Fp.Canonical
      (fpMulRight bhi blo)) :
    Challenge.Bls12381.ProofSupport.Fp.toField
        (fpMulOutputLimbs yst ahi alo bhi blo) =
      Challenge.Bls12381.ProofSupport.Fp.toField (fpMulLeft ahi alo) *
        Challenge.Bls12381.ProofSupport.Fp.toField (fpMulRight bhi blo) := by
  have hproduct :=
    Challenge.Bls12381.ProofSupport.Fp.value_schoolbookProduct ha hb
  have hout :
      Challenge.Bls12381.ProofSupport.Fp.value
          (fpMulOutputLimbs yst ahi alo bhi blo) =
        (Challenge.Bls12381.ProofSupport.Fp.value (fpMulLeft ahi alo) *
          Challenge.Bls12381.ProofSupport.Fp.value (fpMulRight bhi blo)) %
            EvmSemantics.Crypto.Bls12381.p := by
    rw [fpMulOutput_value, conv_fullMulValue]
    simpa only [fpMulLeft, fpMulRight] using congrArg
      (fun n : Nat => n % EvmSemantics.Crypto.Bls12381.p) hproduct
  apply Fin.ext
  change Challenge.Bls12381.ProofSupport.Fp.value
          (fpMulOutputLimbs yst ahi alo bhi blo) %
        EvmSemantics.Crypto.Bls12381.p =
      (Challenge.Bls12381.ProofSupport.Fp.value (fpMulLeft ahi alo) %
          EvmSemantics.Crypto.Bls12381.p *
        (Challenge.Bls12381.ProofSupport.Fp.value (fpMulRight bhi blo) %
          EvmSemantics.Crypto.Bls12381.p)) %
        EvmSemantics.Crypto.Bls12381.p
  rw [hout]
  simp only [Nat.mod_mod, Nat.mul_mod]

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
