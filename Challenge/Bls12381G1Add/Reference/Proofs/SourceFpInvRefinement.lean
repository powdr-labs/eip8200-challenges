import Challenge.Bls12381G1Add.Reference.Proofs.SourceFpInvExec
import Challenge.Bls12381.ProofSupport.FpInv
import Challenge.Bls12381.ProofSupport.FpRepresentation
import Challenge.EvmProof.Bytes
import Challenge.EvmProof.CallMemory
import Challenge.EvmProof.Memory

set_option warningAsError true

/-! # Frozen G1ADD `fpInv` result refinement -/

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open EvmSemantics EvmSemantics.EVM
open YulSemantics YulSemantics.EVM

def fpInvOutputLimbs (yst : EvmState) (hi lo : U256) :
    Challenge.Bls12381.ProofSupport.Fp.Limbs :=
  { hi := YulEvmCompiler.conv (fpInvResult yst hi lo).1
    lo := YulEvmCompiler.conv (fpInvResult yst hi lo).2 }

def fpInvInputLimbs (hi lo : U256) :
    Challenge.Bls12381.ProofSupport.Fp.Limbs :=
  { hi := YulEvmCompiler.conv hi, lo := YulEvmCompiler.conv lo }

private theorem fpInvOutputBytes_size (hi lo : U256) :
    (fpInvOutputBytes hi lo).size = 48 := by
  simp [fpInvOutputBytes, Precompile.natToBytes,
    YulEvmCompiler.BytesLemmas.natToBytesPadded_size]

private theorem fpInvOutputBytes_list_length (hi lo : U256) :
    (fpInvOutputBytes hi lo).toList.length = 48 := by
  rw [YulEvmCompiler.ByteArray.toList_eq_data, Array.length_toList]
  exact fpInvOutputBytes_size hi lo

private theorem fpInvLoad_high (yst : EvmState) (hi lo : U256) :
    loadWord (fpInvCallState yst hi lo).memory 1280 =
      wordFrom (fpInvOutputBytes hi lo).toList 0 := by
  have h := Challenge.EvmProof.loadWord_copyReturn
    (fpInvInputState yst hi lo).memory 1280 48
    (fpInvOutputBytes hi lo).toList 0
    (by norm_num) (by rw [fpInvOutputBytes_list_length]; norm_num)
  simpa [fpInvCallState, fpInvResponse, finishCall] using h

private theorem fpInvLoad_low (yst : EvmState) (hi lo : U256) :
    loadWord (fpInvCallState yst hi lo).memory 1296 =
      wordFrom (fpInvOutputBytes hi lo).toList 16 := by
  have h := Challenge.EvmProof.loadWord_copyReturn
    (fpInvInputState yst hi lo).memory 1280 48
    (fpInvOutputBytes hi lo).toList 16
    (by omega) (by rw [fpInvOutputBytes_list_length])
  simpa [fpInvCallState, fpInvResponse, finishCall] using h

private theorem fpInvHigh_toNat (yst : EvmState) (hi lo : U256) :
    (YulEvmCompiler.conv (fpInvResult yst hi lo).1).toNat =
      Precompile.bytesToNatPadded (fpInvOutputBytes hi lo) 0 16 := by
  let output := fpInvOutputBytes hi lo
  have hmatch := Challenge.EvmProof.MemMatch.byteFrom_toList output
  have hword := hmatch.loadWord 0
  change YulEvmCompiler.conv (wordFrom output.toList 0) =
    MachineState.readWord output 0 at hword
  have hwordNat := congrArg UInt256.toNat hword
  rw [YulEvmCompiler.conv_toNat] at hwordNat
  calc
    (YulEvmCompiler.conv (fpInvResult yst hi lo).1).toNat =
        (loadWord (fpInvCallState yst hi lo).memory 1280).toNat >>> 128 := by
      rw [YulEvmCompiler.conv_toNat]
      rfl
    _ = (wordFrom output.toList 0).toNat >>> 128 := by
      rw [fpInvLoad_high]
    _ = (MachineState.readWord output 0).toNat >>> 128 := by
      rw [hwordNat]
    _ = Precompile.bytesToNatPadded output 0 16 := by
      simpa using Challenge.EvmProof.Bytes.readWord_shift_toNat output 0 16
        (by omega)

private theorem fpInvLow_toNat (yst : EvmState) (hi lo : U256) :
    (YulEvmCompiler.conv (fpInvResult yst hi lo).2).toNat =
      Precompile.bytesToNatPadded (fpInvOutputBytes hi lo) 16 32 := by
  let output := fpInvOutputBytes hi lo
  have hmatch := Challenge.EvmProof.MemMatch.byteFrom_toList output
  have hword := hmatch.loadWord 16
  change YulEvmCompiler.conv (wordFrom output.toList 16) =
    MachineState.readWord output 16 at hword
  have hwordNat := congrArg UInt256.toNat hword
  rw [YulEvmCompiler.conv_toNat] at hwordNat
  calc
    (YulEvmCompiler.conv (fpInvResult yst hi lo).2).toNat =
        (loadWord (fpInvCallState yst hi lo).memory 1296).toNat := by
      rw [YulEvmCompiler.conv_toNat]
      rfl
    _ = (wordFrom output.toList 16).toNat := by
      rw [fpInvLoad_low]
    _ = (MachineState.readWord output 16).toNat := hwordNat
    _ = Precompile.bytesToNatPadded output 16 32 :=
      Challenge.EvmProof.Bytes.readWord_toNat output 16

private theorem fpInvOutputBytes_value (hi lo : U256) :
    Precompile.bytesToNatPadded (fpInvOutputBytes hi lo) 0 48 =
      fpInvReducedValue hi lo := by
  have hp : 0 < EvmSemantics.Crypto.Bls12381.p := by
    norm_num [EvmSemantics.Crypto.Bls12381.p,
      EvmSemantics.Crypto.Bls12381.absU]
  have hlt : fpInvReducedValue hi lo < 256 ^ 48 := by
    exact (Challenge.EvmProof.ModPow.eval_lt hp).trans (by
      norm_num [EvmSemantics.Crypto.Bls12381.p,
        EvmSemantics.Crypto.Bls12381.absU])
  have hencoded := Challenge.EvmProof.Memory.bytesToBigEndianNat_natToBytesPadded
    (fpInvReducedValue hi lo) 48 hlt
  change Data.Bytes.bytesToBigEndianNat
      (MachineState.readPadded (fpInvOutputBytes hi lo) 0 48) = _
  rw [show 48 = (fpInvOutputBytes hi lo).size by
    symm; exact fpInvOutputBytes_size hi lo]
  rw [Challenge.EvmProof.Memory.readPadded_zero_size]
  simpa [fpInvOutputBytes, Precompile.natToBytes] using hencoded

/-- The two loaded output words reconstruct the exact fixed-exponent MODEXP
residue. -/
theorem fpInvOutput_value (yst : EvmState) (hi lo : U256) :
    Challenge.Bls12381.ProofSupport.Fp.value (fpInvOutputLimbs yst hi lo) =
      fpInvReducedValue hi lo := by
  have hsplit := Challenge.EvmProof.Bytes.bytesToNatPadded_add
    (fpInvOutputBytes hi lo) 0 16 32
  rw [show 16 + 32 = 48 by omega, fpInvOutputBytes_value,
    ← fpInvHigh_toNat yst hi lo, ← fpInvLow_toNat yst hi lo] at hsplit
  change
    (YulEvmCompiler.conv (fpInvResult yst hi lo).2).toNat +
        Challenge.EvmProof.Limbs.radix *
          (YulEvmCompiler.conv (fpInvResult yst hi lo).1).toNat = _
  rw [show Challenge.EvmProof.Limbs.radix = 256 ^ 32 by
    norm_num [Challenge.EvmProof.Limbs.radix]]
  omega

/-- The executable inversion helper always returns a canonical field value. -/
theorem canonical_fpInvOutput (yst : EvmState) (hi lo : U256)
    (_hhi : hi.toNat < 2 ^ 128) :
    Challenge.Bls12381.ProofSupport.Fp.Canonical
      (fpInvOutputLimbs yst hi lo) := by
  apply Challenge.Bls12381.ProofSupport.Fp.canonical_of_value_lt
  rw [fpInvOutput_value]
  exact Challenge.EvmProof.ModPow.eval_lt (by
    norm_num [EvmSemantics.Crypto.Bls12381.p,
      EvmSemantics.Crypto.Bls12381.absU])

/-- On a canonical decoded operand, the executable MODEXP helper refines
lawful inversion through the explicit wire-`Fin`/`ZMod` bridge. -/
theorem fpInvOutput_toLawful (yst : EvmState) (hi lo : U256)
    (_ha : Challenge.Bls12381.ProofSupport.Fp.Canonical
      (fpInvInputLimbs hi lo)) :
    Challenge.Bls12381.ProofSupport.PrimeField.finEquiv
        (Challenge.Bls12381.ProofSupport.Fp.toField
          (fpInvOutputLimbs yst hi lo)) =
      (Challenge.Bls12381.ProofSupport.PrimeField.finEquiv
        (Challenge.Bls12381.ProofSupport.Fp.toField
          (fpInvInputLimbs hi lo)))⁻¹ := by
  rw [Challenge.Bls12381.ProofSupport.Fp.finEquiv_toField,
    Challenge.Bls12381.ProofSupport.Fp.finEquiv_toField,
    fpInvOutput_value]
  have hbase :
      hi.toNat * Challenge.EvmProof.Limbs.radix + lo.toNat =
        Challenge.Bls12381.ProofSupport.Fp.value
          (fpInvInputLimbs hi lo) := by
    unfold fpInvInputLimbs Challenge.Bls12381.ProofSupport.Fp.value
    simp only [YulEvmCompiler.conv_toNat]
    rw [Nat.mul_comm, Nat.add_comm]
  unfold fpInvReducedValue
  rw [hbase]
  rw [Challenge.Bls12381.ProofSupport.PrimeField.natCast_modPow_eq_pow
    (Challenge.Bls12381.ProofSupport.Fp.value (fpInvInputLimbs hi lo))
    (EvmSemantics.Crypto.Bls12381.p - 2)
    EvmSemantics.Crypto.Bls12381.p (by
      norm_num [EvmSemantics.Crypto.Bls12381.p,
        EvmSemantics.Crypto.Bls12381.absU])]
  exact Challenge.Bls12381.ProofSupport.Fp.lawful_pow_pMinus2_eq_inv _

/-- The frozen MODEXP helper and the shared source-faithful inversion routine
produce the same canonical limb pair. -/
theorem fpInvOutput_eq_invCanonical (yst : EvmState) (hi lo : U256)
    (ha : Challenge.Bls12381.ProofSupport.Fp.Canonical
      (fpInvInputLimbs hi lo)) :
    fpInvOutputLimbs yst hi lo =
      Challenge.Bls12381.ProofSupport.Fp.invCanonical
        (fpInvInputLimbs hi lo) := by
  have hhi : hi.toNat < 2 ^ 128 := by
    simpa only [fpInvInputLimbs, YulEvmCompiler.conv_toNat] using ha.1
  apply Challenge.Bls12381.ProofSupport.Fp.limbs_ext_of_value_eq
  apply Challenge.Bls12381.ProofSupport.Fp.value_eq_of_lawful_eq
    (canonical_fpInvOutput yst hi lo hhi)
    (Challenge.Bls12381.ProofSupport.Fp.canonical_invCanonical ha)
  have hout := fpInvOutput_toLawful yst hi lo ha
  rw [Challenge.Bls12381.ProofSupport.Fp.finEquiv_toField,
    Challenge.Bls12381.ProofSupport.Fp.finEquiv_toField] at hout
  calc
    (Challenge.Bls12381.ProofSupport.Fp.value
        (fpInvOutputLimbs yst hi lo) :
        Challenge.Bls12381.ProofSupport.PrimeField.LawfulFp) =
        (Challenge.Bls12381.ProofSupport.Fp.value
          (fpInvInputLimbs hi lo) :
          Challenge.Bls12381.ProofSupport.PrimeField.LawfulFp)⁻¹ := hout
    _ = Challenge.Bls12381.ProofSupport.Fp.value
        (Challenge.Bls12381.ProofSupport.Fp.invCanonical
          (fpInvInputLimbs hi lo)) :=
      (Challenge.Bls12381.ProofSupport.Fp.lawful_invCanonical ha).symm

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
