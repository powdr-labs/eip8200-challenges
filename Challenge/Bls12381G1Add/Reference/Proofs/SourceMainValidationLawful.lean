import Challenge.Bls12381G1Add.Reference.Proofs.SourceMainValidationExec

set_option warningAsError true

/-! # Lawful meaning of the G1ADD main validation words -/

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics.EVM

/-- The source padding OR is zero exactly when each 128-bit high half is
zero. -/
theorem mainPaddingValue_eq_zero_iff (yst : EvmState) :
    mainPaddingValue yst = 0 ↔
      mainDecodedWord yst 0 >>> 128 = 0 ∧
      mainDecodedWord yst 64 >>> 128 = 0 ∧
      mainDecodedWord yst 128 >>> 128 = 0 ∧
      mainDecodedWord yst 192 >>> 128 = 0 := by
  unfold mainPaddingValue
  change (((mainDecodedWord yst 0 >>> 128) |||
      (mainDecodedWord yst 64 >>> 128)) |||
      ((mainDecodedWord yst 128 >>> 128) |||
        (mainDecodedWord yst 192 >>> 128)) = (0#256 : BitVec 256)) ↔ _
  rw [BitVec.or_eq_zero_iff, BitVec.or_eq_zero_iff,
    BitVec.or_eq_zero_iff]
  constructor
  · rintro ⟨⟨h0, h64⟩, h128, h192⟩
    exact ⟨h0, h64, h128, h192⟩
  · rintro ⟨h0, h64, h128, h192⟩
    exact ⟨⟨h0, h64⟩, h128, h192⟩

/-- The frozen validity helper returns one exactly for a value below the BLS
modulus. -/
theorem fpValidValue_eq_one_iff (hi lo : U256) :
    fpValidValue hi lo = 1 ↔
      Challenge.Bls12381.ProofSupport.Fp.value (onCurveX hi lo) <
        EvmSemantics.Crypto.Bls12381.p := by
  have hconv := conv_fpValidValue hi lo
  have hcondition :
      Challenge.Bls12381.ProofSupport.Fp.addNeedsCorrection
        (onCurveX hi lo) = Challenge.EvmProof.Limbs.wideGeWord
          (Challenge.Bls12381.ProofSupport.Fp.toWide (onCurveX hi lo))
          Challenge.Bls12381.ProofSupport.Fp.modulusWide :=
    Challenge.Bls12381.ProofSupport.Fp.addNeedsCorrection_eq_wideGeWord _
  have hge :
      (Challenge.Bls12381.ProofSupport.Fp.addNeedsCorrection
        (onCurveX hi lo)).toNat ≠ 0 ↔
      EvmSemantics.Crypto.Bls12381.p ≤
        Challenge.Bls12381.ProofSupport.Fp.value (onCurveX hi lo) := by
    rw [hcondition, Challenge.EvmProof.Limbs.wideGeWord_nonzero_iff,
      Challenge.Bls12381.ProofSupport.Fp.toWide_value,
      Challenge.Bls12381.ProofSupport.Fp.modulusWide_value]
  have hnat := congrArg
    (fun value : EvmSemantics.UInt256 => value.toNat) hconv
  rw [Challenge.EvmProof.Word.word_toNat_isZero] at hnat
  constructor
  · intro hone
    have honeNat := congrArg BitVec.toNat hone
    have hzero :
        (Challenge.Bls12381.ProofSupport.Fp.addNeedsCorrection
          (onCurveX hi lo)).toNat = 0 := by
      have hsource : (fpValidValue hi lo).toNat = 1 := by
        simpa using honeNat
      rw [← YulEvmCompiler.conv_toNat, hnat] at hsource
      split at hsource <;> rename_i hz
      · simpa [onCurveX] using hz
      · omega
    by_contra hnot
    exact (hge.mpr (by omega)) hzero
  · intro hlt
    apply BitVec.toNat_injective
    have hzero :
        (Challenge.Bls12381.ProofSupport.Fp.addNeedsCorrection
          (onCurveX hi lo)).toNat = 0 := by
      by_contra hne
      exact (not_lt_of_ge (hge.mp hne)) hlt
    change (Challenge.Bls12381.ProofSupport.Fp.addNeedsCorrection
      { hi := YulEvmCompiler.conv hi, lo := YulEvmCompiler.conv lo }).toNat =
        0 at hzero
    rw [← YulEvmCompiler.conv_toNat, hnat, hzero]
    rfl

theorem fpValidValue_eq_one_iff_canonical (hi lo : U256) :
    fpValidValue hi lo = 1 ↔
      Challenge.Bls12381.ProofSupport.Fp.Canonical (onCurveX hi lo) := by
  rw [fpValidValue_eq_one_iff]
  constructor
  · exact Challenge.Bls12381.ProofSupport.Fp.canonical_of_value_lt _
  · exact fun h => h.2

private theorem fpValidValue_zero_or_one (hi lo : U256) :
    fpValidValue hi lo = 0 ∨ fpValidValue hi lo = 1 := by
  unfold fpValidValue b2w
  split <;> simp_all

private theorem mainCanonicalValue_ne_zero_iff_ones (yst : EvmState) :
    mainCanonicalValue yst ≠ 0 ↔
      fpValidValue (mainDecodedWord yst 0) (mainDecodedWord yst 32) = 1 ∧
      fpValidValue (mainDecodedWord yst 64) (mainDecodedWord yst 96) = 1 ∧
      fpValidValue (mainDecodedWord yst 128) (mainDecodedWord yst 160) = 1 ∧
      fpValidValue (mainDecodedWord yst 192) (mainDecodedWord yst 224) = 1 := by
  rcases fpValidValue_zero_or_one (mainDecodedWord yst 0)
      (mainDecodedWord yst 32) with hx1 | hx1 <;>
    rcases fpValidValue_zero_or_one (mainDecodedWord yst 64)
      (mainDecodedWord yst 96) with hy1 | hy1 <;>
    rcases fpValidValue_zero_or_one (mainDecodedWord yst 128)
      (mainDecodedWord yst 160) with hx2 | hx2 <;>
    rcases fpValidValue_zero_or_one (mainDecodedWord yst 192)
      (mainDecodedWord yst 224) with hy2 | hy2 <;>
    simp [mainCanonicalValue, hx1, hy1, hx2, hy2]

/-- Passing the four-way source conjunction is exactly canonicality of all
four decoded coordinate values. -/
theorem mainCanonicalValue_ne_zero_iff (yst : EvmState) :
    mainCanonicalValue yst ≠ 0 ↔
      Challenge.Bls12381.ProofSupport.Fp.Canonical (mainX1 yst) ∧
      Challenge.Bls12381.ProofSupport.Fp.Canonical (mainY1 yst) ∧
      Challenge.Bls12381.ProofSupport.Fp.Canonical (mainX2 yst) ∧
      Challenge.Bls12381.ProofSupport.Fp.Canonical (mainY2 yst) := by
  rw [mainCanonicalValue_ne_zero_iff_ones]
  repeat rw [fpValidValue_eq_one_iff_canonical]
  rfl

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
