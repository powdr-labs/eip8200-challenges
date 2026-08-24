import Challenge.Bls12381G1Add.Reference.Proofs.SourceFpInvPowExec

set_option warningAsError true

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics.EVM
open Challenge.Bls12381.ProofSupport

private abbrev LawfulFp := PrimeField.LawfulFp

def sourceLimbs (lo hi : U256) : Fp.Limbs :=
  { lo := YulEvmCompiler.conv lo, hi := YulEvmCompiler.conv hi }

def resultLimbs (result : MontResultValue) : Fp.Limbs :=
  sourceLimbs result.lo result.hi

def sourceBitNat (word bit : Nat) : Nat :=
  if sourceWordBit (BitVec.ofNat 256 word) bit = 0 then 0 else 1

def sourceExponentDown (word : Nat) : Nat → Nat → Nat
  | 0, power => power
  | bit + 1, power =>
      sourceExponentDown word bit (2 * power + sourceBitNat word bit)

def fpPowHighExponent : Nat :=
  sourceExponentDown fpPowHighWordNat 124 1

def fpPowNativeExponent : Nat :=
  sourceExponentDown fpPowLowWordNat 256 fpPowHighExponent

private theorem cancelMontgomery (x y radix : LawfulFp) (hradix : radix ≠ 0) :
    (x * radix) * (y * radix) * radix⁻¹ = (x * y) * radix := by
  field_simp

theorem NativeBitStep.lawful {base acc result : MontResultValue}
    {word bit power : Nat} (hstep : NativeBitStep base acc word bit result)
    (hbaseCanonical : Fp.Canonical (resultLimbs base))
    (haccCanonical : Fp.Canonical (resultLimbs acc))
    (baseValue : LawfulFp)
    (hbaseValue : (Fp.value (resultLimbs base) : LawfulFp) =
      baseValue * (Fp.montgomeryRadix : LawfulFp))
    (haccValue : (Fp.value (resultLimbs acc) : LawfulFp) =
      baseValue ^ power * (Fp.montgomeryRadix : LawfulFp)) :
    Fp.Canonical (resultLimbs result) ∧
      (Fp.value (resultLimbs result) : LawfulFp) =
        baseValue ^ (2 * power + sourceBitNat word bit) *
          (Fp.montgomeryRadix : LawfulFp) := by
  cases hstep with
  | zero square hsquare hzero =>
      have hsquareSpec : Fp.Canonical (resultLimbs result) ∧
          (Fp.value (resultLimbs result) : LawfulFp) =
            (Fp.value (resultLimbs acc) : LawfulFp) *
            (Fp.value (resultLimbs acc) : LawfulFp) *
            (Fp.montgomeryRadix : LawfulFp)⁻¹ := by
        simpa [resultLimbs, sourceLimbs] using
          hsquare.spec haccCanonical haccCanonical
      refine ⟨hsquareSpec.1, ?_⟩
      rw [sourceBitNat, if_pos hzero, Nat.add_zero, hsquareSpec.2, haccValue,
        cancelMontgomery _ _ _ Fp.lawful_montgomeryRadix_ne_zero,
        ← pow_add]
      congr 2
      omega
  | nonzero square output hsquare hnonzero hmultiply =>
      have hsquareSpec : Fp.Canonical (resultLimbs square) ∧
          (Fp.value (resultLimbs square) : LawfulFp) =
            (Fp.value (resultLimbs acc) : LawfulFp) *
            (Fp.value (resultLimbs acc) : LawfulFp) *
            (Fp.montgomeryRadix : LawfulFp)⁻¹ := by
        simpa [resultLimbs, sourceLimbs] using
          hsquare.spec haccCanonical haccCanonical
      have hmultiplySpec : Fp.Canonical (resultLimbs result) ∧
          (Fp.value (resultLimbs result) : LawfulFp) =
            (Fp.value (resultLimbs square) : LawfulFp) *
            (Fp.value (resultLimbs base) : LawfulFp) *
            (Fp.montgomeryRadix : LawfulFp)⁻¹ := by
        simpa [resultLimbs, sourceLimbs] using
          hmultiply.spec hsquareSpec.1 hbaseCanonical
      refine ⟨hmultiplySpec.1, ?_⟩
      rw [sourceBitNat, if_neg hnonzero, hmultiplySpec.2, hsquareSpec.2,
        haccValue, hbaseValue,
        cancelMontgomery _ _ _ Fp.lawful_montgomeryRadix_ne_zero,
        cancelMontgomery _ _ _ Fp.lawful_montgomeryRadix_ne_zero,
        ← pow_add]
      rw [show 2 * power + 1 = (power + power) + 1 by omega, pow_succ]

theorem NativeFoldDown.lawful {base acc result : MontResultValue}
    {word count power : Nat}
    (hfold : NativeFoldDown base word count acc result)
    (hbaseCanonical : Fp.Canonical (resultLimbs base))
    (haccCanonical : Fp.Canonical (resultLimbs acc))
    (baseValue : LawfulFp)
    (hbaseValue : (Fp.value (resultLimbs base) : LawfulFp) =
      baseValue * (Fp.montgomeryRadix : LawfulFp))
    (haccValue : (Fp.value (resultLimbs acc) : LawfulFp) =
      baseValue ^ power * (Fp.montgomeryRadix : LawfulFp)) :
    Fp.Canonical (resultLimbs result) ∧
      (Fp.value (resultLimbs result) : LawfulFp) =
        baseValue ^ (sourceExponentDown word count power) *
          (Fp.montgomeryRadix : LawfulFp) := by
  induction hfold generalizing power with
  | zero => exact ⟨haccCanonical, haccValue⟩
  | @succ bit current next final hstep hrest ih =>
      have hnext := hstep.lawful hbaseCanonical haccCanonical baseValue
        hbaseValue haccValue
      exact ih hnext.1 hnext.2

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem fpPowNativeExponent_eq_pMinus2 :
    fpPowNativeExponent = EvmSemantics.Crypto.Bls12381.p - 2 := by
  decide

private theorem r2Canonical : Fp.Canonical (sourceLimbs fpPowR2Lo fpPowR2Hi) := by
  simpa [sourceLimbs, fpPowR2Lo, fpPowR2Hi, Fp.montgomeryR2,
    Fp.montgomeryR2Lo, Fp.montgomeryR2Hi,
    YulEvmCompiler.conv_eq_ofNat] using Fp.canonical_montgomeryR2

private theorem oneCanonical : Fp.Canonical (sourceLimbs 1 0) := by
  simpa [sourceLimbs, Fp.montgomeryOneInput,
    YulEvmCompiler.conv_eq_ofNat] using Fp.canonical_montgomeryOneInput

private theorem encodeLawful (aHi aLo : U256) (base : MontResultValue)
    (hbase : NativeMontMulResult aLo aHi fpPowR2Lo fpPowR2Hi base.lo base.hi)
    (ha : Fp.Canonical (sourceLimbs aLo aHi)) :
    Fp.Canonical (resultLimbs base) ∧
      (Fp.value (resultLimbs base) : LawfulFp) =
        (Fp.value (sourceLimbs aLo aHi) : LawfulFp) *
          (Fp.montgomeryRadix : LawfulFp) := by
  have hspec : Fp.Canonical (resultLimbs base) ∧
      (Fp.value (resultLimbs base) : LawfulFp) =
        (Fp.value (sourceLimbs aLo aHi) : LawfulFp) *
        (Fp.value (sourceLimbs fpPowR2Lo fpPowR2Hi) : LawfulFp) *
        (Fp.montgomeryRadix : LawfulFp)⁻¹ := by
    simpa [resultLimbs, sourceLimbs] using hbase.spec ha r2Canonical
  refine ⟨hspec.1, ?_⟩
  rw [hspec.2]
  change (Fp.value (sourceLimbs aLo aHi) : LawfulFp) *
      (Fp.value Fp.montgomeryR2 : LawfulFp) *
      (Fp.montgomeryRadix : LawfulFp)⁻¹ = _
  rw [Fp.lawful_montgomeryR2]
  field_simp [Fp.lawful_montgomeryRadix_ne_zero]

set_option maxRecDepth 10000 in
theorem NativePowResult.refines {aHi aLo resultHi resultLo : U256}
    (hresult : NativePowResult aHi aLo resultHi resultLo)
    (ha : Fp.Canonical (sourceLimbs aLo aHi)) :
    YulModexp.Refines (YulModexp.inversionRequest aHi aLo)
      [resultHi, resultLo] := by
  cases hresult with
  | intro base afterHigh afterLow decoded hresultHi hresultLo hbase hhigh hlow hdecode =>
      subst resultHi
      subst resultLo
      have hencoded := encodeLawful aHi aLo base hbase ha
      let baseValue : LawfulFp := Fp.value (sourceLimbs aLo aHi)
      have hinitial : (Fp.value (resultLimbs base) : LawfulFp) =
          baseValue ^ 1 * (Fp.montgomeryRadix : LawfulFp) := by
        rw [pow_one]
        exact hencoded.2
      have hhighResult := hhigh.lawful hencoded.1 hencoded.1 baseValue
        hencoded.2 hinitial
      have hlowResult := hlow.lawful hencoded.1 hhighResult.1 baseValue
        hencoded.2 hhighResult.2
      have hdecoded : Fp.Canonical (resultLimbs decoded) ∧
          (Fp.value (resultLimbs decoded) : LawfulFp) =
            (Fp.value (resultLimbs afterLow) : LawfulFp) *
            (Fp.value (sourceLimbs 1 0) : LawfulFp) *
            (Fp.montgomeryRadix : LawfulFp)⁻¹ := by
        simpa [resultLimbs, sourceLimbs] using
          hdecode.spec hlowResult.1 oneCanonical
      refine ⟨decoded.hi, decoded.lo, rfl, hdecoded.1, ?_⟩
      change (Fp.value (resultLimbs decoded) : LawfulFp) = _
      rw [hdecoded.2, hlowResult.2]
      change baseValue ^ fpPowNativeExponent *
          (Fp.montgomeryRadix : LawfulFp) * 1 *
          (Fp.montgomeryRadix : LawfulFp)⁻¹ = _
      rw [mul_one, mul_assoc,
        mul_inv_cancel₀ Fp.lawful_montgomeryRadix_ne_zero, mul_one,
        fpPowNativeExponent_eq_pMinus2, ← Fp.bytesValue_pMinus2Bytes]
      rfl

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
