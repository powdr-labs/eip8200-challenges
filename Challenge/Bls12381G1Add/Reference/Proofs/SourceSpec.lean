import Challenge.Bls12381G1Add.Reference.Proofs.SourceInput
import Challenge.Bls12381G1Add.Reference.Proofs.SourceRun
import Challenge.Bls12381G1Add.Spec

set_option warningAsError true

/-! # Complete G1ADD source/spec boundary -/

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM
open Challenge.Bls12381.ProofSupport

private abbrev WirePoint := EvmSemantics.Crypto.Bls12381.Point

/-- The decoded point represented by the first four frozen source words. -/
def sourcePoint1 (yst : EvmState) : WirePoint :=
  if mainInf1 yst = 0 then
    .affine (Fp.toField (sourceField yst 0))
      (Fp.toField (sourceField yst 64))
  else .infinity

/-- The decoded point represented by the second four frozen source words. -/
def sourcePoint2 (yst : EvmState) : WirePoint :=
  if mainInf2 yst = 0 then
    .affine (Fp.toField (sourceField yst 128))
      (Fp.toField (sourceField yst 192))
  else .infinity

private theorem fpZeroValue_eq_one_iff (hi lo : U256) :
    fpZeroValue hi lo = 1 ↔ hi = 0 ∧ lo = 0 := by
  unfold fpZeroValue b2w
  split <;> split <;> norm_num <;> simp_all

private theorem fpZeroValue_zero_or_one (hi lo : U256) :
    fpZeroValue hi lo = 0 ∨ fpZeroValue hi lo = 1 := by
  unfold fpZeroValue b2w
  split <;> split <;> norm_num <;> decide

private theorem sourceField_value_eq_zero_iff (yst : EvmState) (offset : Nat) :
    Fp.value (sourceField yst offset) = 0 ↔
      mainDecodedWord yst offset = 0 ∧
        mainDecodedWord yst (offset + 32) = 0 := by
  unfold sourceField onCurveX Fp.value Challenge.EvmProof.Limbs.radix
  rw [YulEvmCompiler.conv_toNat, YulEvmCompiler.conv_toNat]
  constructor
  · intro h
    have hloNat : (mainDecodedWord yst (offset + 32)).toNat = 0 := by omega
    have hhiNat : (mainDecodedWord yst offset).toNat = 0 := by
      have hradix : 0 < 2 ^ 256 := Nat.pow_pos (by omega)
      by_contra hne
      have : 2 ^ 256 ≤
          2 ^ 256 * (mainDecodedWord yst offset).toNat :=
        calc
          2 ^ 256 = 2 ^ 256 * 1 := by rw [Nat.mul_one]
          _ ≤ 2 ^ 256 * (mainDecodedWord yst offset).toNat :=
            Nat.mul_le_mul_left _ (Nat.one_le_iff_ne_zero.mpr hne)
      omega
    exact ⟨BitVec.eq_of_toNat_eq hhiNat, BitVec.eq_of_toNat_eq hloNat⟩
  · rintro ⟨hhi, hlo⟩
    rw [hhi, hlo]
    rfl

private theorem toField_val_eq_value {a : Fp.Limbs} (ha : Fp.Canonical a) :
    (Fp.toField a).val = Fp.value a := by
  unfold Fp.toField
  rw [Fin.val_ofNat, Nat.mod_eq_of_lt ha.2]

private theorem mainInf1_ne_zero_iff (yst : EvmState) :
    mainInf1 yst ≠ 0 ↔
      Fp.value (sourceField yst 0) = 0 ∧
        Fp.value (sourceField yst 64) = 0 := by
  rw [sourceField_value_eq_zero_iff, sourceField_value_eq_zero_iff]
  have hland : mainInf1 yst ≠ 0 ↔
      fpZeroValue (mainDecodedWord yst 0) (mainDecodedWord yst 32) = 1 ∧
        fpZeroValue (mainDecodedWord yst 64) (mainDecodedWord yst 96) = 1 := by
    rcases fpZeroValue_zero_or_one (mainDecodedWord yst 0)
        (mainDecodedWord yst 32) with hx | hx <;>
      rcases fpZeroValue_zero_or_one (mainDecodedWord yst 64)
        (mainDecodedWord yst 96) with hy | hy <;>
      simp [mainInf1, hx, hy]
  exact hland.trans (and_congr
    (fpZeroValue_eq_one_iff _ _) (fpZeroValue_eq_one_iff _ _))

private theorem mainInf2_ne_zero_iff (yst : EvmState) :
    mainInf2 yst ≠ 0 ↔
      Fp.value (sourceField yst 128) = 0 ∧
        Fp.value (sourceField yst 192) = 0 := by
  rw [sourceField_value_eq_zero_iff, sourceField_value_eq_zero_iff]
  have hland : mainInf2 yst ≠ 0 ↔
      fpZeroValue (mainDecodedWord yst 128) (mainDecodedWord yst 160) = 1 ∧
        fpZeroValue (mainDecodedWord yst 192) (mainDecodedWord yst 224) = 1 := by
    rcases fpZeroValue_zero_or_one (mainDecodedWord yst 128)
        (mainDecodedWord yst 160) with hx | hx <;>
      rcases fpZeroValue_zero_or_one (mainDecodedWord yst 192)
        (mainDecodedWord yst 224) with hy | hy <;>
      simp [mainInf2, hx, hy]
  exact hland.trans (and_congr
    (fpZeroValue_eq_one_iff _ _) (fpZeroValue_eq_one_iff _ _))

private theorem mainAffine1_eq_ofWire (yst : EvmState) :
    mainAffine1 yst = G1Affine.ofWire
      (.affine (Fp.toField (sourceField yst 0))
        (Fp.toField (sourceField yst 64))) := by
  simp [mainAffine1, G1Affine.ofWire, sourceField, mainX1, mainY1,
    onCurveX, onCurveY, Fp.finEquiv_toField]

private theorem mainAffine2_eq_ofWire (yst : EvmState) :
    mainAffine2 yst = G1Affine.ofWire
      (.affine (Fp.toField (sourceField yst 128))
        (Fp.toField (sourceField yst 192))) := by
  simp [mainAffine2, G1Affine.ofWire, sourceField, mainX2, mainY2,
    onCurveX, onCurveY, Fp.finEquiv_toField]

/-- Successful source validation of the first point is exactly successful
ordinary G1 decoding of the source-represented point. -/
theorem decodeG1_first_eq_sourcePoint (yst : EvmState) (input : ByteArray)
    (hcalldata : yst.env.calldata = input.toList) (hsize : input.size = 256)
    (hpadding : mainPaddingValue yst = 0)
    (hcanonical : mainCanonicalValue yst ≠ 0)
    (hcurve : mainCurve1ConditionValue yst = 0) :
    Codec.decodeG1 input 0 = some (sourcePoint1 yst) := by
  have hpads := (mainPaddingValue_eq_zero_iff_codec yst input hcalldata hsize).mp
    hpadding
  have hcans := (mainCanonicalValue_ne_zero_iff yst).mp hcanonical
  have hx : Codec.decodeFp input 0 = some (Fp.toField (sourceField yst 0)) :=
    (decodeFp_eq_some_sourceField yst input hcalldata 0 (by omega) (by omega)).mpr
      ⟨hpads.1, by simpa [sourceField, mainX1] using hcans.1⟩
  have hy : Codec.decodeFp input 64 = some (Fp.toField (sourceField yst 64)) :=
    (decodeFp_eq_some_sourceField yst input hcalldata 1 (by omega) (by omega)).mpr
      ⟨hpads.2.1, by
        simpa [sourceField, mainY1, onCurveX, onCurveY] using hcans.2.1⟩
  rw [Codec.decodeG1_of_components _ _ hx (by simpa [Codec.fpBytes] using hy)]
  by_cases hinf : mainInf1 yst = 0
  · have hnonzero : ¬((Fp.toField (sourceField yst 0)).val = 0 ∧
        (Fp.toField (sourceField yst 64)).val = 0) := by
      rintro ⟨hx0, hy0⟩
      have hvalues : Fp.value (sourceField yst 0) = 0 ∧
          Fp.value (sourceField yst 64) = 0 := by
        rw [← toField_val_eq_value (by simpa [sourceField, mainX1] using hcans.1),
          ← toField_val_eq_value (by
            simpa [sourceField, mainY1, onCurveX, onCurveY] using hcans.2.1)]
        exact ⟨hx0, hy0⟩
      exact ((mainInf1_ne_zero_iff yst).mpr hvalues) hinf
    have hcurveLawful : G1Affine.OnCurve (mainAffine1 yst) :=
      (mainCurve1ConditionValue_eq_zero_iff yst hcans.1 hcans.2.1).mp hcurve
        |>.resolve_left (fun hne => hne hinf)
    have hcurveWire : EvmSemantics.Crypto.Bls12381.onCurve
        (Fp.toField (sourceField yst 0))
        (Fp.toField (sourceField yst 64)) = true := by
      have hcurveLawful' : G1Affine.OnCurve (G1Affine.ofWire
          (.affine (Fp.toField (sourceField yst 0))
            (Fp.toField (sourceField yst 64)))) := by
        rw [← mainAffine1_eq_ofWire yst]
        exact hcurveLawful
      exact G1Affine.onCurve_toWire hcurveLawful'
    rw [if_neg hnonzero, if_pos hcurveWire]
    simp [sourcePoint1, hinf]
  · obtain ⟨hx0, hy0⟩ := (mainInf1_ne_zero_iff yst).mp hinf
    have hxval : (Fp.toField (sourceField yst 0)).val = 0 := by
      rw [toField_val_eq_value (by simpa [sourceField, mainX1] using hcans.1), hx0]
    have hyval : (Fp.toField (sourceField yst 64)).val = 0 := by
      rw [toField_val_eq_value (by
        simpa [sourceField, mainY1, onCurveX, onCurveY] using hcans.2.1), hy0]
    rw [if_pos ⟨hxval, hyval⟩]
    unfold sourcePoint1
    rw [if_neg hinf]

/-- Successful source validation of the second point is exactly successful
ordinary G1 decoding of the source-represented point. -/
theorem decodeG1_second_eq_sourcePoint (yst : EvmState) (input : ByteArray)
    (hcalldata : yst.env.calldata = input.toList) (hsize : input.size = 256)
    (hpadding : mainPaddingValue yst = 0)
    (hcanonical : mainCanonicalValue yst ≠ 0)
    (hcurve : mainCurve2ConditionValue yst = 0) :
    Codec.decodeG1 input 128 = some (sourcePoint2 yst) := by
  have hpads := (mainPaddingValue_eq_zero_iff_codec yst input hcalldata hsize).mp
    hpadding
  have hcans := (mainCanonicalValue_ne_zero_iff yst).mp hcanonical
  have hx : Codec.decodeFp input 128 = some (Fp.toField (sourceField yst 128)) :=
    (decodeFp_eq_some_sourceField yst input hcalldata 2 (by omega) (by omega)).mpr
      ⟨hpads.2.2.1, by
        simpa [sourceField, mainX2, onCurveX, onCurveY] using hcans.2.2.1⟩
  have hy : Codec.decodeFp input 192 = some (Fp.toField (sourceField yst 192)) :=
    (decodeFp_eq_some_sourceField yst input hcalldata 3 (by omega) (by omega)).mpr
      ⟨hpads.2.2.2, by
        simpa [sourceField, mainY2, onCurveX, onCurveY] using hcans.2.2.2⟩
  rw [Codec.decodeG1_of_components _ _ hx (by simpa [Codec.fpBytes] using hy)]
  by_cases hinf : mainInf2 yst = 0
  · have hnonzero : ¬((Fp.toField (sourceField yst 128)).val = 0 ∧
        (Fp.toField (sourceField yst 192)).val = 0) := by
      rintro ⟨hx0, hy0⟩
      have hvalues : Fp.value (sourceField yst 128) = 0 ∧
          Fp.value (sourceField yst 192) = 0 := by
        rw [← toField_val_eq_value (by
              simpa [sourceField, mainX2, onCurveX, onCurveY] using hcans.2.2.1),
          ← toField_val_eq_value (by
            simpa [sourceField, mainY2, onCurveX, onCurveY] using hcans.2.2.2)]
        exact ⟨hx0, hy0⟩
      exact ((mainInf2_ne_zero_iff yst).mpr hvalues) hinf
    have hcurveLawful : G1Affine.OnCurve (mainAffine2 yst) :=
      (mainCurve2ConditionValue_eq_zero_iff yst hcans.2.2.1 hcans.2.2.2).mp
          hcurve
        |>.resolve_left (fun hne => hne hinf)
    have hcurveWire : EvmSemantics.Crypto.Bls12381.onCurve
        (Fp.toField (sourceField yst 128))
        (Fp.toField (sourceField yst 192)) = true := by
      have hcurveLawful' : G1Affine.OnCurve (G1Affine.ofWire
          (.affine (Fp.toField (sourceField yst 128))
            (Fp.toField (sourceField yst 192)))) := by
        rw [← mainAffine2_eq_ofWire yst]
        exact hcurveLawful
      exact G1Affine.onCurve_toWire hcurveLawful'
    rw [if_neg hnonzero, if_pos hcurveWire]
    simp [sourcePoint2, hinf]
  · obtain ⟨hx0, hy0⟩ := (mainInf2_ne_zero_iff yst).mp hinf
    have hxval : (Fp.toField (sourceField yst 128)).val = 0 := by
      rw [toField_val_eq_value (by
        simpa [sourceField, mainX2, onCurveX, onCurveY] using hcans.2.2.1), hx0]
    have hyval : (Fp.toField (sourceField yst 192)).val = 0 := by
      rw [toField_val_eq_value (by
        simpa [sourceField, mainY2, onCurveX, onCurveY] using hcans.2.2.2), hy0]
    rw [if_pos ⟨hxval, hyval⟩]
    unfold sourcePoint2
    rw [if_neg hinf]

private theorem decodeG1_first_eq_none_of_curve (yst : EvmState)
    (input : ByteArray) (hcalldata : yst.env.calldata = input.toList)
    (hsize : input.size = 256) (hpadding : mainPaddingValue yst = 0)
    (hcanonical : mainCanonicalValue yst ≠ 0)
    (hcurve : mainCurve1ConditionValue yst ≠ 0) :
    Codec.decodeG1 input 0 = none := by
  have hpads := (mainPaddingValue_eq_zero_iff_codec yst input hcalldata hsize).mp
    hpadding
  have hcans := (mainCanonicalValue_ne_zero_iff yst).mp hcanonical
  have hx : Codec.decodeFp input 0 = some (Fp.toField (sourceField yst 0)) :=
    (decodeFp_eq_some_sourceField yst input hcalldata 0 (by omega) (by omega)).mpr
      ⟨hpads.1, by simpa [sourceField, mainX1] using hcans.1⟩
  have hy : Codec.decodeFp input 64 = some (Fp.toField (sourceField yst 64)) :=
    (decodeFp_eq_some_sourceField yst input hcalldata 1 (by omega) (by omega)).mpr
      ⟨hpads.2.1, by
        simpa [sourceField, mainY1, onCurveX, onCurveY] using hcans.2.1⟩
  have hcondition := (mainCurve1ConditionValue_eq_zero_iff yst hcans.1
    hcans.2.1).not.mp hcurve
  push Not at hcondition
  have hinf : mainInf1 yst = 0 := hcondition.1
  have hnonzero : ¬((Fp.toField (sourceField yst 0)).val = 0 ∧
      (Fp.toField (sourceField yst 64)).val = 0) := by
    rintro ⟨hx0, hy0⟩
    have hvalues : Fp.value (sourceField yst 0) = 0 ∧
        Fp.value (sourceField yst 64) = 0 := by
      rw [← toField_val_eq_value (by simpa [sourceField, mainX1] using hcans.1),
        ← toField_val_eq_value (by
          simpa [sourceField, mainY1, onCurveX, onCurveY] using hcans.2.1)]
      exact ⟨hx0, hy0⟩
    exact ((mainInf1_ne_zero_iff yst).mpr hvalues) hinf
  have hcurveWire : EvmSemantics.Crypto.Bls12381.onCurve
      (Fp.toField (sourceField yst 0))
      (Fp.toField (sourceField yst 64)) = false := by
    apply Bool.eq_false_iff.mpr
    intro hwire
    apply hcondition.2
    rw [mainAffine1_eq_ofWire yst]
    exact G1Affine.onCurve_ofWire hwire
  exact Codec.decodeG1_eq_none_of_offCurve hx
    (by simpa [Codec.fpBytes] using hy) hnonzero hcurveWire

private theorem decodeG1_second_eq_none_of_curve (yst : EvmState)
    (input : ByteArray) (hcalldata : yst.env.calldata = input.toList)
    (hsize : input.size = 256) (hpadding : mainPaddingValue yst = 0)
    (hcanonical : mainCanonicalValue yst ≠ 0)
    (hcurve : mainCurve2ConditionValue yst ≠ 0) :
    Codec.decodeG1 input 128 = none := by
  have hpads := (mainPaddingValue_eq_zero_iff_codec yst input hcalldata hsize).mp
    hpadding
  have hcans := (mainCanonicalValue_ne_zero_iff yst).mp hcanonical
  have hx : Codec.decodeFp input 128 = some (Fp.toField (sourceField yst 128)) :=
    (decodeFp_eq_some_sourceField yst input hcalldata 2 (by omega) (by omega)).mpr
      ⟨hpads.2.2.1, by
        simpa [sourceField, mainX2, onCurveX, onCurveY] using hcans.2.2.1⟩
  have hy : Codec.decodeFp input 192 = some (Fp.toField (sourceField yst 192)) :=
    (decodeFp_eq_some_sourceField yst input hcalldata 3 (by omega) (by omega)).mpr
      ⟨hpads.2.2.2, by
        simpa [sourceField, mainY2, onCurveX, onCurveY] using hcans.2.2.2⟩
  have hcondition := (mainCurve2ConditionValue_eq_zero_iff yst hcans.2.2.1
    hcans.2.2.2).not.mp hcurve
  push Not at hcondition
  have hinf : mainInf2 yst = 0 := hcondition.1
  have hnonzero : ¬((Fp.toField (sourceField yst 128)).val = 0 ∧
      (Fp.toField (sourceField yst 192)).val = 0) := by
    rintro ⟨hx0, hy0⟩
    have hvalues : Fp.value (sourceField yst 128) = 0 ∧
        Fp.value (sourceField yst 192) = 0 := by
      rw [← toField_val_eq_value (by
            simpa [sourceField, mainX2, onCurveX, onCurveY] using hcans.2.2.1),
        ← toField_val_eq_value (by
          simpa [sourceField, mainY2, onCurveX, onCurveY] using hcans.2.2.2)]
      exact ⟨hx0, hy0⟩
    exact ((mainInf2_ne_zero_iff yst).mpr hvalues) hinf
  have hcurveWire : EvmSemantics.Crypto.Bls12381.onCurve
      (Fp.toField (sourceField yst 128))
      (Fp.toField (sourceField yst 192)) = false := by
    apply Bool.eq_false_iff.mpr
    intro hwire
    apply hcondition.2
    rw [mainAffine2_eq_ofWire yst]
    exact G1Affine.onCurve_ofWire hwire
  exact Codec.decodeG1_eq_none_of_offCurve hx
    (by simpa [Codec.fpBytes] using hy) hnonzero hcurveWire

private theorem mainCanonicalValue_ne_zero_finite (yst : EvmState)
    (hcanonical : mainCanonicalValue yst ≠ 0) :
    Fp.Canonical (mainFinitePostX1 yst) ∧
      Fp.Canonical (mainFinitePostY1 yst) ∧
      Fp.Canonical (mainFinitePostX2 yst) ∧
      Fp.Canonical (mainFiniteUnequalY2 yst) := by
  obtain ⟨hx1, hy1, hx2, hy2⟩ :=
    (mainCanonicalValue_ne_zero_iff yst).mp hcanonical
  refine ⟨?_, ?_, ?_, ?_⟩
  · change Fp.Canonical (sourceField yst 0)
    simpa [sourceField, mainX1] using hx1
  · change Fp.Canonical (sourceField yst 64)
    simpa [sourceField, mainY1, onCurveX, onCurveY] using hy1
  · change Fp.Canonical (sourceField yst 128)
    simpa [sourceField, mainX2, onCurveX, onCurveY] using hx2
  · change Fp.Canonical (sourceField yst 192)
    simpa [sourceField, mainY2, onCurveX, onCurveY] using hy2

private def toLawful (a : Fp.Limbs) : PrimeField.LawfulFp :=
  PrimeField.finEquiv (Fp.toField a)

private theorem mainFinitePostX1_eq_source (yst : EvmState) :
    mainFinitePostX1 yst = sourceField yst 0 := rfl

private theorem mainFinitePostY1_eq_source (yst : EvmState) :
    mainFinitePostY1 yst = sourceField yst 64 := rfl

private theorem mainFinitePostX2_eq_source (yst : EvmState) :
    mainFinitePostX2 yst = sourceField yst 128 := rfl

private theorem mainFiniteUnequalY2_eq_source (yst : EvmState) :
    mainFiniteUnequalY2 yst = sourceField yst 192 := rfl

private theorem mainFiniteDoubleX_eq_source (yst : EvmState) :
    mainFiniteDoubleX yst = sourceField yst 0 := rfl

private theorem mainFiniteDoubleY_eq_source (yst : EvmState) :
    mainFiniteDoubleY yst = sourceField yst 64 := rfl

private theorem mainFinitePostLambda_double_eq (yst : EvmState) :
    mainFinitePostLambda (mainFiniteDoubleLambdaWords yst) =
      mainFiniteDoubleLambda yst := rfl

private theorem mainFiniteXEq_one_lawful (yst : EvmState)
    (hxeq : mainFiniteXEqValue yst = 1) :
    toLawful (mainFinitePostX2 yst) = toLawful (mainFinitePostX1 yst) := by
  obtain ⟨hhi, hlo⟩ := (mainFiniteXEq_eq_one_iff yst).mp hxeq
  simp [toLawful, mainFinitePostX1, mainFinitePostX2, hhi, hlo]

private theorem mainFiniteYZero_zero_lawful (yst : EvmState)
    (hy : Fp.Canonical (mainFinitePostY1 yst))
    (hyzero : mainFiniteYZeroValue yst = 0) :
    toLawful (mainFinitePostY1 yst) ≠ 0 := by
  intro hzero
  have hfield : Fp.toField (mainFinitePostY1 yst) = 0 := by
    apply PrimeField.finEquiv.injective
    simpa [toLawful] using hzero
  have hvalue : Fp.value (mainFinitePostY1 yst) = 0 := by
    rw [← toField_val_eq_value hy, hfield]
    rfl
  have hwords : mainDecodedWord yst 64 = 0 ∧
      mainDecodedWord yst 96 = 0 := by
    have hvalue' : Fp.value (sourceField yst 64) = 0 := by
      change Fp.value (sourceField yst 64) = 0 at hvalue
      exact hvalue
    exact (sourceField_value_eq_zero_iff yst 64).mp hvalue'
  have hone : mainFiniteYZeroValue yst = 1 := by
    apply (fpZeroValue_eq_one_iff _ _).mpr
    exact hwords
  exact (by decide : (0 : U256) ≠ 1) (hyzero.symm.trans hone)

private theorem fpEqValue_zero_or_one (ahi alo bhi blo : U256) :
    fpEqValue ahi alo bhi blo = 0 ∨ fpEqValue ahi alo bhi blo = 1 := by
  unfold fpEqValue b2w
  split <;> split <;> norm_num <;> decide

private theorem mainFiniteYEq_one_lawful (yst : EvmState)
    (hyeq : mainFiniteYEqValue yst = 1) :
    toLawful (mainFiniteUnequalY2 yst) =
      toLawful (mainFinitePostY1 yst) := by
  obtain ⟨hhi, hlo⟩ := (mainFiniteYEq_eq_one_iff yst).mp hyeq
  change toLawful (sourceField yst 192) = toLawful (sourceField yst 64)
  simp [toLawful, sourceField, hhi, hlo]

private theorem mainFiniteYEq_zero_lawful (yst : EvmState)
    (hy1 : Fp.Canonical (mainFinitePostY1 yst))
    (hy2 : Fp.Canonical (mainFiniteUnequalY2 yst))
    (hyeq : mainFiniteYEqValue yst = 0) :
    toLawful (mainFinitePostY1 yst) ≠
      toLawful (mainFiniteUnequalY2 yst) := by
  intro heq
  have hvalue := Fp.value_eq_of_lawful_eq hy1 hy2 heq
  have hlimbs := Fp.limbs_ext_of_value_eq hvalue
  have hone : mainFiniteYEqValue yst = 1 := by
    apply (mainFiniteYEq_eq_one_iff yst).mpr
    constructor
    · apply YulEvmCompiler.conv_injective
      exact congrArg Fp.Limbs.hi hlimbs
    · apply YulEvmCompiler.conv_injective
      exact congrArg Fp.Limbs.lo hlimbs
  exact (by decide : (0 : U256) ≠ 1) (hyeq.symm.trans hone)

private theorem mainFiniteYZero_nonzero_lawful (yst : EvmState)
    (hy : Fp.Canonical (mainFinitePostY1 yst))
    (hyzero : mainFiniteYZeroValue yst ≠ 0) :
    toLawful (mainFinitePostY1 yst) = 0 := by
  have hone : mainFiniteYZeroValue yst = 1 := by
    rcases fpZeroValue_zero_or_one (mainDecodedWord yst 64)
      (mainDecodedWord yst 96) with hzero | hone
    · exact False.elim (hyzero hzero)
    · exact hone
  obtain ⟨hhi, hlo⟩ := (fpZeroValue_eq_one_iff _ _).mp hone
  have hfield : Fp.toField (mainFinitePostY1 yst) = 0 := by
    change Fp.toField (sourceField yst 64) = 0
    apply Fin.ext
    have hy' : Fp.Canonical (sourceField yst 64) := by
      change Fp.Canonical (sourceField yst 64) at hy
      exact hy
    rw [toField_val_eq_value hy']
    simp [Fp.value, sourceField, onCurveX, hhi, hlo,
      Challenge.EvmProof.Limbs.radix]
  change PrimeField.finEquiv (Fp.toField (mainFinitePostY1 yst)) = 0
  rw [hfield]
  rfl

private theorem ofWire_sourcePoint1_finite (yst : EvmState)
    (hfirst : mainInf1 yst = 0) :
    G1Affine.ofWire (sourcePoint1 yst) =
      .affine (toLawful (mainFinitePostX1 yst))
        (toLawful (mainFinitePostY1 yst)) := by
  rw [sourcePoint1, if_pos hfirst]
  simp [G1Affine.ofWire, toLawful, mainFinitePostX1_eq_source,
    mainFinitePostY1_eq_source]

private theorem ofWire_sourcePoint2_finite (yst : EvmState)
    (hsecond : mainInf2 yst = 0) :
    G1Affine.ofWire (sourcePoint2 yst) =
      .affine (toLawful (mainFinitePostX2 yst))
        (toLawful (mainFiniteUnequalY2 yst)) := by
  rw [sourcePoint2, if_pos hsecond]
  simp [G1Affine.ofWire, toLawful, mainFinitePostX2_eq_source,
    mainFiniteUnequalY2_eq_source]

private theorem ofWire_sourcePoint1_infinity (yst : EvmState)
    (hfirst : mainInf1 yst ≠ 0) :
    G1Affine.ofWire (sourcePoint1 yst) = .infinity := by
  rw [sourcePoint1, if_neg hfirst]
  rfl

private theorem ofWire_sourcePoint2_infinity (yst : EvmState)
    (hsecond : mainInf2 yst ≠ 0) :
    G1Affine.ofWire (sourcePoint2 yst) = .infinity := by
  rw [sourcePoint2, if_neg hsecond]
  rfl

private theorem mainInf1_eq_one_of_ne (yst : EvmState)
    (hfirst : mainInf1 yst ≠ 0) : mainInf1 yst = 1 := by
  rcases fpZeroValue_zero_or_one (mainDecodedWord yst 0)
      (mainDecodedWord yst 32) with hx | hx <;>
    rcases fpZeroValue_zero_or_one (mainDecodedWord yst 64)
      (mainDecodedWord yst 96) with hy | hy <;>
    simp [mainInf1, hx, hy] at hfirst ⊢

private theorem mainInf2_eq_one_of_ne (yst : EvmState)
    (hsecond : mainInf2 yst ≠ 0) : mainInf2 yst = 1 := by
  rcases fpZeroValue_zero_or_one (mainDecodedWord yst 128)
      (mainDecodedWord yst 160) with hx | hx <;>
    rcases fpZeroValue_zero_or_one (mainDecodedWord yst 192)
      (mainDecodedWord yst 224) with hy | hy <;>
    simp [mainInf2, hx, hy] at hsecond ⊢

private theorem run_valid_matches_decoded (yst : EvmState) (input : ByteArray)
    (hcalldata : yst.env.calldata = input.toList) (hsize : input.size = 256)
    (hpadding : mainPaddingValue yst = 0)
    (hcanonical : mainCanonicalValue yst ≠ 0)
    (hcurve1 : mainCurve1ConditionValue yst = 0)
    (hcurve2 : mainCurve2ConditionValue yst = 0) :
    ∃ yst', Run Challenge.Bls12381G1Add.ProofSupport.Yul.localDialect
        Compilation.referenceCompiledBlock yst [] yst' .halt ∧
      yst'.halted = some (.ret,
        (Codec.encodeG1 (G1Affine.toWire
          (G1Affine.add (G1Affine.ofWire (sourcePoint1 yst))
            (G1Affine.ofWire (sourcePoint2 yst))))).toList) := by
  have hlength : yst.env.calldata.length = 256 := by
    rw [hcalldata, YulEvmCompiler.ByteArray.toList_eq_data,
      Array.length_toList]
    change input.size = 256 at hsize
    exact hsize
  obtain ⟨hx1, hy1, hx2, hy2⟩ :=
    mainCanonicalValue_ne_zero_finite yst hcanonical
  by_cases hfirst : mainInf1 yst = 0
  · by_cases hsecond : mainInf2 yst = 0
    · rcases fpEqValue_zero_or_one (mainDecodedWord yst 0)
          (mainDecodedWord yst 32) (mainDecodedWord yst 128)
          (mainDecodedWord yst 160) with hxeq | hxeq
      · rcases main_unequal_yulContract yst
            ⟨hlength, hpadding, hcanonical, hcurve1, hcurve2, hfirst,
              hsecond, hxeq, hx1, hy1, hx2, hy2⟩ with
          ⟨finalEnv, final, outcome, hrun, henv, houtcome, hreturned⟩
        subst finalEnv
        subst outcome
        refine ⟨final, hrun, ?_⟩
        calc
          final.halted = some (.ret, mainFiniteUnequalExpected yst) := hreturned
          _ = some (.ret,
              (Codec.encodeG1 (G1Affine.toWire
                (G1Affine.add (G1Affine.ofWire (sourcePoint1 yst))
                  (G1Affine.ofWire (sourcePoint2 yst))))).toList) := by
            unfold mainFiniteUnequalExpected
            rw [mainFinitePostX1_eq_source, mainFinitePostY1_eq_source,
              mainFinitePostX2_eq_source, mainFiniteUnequalY2_eq_source]
            simp [sourcePoint1, sourcePoint2, hfirst, hsecond,
              G1Affine.ofWire, Fp.finEquiv_toField]
      · rcases fpEqValue_zero_or_one (mainDecodedWord yst 64)
            (mainDecodedWord yst 96) (mainDecodedWord yst 192)
            (mainDecodedWord yst 224) with hyeq | hyeq
        · have hrun := run_main_opposite yst hlength hpadding hcanonical
            hcurve1 hcurve2 hfirst hsecond hxeq hyeq
          refine ⟨_, hrun, ?_⟩
          have hxEq := mainFiniteXEq_one_lawful yst hxeq
          have hyne := mainFiniteYEq_zero_lawful yst hy1 hy2 hyeq
          have hcans := (mainCanonicalValue_ne_zero_iff yst).mp hcanonical
          have hon1 := (mainCurve1ConditionValue_eq_zero_iff yst hcans.1
            hcans.2.1).mp hcurve1 |>.resolve_left (fun h => h hfirst)
          have hon2 := (mainCurve2ConditionValue_eq_zero_iff yst hcans.2.2.1
            hcans.2.2.2).mp hcurve2 |>.resolve_left (fun h => h hsecond)
          have hopposite : toLawful (mainFinitePostY1 yst) +
              toLawful (mainFiniteUnequalY2 yst) = 0 := by
            have hsquares : toLawful (mainFinitePostY1 yst) ^ 2 =
                toLawful (mainFiniteUnequalY2 yst) ^ 2 := by
              change (match mainAffine1 yst with
                | .infinity => True
                | .affine x y => y ^ 2 = x ^ 3 + G1Affine.curve.a * x +
                    G1Affine.curve.b) at hon1
              change (match mainAffine2 yst with
                | .infinity => True
                | .affine x y => y ^ 2 = x ^ 3 + G1Affine.curve.a * x +
                    G1Affine.curve.b) at hon2
              change toLawful (mainFinitePostY1 yst) ^ 2 = _ at hon1
              change toLawful (mainFiniteUnequalY2 yst) ^ 2 = _ at hon2
              have hmx1 : (Fp.value (mainX1 yst) : PrimeField.LawfulFp) =
                  toLawful (mainFinitePostX1 yst) := by
                simp [toLawful, mainFinitePostX1_eq_source, sourceField,
                  mainX1, Fp.finEquiv_toField]
              have hmx2 : (Fp.value (mainX2 yst) : PrimeField.LawfulFp) =
                  toLawful (mainFinitePostX2 yst) := by
                simp [toLawful, mainFinitePostX2_eq_source, sourceField,
                  mainX2, Fp.finEquiv_toField]
              rw [hmx1] at hon1
              rw [hmx2, hxEq] at hon2
              exact hon1.trans hon2.symm
            have hprod : (toLawful (mainFinitePostY1 yst) -
                toLawful (mainFiniteUnequalY2 yst)) *
                (toLawful (mainFinitePostY1 yst) +
                  toLawful (mainFiniteUnequalY2 yst)) = 0 := by
              calc
                _ = toLawful (mainFinitePostY1 yst) ^ 2 -
                    toLawful (mainFiniteUnequalY2 yst) ^ 2 := by ring
                _ = 0 := by rw [hsquares, sub_self]
            exact (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hyne)
          have hout := mainFiniteDispatcher_opposite_returned_add yst
            (toLawful (mainFinitePostX1 yst))
            (toLawful (mainFinitePostY1 yst))
            (toLawful (mainFiniteUnequalY2 yst)) hopposite
          rw [ofWire_sourcePoint1_finite yst hfirst,
            ofWire_sourcePoint2_finite yst hsecond, hxEq]
          exact hout
        · rcases fpZeroValue_zero_or_one (mainDecodedWord yst 64)
              (mainDecodedWord yst 96) with hyzero | hyzero
          · have hrun := run_main_double yst hlength hpadding hcanonical
              hcurve1 hcurve2 hfirst hsecond hxeq (by
                show mainFiniteYEqValue yst ≠ 0
                rw [show mainFiniteYEqValue yst = 1 from hyeq]
                decide)
              hyzero hx1 hy1
            refine ⟨_, hrun, ?_⟩
            have hlam := canonical_mainFiniteDoubleLambda yst hx1 hy1
            have hyne := mainFiniteYZero_zero_lawful yst hy1 hyzero
            have hxEq := mainFiniteXEq_one_lawful yst hxeq
            have hslope := mainFiniteDoubleLambda_toLawful yst hx1 hy1
            have hlam' : Fp.Canonical
                (mainFinitePostLambda (mainFiniteDoubleLambdaWords yst)) := by
              rw [mainFinitePostLambda_double_eq]
              exact hlam
            have hslope' : toLawful
                  (mainFinitePostLambda (mainFiniteDoubleLambdaWords yst)) =
                (3 * toLawful (mainFinitePostX1 yst) ^ 2) /
                  (2 * toLawful (mainFinitePostY1 yst)) := by
              rw [mainFinitePostLambda_double_eq]
              simpa [toLawful, mainFinitePostX1_eq_source,
                mainFinitePostY1_eq_source, mainFiniteDoubleX_eq_source,
                mainFiniteDoubleY_eq_source] using hslope
            have hout := mainFiniteDispatcher_double_returned_add yst hx1 hy1
              hx2 hlam' hyne hxEq hslope'
            rw [ofWire_sourcePoint1_finite yst hfirst,
              ofWire_sourcePoint2_finite yst hsecond, hxEq,
              mainFiniteYEq_one_lawful yst hyeq]
            exact hout
          · have hrun := run_main_zeroY yst hlength hpadding hcanonical
              hcurve1 hcurve2 hfirst hsecond hxeq (by
                show mainFiniteYEqValue yst ≠ 0
                rw [show mainFiniteYEqValue yst = 1 from hyeq]
                decide) (by
                show mainFiniteYZeroValue yst ≠ 0
                rw [show mainFiniteYZeroValue yst = 1 from hyzero]
                decide)
            refine ⟨_, hrun, ?_⟩
            have hy0 := mainFiniteYZero_nonzero_lawful yst hy1
              (by
                show mainFiniteYZeroValue yst ≠ 0
                rw [show mainFiniteYZeroValue yst = 1 from hyzero]
                decide)
            have hxEq := mainFiniteXEq_one_lawful yst hxeq
            have hout := mainFiniteDispatcher_zeroY_returned_add yst
              (toLawful (mainFinitePostX1 yst))
            rw [ofWire_sourcePoint1_finite yst hfirst,
              ofWire_sourcePoint2_finite yst hsecond, hxEq,
              mainFiniteYEq_one_lawful yst hyeq, hy0]
            exact hout
    · have hrun := run_main_secondInfinity yst hlength hpadding hcanonical
          hcurve1 hcurve2 hfirst hsecond
      refine ⟨_, hrun, ?_⟩
      have hleft := decodeG1_first_eq_sourcePoint yst input hcalldata hsize
        hpadding hcanonical hcurve1
      rw [ofWire_sourcePoint2_infinity yst hsecond]
      exact mainSecondInfinity_returned_affineIdentity yst input hcalldata
        (sourcePoint1 yst) hleft
  · by_cases hsecond : mainInf2 yst = 0
    · rcases run_main_firstInfinity_contract yst hlength hpadding hcanonical
          hcurve1 hcurve2 hfirst hsecond with ⟨final, contract⟩
      refine ⟨final, contract.run, ?_⟩
      have hright := decodeG1_second_eq_sourcePoint yst input hcalldata hsize
        hpadding hcanonical hcurve2
      rw [ofWire_sourcePoint1_infinity yst hfirst]
      exact contract.returned_affineIdentity input hcalldata
        (sourcePoint2 yst) hright
    · have hboth : mainBothInfinityValue yst ≠ 0 := by
        rw [mainBothInfinityValue, mainInf1_eq_one_of_ne yst hfirst,
          mainInf2_eq_one_of_ne yst hsecond]
        decide
      rcases main_bothInfinity_yulContract yst
          ⟨hlength, hpadding, hcanonical, hcurve1, hcurve2, hboth⟩ with
        ⟨finalEnv, final, outcome, hrun, henv, houtcome, post⟩
      subst finalEnv
      subst outcome
      refine ⟨final, hrun, ?_⟩
      have hleft := decodeG1_first_eq_sourcePoint yst input hcalldata hsize
        hpadding hcanonical hcurve1
      rw [post.bothInfinity_returned_inputWindow input hcalldata,
        Challenge.EvmProof.Bytes.readPadded_eq_extract input 0 128 (by omega)]
      have hencode := Codec.encodeG1_decodeG1 hleft
      rw [Codec.g1Bytes] at hencode
      rw [← hencode, ofWire_sourcePoint1_infinity yst hfirst,
        ofWire_sourcePoint2_infinity yst hsecond]
      rw [sourcePoint1, if_neg hfirst]
      rfl

/-- Complete exact source semantics for every EVM-sized calldata input. -/
theorem run_matches_spec (yst : EvmState) (input : ByteArray)
    (hcalldata : yst.env.calldata = input.toList)
    (hfit : input.size < 2 ^ 256) (hhalted : yst.halted = none) :
    ∃ yst', Run Challenge.Bls12381G1Add.ProofSupport.Yul.localDialect
        Compilation.referenceCompiledBlock yst [] yst' .halt ∧
      match Challenge.Bls12381G1Add.spec input with
      | some output => yst'.halted = some (.ret, output.toList)
      | none => yst'.halted = some (.invalid, []) := by
  by_cases hsize : input.size = 256
  · have hlength : yst.env.calldata.length = 256 := by
      rw [hcalldata, YulEvmCompiler.ByteArray.toList_eq_data,
        Array.length_toList]
      change input.size = 256 at hsize
      exact hsize
    by_cases hpadding : mainPaddingValue yst = 0
    · by_cases hcanonical : mainCanonicalValue yst = 0
      · have hrun := run_main_canonical_reject yst hlength hpadding hcanonical
        have hpads :=
          (mainPaddingValue_eq_zero_iff_codec yst input hcalldata hsize).mp
            hpadding
        have hnot : ¬(Fp.Canonical (sourceField yst 0) ∧
            Fp.Canonical (sourceField yst 64) ∧
            Fp.Canonical (sourceField yst 128) ∧
            Fp.Canonical (sourceField yst 192)) := by
          intro hall
          have hne := (mainCanonicalValue_ne_zero_iff yst).mpr (by
            simpa [sourceField, mainX1, mainY1, mainX2, mainY2,
              onCurveX, onCurveY] using hall)
          exact hne hcanonical
        simp only [not_and_or] at hnot
        have hspec : Challenge.Bls12381G1Add.spec input = none := by
          apply Challenge.Bls12381G1Add.spec_eq_none_iff.mpr
          right
          rcases hnot with h0 | h64 | h128 | h192
          · left
            apply Codec.decodeG1_eq_none_of_first_field
            exact (decodeFp_eq_none_iff_sourceField yst input hcalldata 0
              (by omega) (by omega)).mpr (Or.inr h0)
          · left
            apply Codec.decodeG1_eq_none_of_second_field
            simpa [Codec.fpBytes] using
              (decodeFp_eq_none_iff_sourceField yst input hcalldata 1
                (by omega) (by omega)).mpr (Or.inr h64)
          · right
            apply Codec.decodeG1_eq_none_of_first_field
            exact (decodeFp_eq_none_iff_sourceField yst input hcalldata 2
              (by omega) (by omega)).mpr (Or.inr h128)
          · right
            have hnone :=
              (decodeFp_eq_none_iff_sourceField yst input hcalldata 3
                (by omega) (by omega)).mpr (Or.inr h192)
            have hpoint : Codec.decodeG1 input 128 = none :=
              Codec.decodeG1_eq_none_of_second_field (offset := 128)
                (by simpa [Codec.fpBytes] using hnone)
            simpa [Codec.g1Bytes] using hpoint
        refine ⟨_, hrun, ?_⟩
        rw [hspec]
        rfl
      · by_cases hcurve1 : mainCurve1ConditionValue yst = 0
        · by_cases hcurve2 : mainCurve2ConditionValue yst = 0
          · have hvalid := run_valid_matches_decoded yst input hcalldata hsize
                hpadding hcanonical hcurve1 hcurve2
            obtain ⟨yst', hrun, hhalt⟩ := hvalid
            have hleft := decodeG1_first_eq_sourcePoint yst input hcalldata
              hsize hpadding hcanonical hcurve1
            have hright := decodeG1_second_eq_sourcePoint yst input hcalldata
              hsize hpadding hcanonical hcurve2
            have hspec := Challenge.Bls12381G1Add.spec_success hsize hleft
              (by simpa [Codec.g1Bytes] using hright)
            refine ⟨yst', hrun, ?_⟩
            rw [hspec]
            exact hhalt
          · have hrun := run_main_curve2_reject yst hlength hpadding
                hcanonical hcurve1 hcurve2
            have hright := decodeG1_second_eq_none_of_curve yst input hcalldata
              hsize hpadding hcanonical hcurve2
            have hspec : Challenge.Bls12381G1Add.spec input = none :=
              Challenge.Bls12381G1Add.spec_eq_none_iff.mpr
                (Or.inr (Or.inr (by simpa [Codec.g1Bytes] using hright)))
            refine ⟨_, hrun, ?_⟩
            rw [hspec]
            rfl
        · have hrun := run_main_curve1_reject yst hlength hpadding
              hcanonical hcurve1
          have hleft := decodeG1_first_eq_none_of_curve yst input hcalldata
            hsize hpadding hcanonical hcurve1
          have hspec : Challenge.Bls12381G1Add.spec input = none :=
            Challenge.Bls12381G1Add.spec_eq_none_iff.mpr
              (Or.inr (Or.inl hleft))
          refine ⟨_, hrun, ?_⟩
          rw [hspec]
          rfl
    · have hrun := run_main_padding_reject yst hlength hpadding
      have hnot :=
        (mainPaddingValue_eq_zero_iff_codec yst input hcalldata hsize).not.mp
          hpadding
      simp only [not_and_or] at hnot
      have hspec : Challenge.Bls12381G1Add.spec input = none := by
        apply Challenge.Bls12381G1Add.spec_eq_none_iff.mpr
        right
        rcases hnot with h0 | h64 | h128 | h192
        · left
          apply Codec.decodeG1_eq_none_of_first_field
          exact (decodeFp_eq_none_iff_sourceField yst input hcalldata 0
            (by omega) (by omega)).mpr (Or.inl h0)
        · left
          apply Codec.decodeG1_eq_none_of_second_field
          simpa [Codec.fpBytes] using
            (decodeFp_eq_none_iff_sourceField yst input hcalldata 1
              (by omega) (by omega)).mpr (Or.inl h64)
        · right
          apply Codec.decodeG1_eq_none_of_first_field
          exact (decodeFp_eq_none_iff_sourceField yst input hcalldata 2
            (by omega) (by omega)).mpr (Or.inl h128)
        · right
          have hnone :=
            (decodeFp_eq_none_iff_sourceField yst input hcalldata 3
              (by omega) (by omega)).mpr (Or.inl h192)
          have hpoint : Codec.decodeG1 input 128 = none :=
            Codec.decodeG1_eq_none_of_second_field (offset := 128)
              (by simpa [Codec.fpBytes] using hnone)
          simpa [Codec.g1Bytes] using hpoint
      refine ⟨_, hrun, ?_⟩
      rw [hspec]
      rfl
  · have hlength : yst.env.calldata.length ≠
        Challenge.Bls12381G1Add.inputBytes := by
      simpa [hcalldata, YulEvmCompiler.ByteArray.toList_eq_data,
        Array.length_toList, Challenge.Bls12381G1Add.inputBytes,
        Codec.g1Bytes] using hsize
    have hfit' : yst.env.calldata.length < 2 ^ 256 := by
      simpa [hcalldata, YulEvmCompiler.ByteArray.toList_eq_data,
        Array.length_toList] using hfit
    obtain ⟨yst', hrun, hhalt⟩ := run_invalid_length hfit' hlength hhalted
    have hspec := Challenge.Bls12381G1Add.spec_invalid_length (by
      simpa [Challenge.Bls12381G1Add.inputBytes, Codec.g1Bytes] using hsize)
    refine ⟨yst', hrun, ?_⟩
    rw [hspec]
    exact hhalt

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
