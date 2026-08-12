import Challenge.Bls12381G2Add.Reference.Proofs.SourceMainPointLawful
import Challenge.Bls12381G2Add.Spec

set_option warningAsError true

/-! # G2ADD validated source points agree with the EIP codec -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics.EVM
open Challenge.Bls12381.ProofSupport

private abbrev WirePoint := EvmSemantics.Crypto.Bls12381.G2Point

def sourcePoint1 (yst : EvmState) : WirePoint :=
  if mainInf1 yst = 0 then
    .affine (Fp2.toField (sourceFp2 yst 0))
      (Fp2.toField (sourceFp2 yst 128))
  else .infinity

def sourcePoint2 (yst : EvmState) : WirePoint :=
  if mainInf2 yst = 0 then
    .affine (Fp2.toField (sourceFp2 yst 256))
      (Fp2.toField (sourceFp2 yst 384))
  else .infinity

theorem toField_eq_zero_of_repr_eq_zero {a : Fp2.Repr}
    (h : a = Challenge.Bls12381.ProofSupport.Fp2.zero) : Fp2.toField a = 0 := by
  rw [h, Fp2.toField_zero]

theorem wireFp2_eq_zero
    (a : EvmSemantics.Crypto.Bls12381.Fp2)
    (h0 : a.c0.val = 0) (h1 : a.c1.val = 0) : a = 0 := by
  have hc0 : a.c0 = 0 := Fin.ext h0
  have hc1 : a.c1 = 0 := Fin.ext h1
  cases a
  simp only at hc0 hc1
  subst_vars
  rfl

theorem repr_eq_zero_of_toField_eq_zero {a : Fp2.Repr}
    (ha : Fp2.Canonical a) (hzero : Fp2.toField a = 0) :
    a = Challenge.Bls12381.ProofSupport.Fp2.zero := by
  apply Fp2.eq_zero_of_isZeroSource_true
  apply (Fp2.isZeroSource_iff ha).mpr
  unfold Fp2.toLawful
  rw [hzero]
  change LawfulFp2.ofWire
    ({ c0 := 0, c1 := 0 } : EvmSemantics.Crypto.Bls12381.Fp2) = 0
  apply QuadraticAlgebra.ext <;> simp [LawfulFp2.ofWire]

theorem decodeG2_first_eq_sourcePoint (yst : EvmState) (input : ByteArray)
    (hcalldata : yst.env.calldata = input.toList) (hsize : input.size = 512)
    (hvalid : mainValidationValue yst ≠ 0)
    (hcurve : mainCurve1ConditionValue yst = 0) :
    Codec.decodeG2 input 0 = some (sourcePoint1 yst) := by
  obtain ⟨⟨hx, hy, hpad⟩, _⟩ := mainValidation_canonical yst hvalid
  have hpads := (pointPaddingZero_iff_codec yst input hcalldata 0
    (by norm_num) (by norm_num) hsize).mp hpad
  have hdx : Codec.decodeFp2 input 0 =
      some (Fp2.toField (sourceFp2 yst 0)) :=
    (decodeFp2_eq_some_sourceFp2 yst input hcalldata 0 (by omega)
      (by omega)).mpr ⟨hpads.1, hpads.2.1, hx⟩
  have hdy : Codec.decodeFp2 input 128 =
      some (Fp2.toField (sourceFp2 yst 128)) :=
    (decodeFp2_eq_some_sourceFp2 yst input hcalldata 1 (by omega)
      (by omega)).mpr ⟨hpads.2.2.1, hpads.2.2.2, hy⟩
  rw [Codec.decodeG2_of_components _ _ hdx (by simpa [Codec.fp2Bytes] using hdy)]
  rcases mainInf1_zero_or_one yst with hinf | hinf
  · have hlawful := mainCurve1_success_finite yst hx hy hinf hcurve
    have hwire := G2Affine.onCurve_toWire hlawful
    have hnz : ¬ Codec.G2WireZero (Fp2.toField (sourceFp2 yst 0))
        (Fp2.toField (sourceFp2 yst 128)) := by
      intro hz
      have hx0 : Fp2.toField (sourceFp2 yst 0) = 0 := by
        exact wireFp2_eq_zero _ hz.1 hz.2.1
      have hy0 : Fp2.toField (sourceFp2 yst 128) = 0 := by
        exact wireFp2_eq_zero _ hz.2.2.1 hz.2.2.2
      have hrx : sourceFp2 yst 0 = Challenge.Bls12381.ProofSupport.Fp2.zero :=
        repr_eq_zero_of_toField_eq_zero hx hx0
      have hry : sourceFp2 yst 128 = Challenge.Bls12381.ProofSupport.Fp2.zero :=
        repr_eq_zero_of_toField_eq_zero hy hy0
      have hone := (mainInf1_eq_one_iff yst).mpr ⟨hrx, hry⟩
      rw [hinf] at hone
      contradiction
    have hwire' : EvmSemantics.Crypto.G2.onCurve
        EvmSemantics.Crypto.Bls12381.g2Curve
        (Fp2.toField (sourceFp2 yst 0))
        (Fp2.toField (sourceFp2 yst 128)) = true := by
      simpa [Fp2.toLawful] using hwire
    rw [if_neg hnz, if_pos hwire']
    simp [sourcePoint1, hinf]
  · obtain ⟨hx0, hy0⟩ := (mainInf1_eq_one_iff yst).mp hinf
    have hz : Codec.G2WireZero (Fp2.toField (sourceFp2 yst 0))
        (Fp2.toField (sourceFp2 yst 128)) := by
      rw [toField_eq_zero_of_repr_eq_zero hx0,
        toField_eq_zero_of_repr_eq_zero hy0]
      change Codec.G2WireZero
        ({ c0 := 0, c1 := 0 } : EvmSemantics.Crypto.Bls12381.Fp2)
        ({ c0 := 0, c1 := 0 } : EvmSemantics.Crypto.Bls12381.Fp2)
      exact ⟨rfl, rfl, rfl, rfl⟩
    rw [if_pos hz]
    simp [sourcePoint1, hinf]

theorem decodeG2_second_eq_sourcePoint (yst : EvmState) (input : ByteArray)
    (hcalldata : yst.env.calldata = input.toList) (hsize : input.size = 512)
    (hvalid : mainValidationValue yst ≠ 0)
    (hcurve : mainCurve2ConditionValue yst = 0) :
    Codec.decodeG2 input 256 = some (sourcePoint2 yst) := by
  obtain ⟨_, hx, hy, hpad⟩ := mainValidation_canonical yst hvalid
  have hpads := (pointPaddingZero_iff_codec yst input hcalldata 256
    (by norm_num) (by norm_num) hsize).mp hpad
  have hdx : Codec.decodeFp2 input 256 =
      some (Fp2.toField (sourceFp2 yst 256)) :=
    (decodeFp2_eq_some_sourceFp2 yst input hcalldata 2 (by omega)
      (by omega)).mpr ⟨hpads.1, hpads.2.1, hx⟩
  have hdy : Codec.decodeFp2 input 384 =
      some (Fp2.toField (sourceFp2 yst 384)) :=
    (decodeFp2_eq_some_sourceFp2 yst input hcalldata 3 (by omega)
      (by omega)).mpr ⟨hpads.2.2.1, hpads.2.2.2, hy⟩
  rw [Codec.decodeG2_of_components _ _ hdx (by simpa [Codec.fp2Bytes] using hdy)]
  rcases mainInf2_zero_or_one yst with hinf | hinf
  · have hlawful := mainCurve2_success_finite yst hx hy hinf hcurve
    have hwire := G2Affine.onCurve_toWire hlawful
    have hnz : ¬ Codec.G2WireZero (Fp2.toField (sourceFp2 yst 256))
        (Fp2.toField (sourceFp2 yst 384)) := by
      intro hz
      have hx0 : Fp2.toField (sourceFp2 yst 256) = 0 := by
        exact wireFp2_eq_zero _ hz.1 hz.2.1
      have hy0 : Fp2.toField (sourceFp2 yst 384) = 0 := by
        exact wireFp2_eq_zero _ hz.2.2.1 hz.2.2.2
      have hrx : sourceFp2 yst 256 = Challenge.Bls12381.ProofSupport.Fp2.zero :=
        repr_eq_zero_of_toField_eq_zero hx hx0
      have hry : sourceFp2 yst 384 = Challenge.Bls12381.ProofSupport.Fp2.zero :=
        repr_eq_zero_of_toField_eq_zero hy hy0
      have hone := (mainInf2_eq_one_iff yst).mpr ⟨hrx, hry⟩
      rw [hinf] at hone
      contradiction
    have hwire' : EvmSemantics.Crypto.G2.onCurve
        EvmSemantics.Crypto.Bls12381.g2Curve
        (Fp2.toField (sourceFp2 yst 256))
        (Fp2.toField (sourceFp2 yst 384)) = true := by
      simpa [Fp2.toLawful] using hwire
    rw [if_neg hnz, if_pos hwire']
    simp [sourcePoint2, hinf]
  · obtain ⟨hx0, hy0⟩ := (mainInf2_eq_one_iff yst).mp hinf
    have hz : Codec.G2WireZero (Fp2.toField (sourceFp2 yst 256))
        (Fp2.toField (sourceFp2 yst 384)) := by
      rw [toField_eq_zero_of_repr_eq_zero hx0,
        toField_eq_zero_of_repr_eq_zero hy0]
      change Codec.G2WireZero
        ({ c0 := 0, c1 := 0 } : EvmSemantics.Crypto.Bls12381.Fp2)
        ({ c0 := 0, c1 := 0 } : EvmSemantics.Crypto.Bls12381.Fp2)
      exact ⟨rfl, rfl, rfl, rfl⟩
    rw [if_pos hz]
    simp [sourcePoint2, hinf]

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
