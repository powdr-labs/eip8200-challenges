import Challenge.Bls12381G2Add.Reference.Proofs.SourceSpecRejectValidation

set_option warningAsError true

/-! # Codec rejection induced by the frozen G2ADD curve checks -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics.EVM
open Challenge.Bls12381.ProofSupport

theorem decodeG2_first_eq_none_of_curve (yst : EvmState)
    (input : ByteArray) (hcalldata : yst.env.calldata = input.toList)
    (hsize : input.size = 512) (hvalid : mainValidationValue yst ≠ 0)
    (hcurve : mainCurve1ConditionValue yst ≠ 0) :
    Codec.decodeG2 input 0 = none := by
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
  have hcondition := (mainCurve1ConditionValue_eq_zero_iff yst hx hy).not.mp
    hcurve
  push Not at hcondition
  have hinf : mainInf1 yst = 0 := hcondition.1
  have hnonzero : ¬ Codec.G2WireZero (Fp2.toField (sourceFp2 yst 0))
      (Fp2.toField (sourceFp2 yst 128)) := by
    intro hz
    have hx0 : Fp2.toField (sourceFp2 yst 0) = 0 :=
      wireFp2_eq_zero _ hz.1 hz.2.1
    have hy0 : Fp2.toField (sourceFp2 yst 128) = 0 :=
      wireFp2_eq_zero _ hz.2.2.1 hz.2.2.2
    have hone := (mainInf1_eq_one_iff yst).mpr
      ⟨repr_eq_zero_of_toField_eq_zero hx hx0,
        repr_eq_zero_of_toField_eq_zero hy hy0⟩
    rw [hinf] at hone
    exact (by decide : (0 : U256) ≠ 1) hone
  have hcurveWire : EvmSemantics.Crypto.G2.onCurve
      EvmSemantics.Crypto.Bls12381.g2Curve
      (Fp2.toField (sourceFp2 yst 0))
      (Fp2.toField (sourceFp2 yst 128)) = false := by
    apply Bool.eq_false_iff.mpr
    intro hwire
    apply hcondition.2
    simpa [G2Affine.ofWire, Fp2.toLawful] using
      (G2Affine.onCurve_ofWire hwire)
  exact Codec.decodeG2_eq_none_of_offCurve hdx
    (by simpa [Codec.fp2Bytes] using hdy) hnonzero hcurveWire

theorem decodeG2_second_eq_none_of_curve (yst : EvmState)
    (input : ByteArray) (hcalldata : yst.env.calldata = input.toList)
    (hsize : input.size = 512) (hvalid : mainValidationValue yst ≠ 0)
    (hcurve : mainCurve2ConditionValue yst ≠ 0) :
    Codec.decodeG2 input 256 = none := by
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
  have hcondition := (mainCurve2ConditionValue_eq_zero_iff yst hx hy).not.mp
    hcurve
  push Not at hcondition
  have hinf : mainInf2 yst = 0 := hcondition.1
  have hnonzero : ¬ Codec.G2WireZero (Fp2.toField (sourceFp2 yst 256))
      (Fp2.toField (sourceFp2 yst 384)) := by
    intro hz
    have hx0 : Fp2.toField (sourceFp2 yst 256) = 0 :=
      wireFp2_eq_zero _ hz.1 hz.2.1
    have hy0 : Fp2.toField (sourceFp2 yst 384) = 0 :=
      wireFp2_eq_zero _ hz.2.2.1 hz.2.2.2
    have hone := (mainInf2_eq_one_iff yst).mpr
      ⟨repr_eq_zero_of_toField_eq_zero hx hx0,
        repr_eq_zero_of_toField_eq_zero hy hy0⟩
    rw [hinf] at hone
    exact (by decide : (0 : U256) ≠ 1) hone
  have hcurveWire : EvmSemantics.Crypto.G2.onCurve
      EvmSemantics.Crypto.Bls12381.g2Curve
      (Fp2.toField (sourceFp2 yst 256))
      (Fp2.toField (sourceFp2 yst 384)) = false := by
    apply Bool.eq_false_iff.mpr
    intro hwire
    apply hcondition.2
    simpa [G2Affine.ofWire, Fp2.toLawful] using
      (G2Affine.onCurve_ofWire hwire)
  exact Codec.decodeG2_eq_none_of_offCurve hdx
    (by simpa [Codec.fp2Bytes] using hdy) hnonzero hcurveWire

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
