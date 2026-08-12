import Challenge.Bls12381G2Add.Reference.Proofs.SourceSpecValid

set_option warningAsError true

/-! # Codec rejection induced by the frozen G2ADD validation word -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics.EVM
open Challenge.Bls12381.ProofSupport

private theorem decodeG2_first_none_of_invalid (yst : EvmState)
    (input : ByteArray) (hcalldata : yst.env.calldata = input.toList)
    (hsize : input.size = 512)
    (hinvalid : ¬(Fp2.Canonical (sourceFp2 yst 0) ∧
      Fp2.Canonical (sourceFp2 yst 128) ∧
      PointPaddingZero (mainDecodedState yst) 0)) :
    Codec.decodeG2 input 0 = none := by
  have hpads := pointPaddingZero_iff_codec yst input hcalldata 0
    (by norm_num) (by norm_num) hsize
  simp only [not_and_or] at hinvalid
  rcases hinvalid with hx | hy | hp
  · have hnone := (decodeFp2_eq_none_iff_sourceFp2 yst input hcalldata
      0 (by omega) (by omega)).mpr (Or.inr (Or.inr hx))
    exact Codec.decodeG2_eq_none_of_first_field hnone
  · have hnone := (decodeFp2_eq_none_iff_sourceFp2 yst input hcalldata
      1 (by omega) (by omega)).mpr (Or.inr (Or.inr (by
        simpa using hy)))
    apply Codec.decodeG2_eq_none_of_second_field
    simpa [Codec.fp2Bytes] using hnone
  · have hp' := hpads.not.mp hp
    simp only [not_and_or] at hp'
    rcases hp' with hp0 | hp64 | hp128 | hp192
    · exact Codec.decodeG2_eq_none_of_first_field
        ((decodeFp2_eq_none_iff_sourceFp2 yst input hcalldata
          0 (by omega) (by omega)).mpr (Or.inl hp0))
    · exact Codec.decodeG2_eq_none_of_first_field
        ((decodeFp2_eq_none_iff_sourceFp2 yst input hcalldata
          0 (by omega) (by omega)).mpr (Or.inr (Or.inl hp64)))
    · apply Codec.decodeG2_eq_none_of_second_field
      simpa [Codec.fp2Bytes] using
        ((decodeFp2_eq_none_iff_sourceFp2 yst input hcalldata
          1 (by omega) (by omega)).mpr (Or.inl (by simpa using hp128)))
    · apply Codec.decodeG2_eq_none_of_second_field
      simpa [Codec.fp2Bytes] using
        ((decodeFp2_eq_none_iff_sourceFp2 yst input hcalldata
          1 (by omega) (by omega)).mpr
            (Or.inr (Or.inl (by simpa using hp192))))

private theorem decodeG2_second_none_of_invalid (yst : EvmState)
    (input : ByteArray) (hcalldata : yst.env.calldata = input.toList)
    (hsize : input.size = 512)
    (hinvalid : ¬(Fp2.Canonical (sourceFp2 yst 256) ∧
      Fp2.Canonical (sourceFp2 yst 384) ∧
      PointPaddingZero (mainDecodedState yst) 256)) :
    Codec.decodeG2 input 256 = none := by
  have hpads := pointPaddingZero_iff_codec yst input hcalldata 256
    (by norm_num) (by norm_num) hsize
  simp only [not_and_or] at hinvalid
  rcases hinvalid with hx | hy | hp
  · have hnone := (decodeFp2_eq_none_iff_sourceFp2 yst input hcalldata
      2 (by omega) (by omega)).mpr (Or.inr (Or.inr (by simpa using hx)))
    exact Codec.decodeG2_eq_none_of_first_field hnone
  · have hnone := (decodeFp2_eq_none_iff_sourceFp2 yst input hcalldata
      3 (by omega) (by omega)).mpr (Or.inr (Or.inr (by simpa using hy)))
    apply Codec.decodeG2_eq_none_of_second_field
    simpa [Codec.fp2Bytes] using hnone
  · have hp' := hpads.not.mp hp
    simp only [not_and_or] at hp'
    rcases hp' with hp256 | hp320 | hp384 | hp448
    · exact Codec.decodeG2_eq_none_of_first_field
        ((decodeFp2_eq_none_iff_sourceFp2 yst input hcalldata
          2 (by omega) (by omega)).mpr (Or.inl (by simpa using hp256)))
    · exact Codec.decodeG2_eq_none_of_first_field
        ((decodeFp2_eq_none_iff_sourceFp2 yst input hcalldata
          2 (by omega) (by omega)).mpr
            (Or.inr (Or.inl (by simpa using hp320))))
    · apply Codec.decodeG2_eq_none_of_second_field
      simpa [Codec.fp2Bytes] using
        ((decodeFp2_eq_none_iff_sourceFp2 yst input hcalldata
          3 (by omega) (by omega)).mpr (Or.inl (by simpa using hp384)))
    · apply Codec.decodeG2_eq_none_of_second_field
      simpa [Codec.fp2Bytes] using
        ((decodeFp2_eq_none_iff_sourceFp2 yst input hcalldata
          3 (by omega) (by omega)).mpr
            (Or.inr (Or.inl (by simpa using hp448))))

theorem mainValidation_reject_decode_none (yst : EvmState)
    (input : ByteArray) (hcalldata : yst.env.calldata = input.toList)
    (hsize : input.size = 512) (hvalid : mainValidationValue yst = 0) :
    Codec.decodeG2 input 0 = none ∨ Codec.decodeG2 input 256 = none := by
  have hpair : ¬(mainPoint1Valid yst = 1 ∧ mainPoint2Valid yst = 1) := by
    intro hp
    exact ((mainValidationValue_ne_zero_iff yst).mpr hp) hvalid
  simp only [not_and_or] at hpair
  rcases hpair with hpoint1 | hpoint2
  · left
    have hbad := (pointValidValue_eq_one_iff
      (mainAfterPoint2Valid yst) 0).not.mp hpoint1
    have hx : fp2At (mainAfterPoint2Valid yst) 0 =
        fp2At (mainDecodedState yst) 0 := by
      unfold fp2At
      rw [mainAfterPoint2Valid_memory]
    have hy : fp2At (mainAfterPoint2Valid yst) 128 =
        fp2At (mainDecodedState yst) 128 := by
      unfold fp2At
      rw [mainAfterPoint2Valid_memory]
    have hp : PointPaddingZero (mainAfterPoint2Valid yst) 0 ↔
        PointPaddingZero (mainDecodedState yst) 0 := by
      unfold PointPaddingZero
      rw [mainAfterPoint2Valid_memory]
    rw [show (0 : U256) + BitVec.ofNat 256 128 = 128 by decide,
      hx, hy, hp] at hbad
    exact decodeG2_first_none_of_invalid yst input hcalldata hsize (by
      simpa [sourceFp2] using hbad)
  · right
    have hbad := (pointValidValue_eq_one_iff
      (mainDecodedState yst) 256).not.mp hpoint2
    rw [show (256 : U256) + BitVec.ofNat 256 128 = 384 by decide] at hbad
    exact decodeG2_second_none_of_invalid yst input hcalldata hsize (by
      simpa [sourceFp2] using hbad)

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
