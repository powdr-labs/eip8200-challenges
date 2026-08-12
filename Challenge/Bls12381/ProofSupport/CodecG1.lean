import Challenge.Bls12381.ProofSupport.CodecFp
import Challenge.Bls12381.ProofSupport.CodecG1Core

set_option warningAsError true

/-! # Exact EIP-2537 G1 point codec boundary -/

namespace Challenge.Bls12381.ProofSupport.Codec

open EvmSemantics.Crypto.Bls12381

theorem decodeG1_of_components {input : ByteArray} {offset : Nat} (x y : Fp)
    (hx : decodeFp input offset = some x)
    (hy : decodeFp input (offset + fpBytes) = some y) :
    decodeG1 input offset =
      if x.val = 0 ∧ y.val = 0 then some .infinity
      else if EvmSemantics.Crypto.Bls12381.onCurve x y then
        some (.affine x y) else none := by
  unfold decodeG1 EvmSemantics.Crypto.Bls12381G1Add.decodePoint
  have hx' : EvmSemantics.Crypto.Bls12381Codec.decodeFp input offset = some x :=
    by simpa [decodeFp] using hx
  have hy' : EvmSemantics.Crypto.Bls12381Codec.decodeFp input
      (offset + 64) = some y := by
    simpa [decodeFp, fpBytes] using hy
  simp only [EvmSemantics.Crypto.Bls12381Codec.fpBytes]
  rw [hx', hy']
  rfl

theorem decodeG1_eq_some_infinity {input : ByteArray} {offset : Nat}
    (hx : decodeFp input offset = some 0)
    (hy : decodeFp input (offset + fpBytes) = some 0) :
    decodeG1 input offset = some .infinity := by
  rw [decodeG1_of_components 0 0 hx hy]
  rfl

theorem decodeG1_eq_some_affine {input : ByteArray} {offset : Nat} {x y : Fp}
    (hx : decodeFp input offset = some x)
    (hy : decodeFp input (offset + fpBytes) = some y)
    (hnonzero : ¬(x.val = 0 ∧ y.val = 0))
    (hcurve : EvmSemantics.Crypto.Bls12381.onCurve x y = true) :
    decodeG1 input offset = some (.affine x y) := by
  rw [decodeG1_of_components x y hx hy, if_neg hnonzero, if_pos hcurve]

theorem decodeG1_eq_none_of_offCurve
    {input : ByteArray} {offset : Nat} {x y : Fp}
    (hx : decodeFp input offset = some x)
    (hy : decodeFp input (offset + fpBytes) = some y)
    (hnonzero : ¬(x.val = 0 ∧ y.val = 0))
    (hcurve : EvmSemantics.Crypto.Bls12381.onCurve x y = false) :
    decodeG1 input offset = none := by
  rw [decodeG1_of_components x y hx hy, if_neg hnonzero]
  simp [hcurve]

/-- Any non-all-zero coordinate pair, including a partial-zero pair, can
never be interpreted as the infinity encoding. -/
theorem decodeG1_nonzero_ne_infinity
    {input : ByteArray} {offset : Nat} {x y : Fp}
    (hx : decodeFp input offset = some x)
    (hy : decodeFp input (offset + fpBytes) = some y)
    (hnonzero : ¬(x.val = 0 ∧ y.val = 0)) :
    decodeG1 input offset ≠ some .infinity := by
  rw [decodeG1_of_components x y hx hy, if_neg hnonzero]
  by_cases hcurve : EvmSemantics.Crypto.Bls12381.onCurve x y = true
  · rw [if_pos hcurve]
    simp
  · rw [if_neg hcurve]
    simp

theorem decodeG1_eq_none_of_first_field {input : ByteArray} {offset : Nat}
    (hx : decodeFp input offset = none) : decodeG1 input offset = none := by
  unfold decodeG1 EvmSemantics.Crypto.Bls12381G1Add.decodePoint
  have hx' : EvmSemantics.Crypto.Bls12381Codec.decodeFp input offset = none :=
    by simpa [decodeFp] using hx
  rw [hx']
  rfl

theorem decodeG1_eq_none_of_second_field {input : ByteArray} {offset : Nat}
    (hy : decodeFp input (offset + fpBytes) = none) :
    decodeG1 input offset = none := by
  unfold decodeG1 EvmSemantics.Crypto.Bls12381G1Add.decodePoint
  have hy' : EvmSemantics.Crypto.Bls12381Codec.decodeFp input
      (offset + 64) = none := by
    simpa [decodeFp, fpBytes] using hy
  simp only [EvmSemantics.Crypto.Bls12381Codec.fpBytes]
  rw [hy']
  cases EvmSemantics.Crypto.Bls12381Codec.decodeFp input offset <;> rfl

theorem decodeG1_success_cases {input : ByteArray} {offset : Nat} {point : Point}
    (hdecode : decodeG1 input offset = some point) :
    ∃ x y, decodeFp input offset = some x ∧
      decodeFp input (offset + fpBytes) = some y ∧
      ((x.val = 0 ∧ y.val = 0 ∧ point = .infinity) ∨
       (¬(x.val = 0 ∧ y.val = 0) ∧
        EvmSemantics.Crypto.Bls12381.onCurve x y = true ∧
        point = .affine x y)) := by
  cases hx : EvmSemantics.Crypto.Bls12381Codec.decodeFp input offset with
  | none =>
      have hx' : decodeFp input offset = none := by simpa [decodeFp] using hx
      rw [decodeG1_eq_none_of_first_field hx'] at hdecode
      simp at hdecode
  | some x =>
      cases hy : EvmSemantics.Crypto.Bls12381Codec.decodeFp input
          (offset + 64) with
      | none =>
          have hy' : decodeFp input (offset + fpBytes) = none := by
            simpa [decodeFp, fpBytes] using hy
          rw [decodeG1_eq_none_of_second_field hy'] at hdecode
          simp at hdecode
      | some y =>
          have hx' : decodeFp input offset = some x := by
            simpa [decodeFp] using hx
          have hy' : decodeFp input (offset + fpBytes) = some y := by
            simpa [decodeFp, fpBytes] using hy
          rw [decodeG1_of_components x y hx' hy'] at hdecode
          refine ⟨x, y, ?_, ?_, ?_⟩
          · exact hx'
          · exact hy'
          · by_cases hzero : x.val = 0 ∧ y.val = 0
            · left
              rw [if_pos hzero] at hdecode
              exact ⟨hzero.1, hzero.2, (Option.some.inj hdecode).symm⟩
            · right
              rw [if_neg hzero] at hdecode
              have hcurve : EvmSemantics.Crypto.Bls12381.onCurve x y = true := by
                by_contra hnot
                rw [if_neg hnot] at hdecode
                simp at hdecode
              rw [if_pos hcurve] at hdecode
              exact ⟨hzero, hcurve, (Option.some.inj hdecode).symm⟩

theorem decodeG1_framed (pre suffix : ByteArray) (point : Point)
    (hpoint : ValidG1 point) :
    decodeG1 (pre ++ encodeG1 point ++ suffix) pre.size = some point := by
  cases point with
  | infinity =>
      unfold encodeG1 EvmSemantics.Crypto.Bls12381G1Add.encodePoint
      apply decodeG1_eq_some_infinity
      · simpa [ByteArray.append_assoc] using
          decodeFp_framed pre (encodeFp 0 ++ suffix) 0
      · have h := decodeFp_framed (pre ++ encodeFp 0) suffix 0
        rw [ByteArray.size_append, encodeFp_size] at h
        simpa [fpBytes, ByteArray.append_assoc] using h
  | affine x y =>
      change EvmSemantics.Crypto.Bls12381.onCurve x y = true at hpoint
      unfold encodeG1 EvmSemantics.Crypto.Bls12381G1Add.encodePoint
      have hx : decodeFp (pre ++ (encodeFp x ++ encodeFp y) ++ suffix)
          pre.size = some x := by
        simpa [ByteArray.append_assoc] using
          decodeFp_framed pre (encodeFp y ++ suffix) x
      have hy : decodeFp (pre ++ (encodeFp x ++ encodeFp y) ++ suffix)
          (pre.size + fpBytes) = some y := by
        have h := decodeFp_framed (pre ++ encodeFp x) suffix y
        rw [ByteArray.size_append, encodeFp_size] at h
        simpa [fpBytes, ByteArray.append_assoc] using h
      have hnonzero : ¬(x.val = 0 ∧ y.val = 0) := by
        rintro ⟨hx0, hy0⟩
        have hx' : x = 0 := Fin.ext hx0
        have hy' : y = 0 := Fin.ext hy0
        subst x
        subst y
        have hzeroCurve : EvmSemantics.Crypto.Bls12381.onCurve 0 0 = false :=
          by decide
        rw [hzeroCurve] at hpoint
        exact Bool.noConfusion hpoint
      exact decodeG1_eq_some_affine hx hy hnonzero hpoint

theorem encodeG1_decodeG1 {input : ByteArray} {offset : Nat} {point : Point}
    (hdecode : decodeG1 input offset = some point) :
    encodeG1 point = input.extract offset (offset + g1Bytes) := by
  obtain ⟨x, y, hx, hy, hcase⟩ := decodeG1_success_cases hdecode
  have hex := encodeFp_decodeFp hx
  have hey := encodeFp_decodeFp hy
  rcases hcase with hzero | haffine
  · rcases hzero with ⟨hx0, hy0, rfl⟩
    have hx' : x = 0 := Fin.ext hx0
    have hy' : y = 0 := Fin.ext hy0
    subst x
    subst y
    unfold encodeG1 EvmSemantics.Crypto.Bls12381G1Add.encodePoint
    change encodeFp 0 ++ encodeFp 0 = _
    calc
      encodeFp 0 ++ encodeFp 0 =
          input.extract offset (offset + fpBytes) ++ encodeFp 0 := by rw [hex]
      _ = input.extract offset (offset + fpBytes) ++
          input.extract (offset + fpBytes) (offset + fpBytes + fpBytes) := by
            rw [hey]
      _ = input.extract offset (offset + g1Bytes) :=
        (ByteArray.extract_eq_extract_append_extract (offset + fpBytes)
          (by omega) (by simp [fpBytes])).symm
  · rcases haffine with ⟨_, _, rfl⟩
    unfold encodeG1 EvmSemantics.Crypto.Bls12381G1Add.encodePoint
    change encodeFp x ++ encodeFp y = _
    rw [hex, hey]
    exact (ByteArray.extract_eq_extract_append_extract (offset + fpBytes)
      (by omega) (by simp [fpBytes])).symm

theorem decodeG1_encodeG1 (point : Point) (hpoint : ValidG1 point) :
    decodeG1 (encodeG1 point) 0 = some point := by
  simpa using decodeG1_framed ByteArray.empty ByteArray.empty point hpoint

theorem decodeG1_eq_none_of_short {input : ByteArray} {offset : Nat}
    (hshort : input.size < offset + g1Bytes) : decodeG1 input offset = none := by
  have hsecond : input.size < (offset + fpBytes) + fpBytes := by
    simpa [g1Bytes, fpBytes, Nat.add_assoc] using hshort
  have hnone : decodeFp input (offset + fpBytes) = none :=
    decodeFp_eq_none_of_short hsecond
  exact decodeG1_eq_none_of_second_field hnone

end Challenge.Bls12381.ProofSupport.Codec
