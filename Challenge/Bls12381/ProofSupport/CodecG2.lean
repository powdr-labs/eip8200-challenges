import Challenge.Bls12381.ProofSupport.CodecFp2
import Challenge.Bls12381.ProofSupport.CodecG2Core

set_option warningAsError true

/-! # Exact EIP-2537 G2 point codec boundary -/

namespace Challenge.Bls12381.ProofSupport.Codec

open EvmSemantics.Crypto.Bls12381

def G2WireZero (x y : Fp2) : Prop :=
  x.c0.val = 0 ∧ x.c1.val = 0 ∧ y.c0.val = 0 ∧ y.c1.val = 0

private instance (x y : Fp2) : Decidable (G2WireZero x y) := by
  unfold G2WireZero
  infer_instance

theorem decodeG2_of_components {input : ByteArray} {offset : Nat} (x y : Fp2)
    (hx : decodeFp2 input offset = some x)
    (hy : decodeFp2 input (offset + fp2Bytes) = some y) :
    decodeG2 input offset =
      if G2WireZero x y then
        some (EvmSemantics.Crypto.G2.Point.infinity : G2Point)
      else if EvmSemantics.Crypto.G2.onCurve
          EvmSemantics.Crypto.Bls12381.g2Curve x y then
        some (EvmSemantics.Crypto.G2.Point.affine x y) else none := by
  unfold decodeG2 EvmSemantics.Crypto.Bls12381G2Add.decodePoint
  have hx' : EvmSemantics.Crypto.Bls12381Codec.decodeFp2 input offset = some x :=
    by simpa [decodeFp2] using hx
  have hy' : EvmSemantics.Crypto.Bls12381Codec.decodeFp2 input
      (offset + 128) = some y := by
    simpa [decodeFp2, fp2Bytes] using hy
  simp only [EvmSemantics.Crypto.Bls12381Codec.fp2Bytes]
  rw [hx', hy']
  rfl

theorem decodeG2_eq_some_infinity {input : ByteArray} {offset : Nat}
    (hx : decodeFp2 input offset = some 0)
    (hy : decodeFp2 input (offset + fp2Bytes) = some 0) :
    decodeG2 input offset = some .infinity := by
  rw [decodeG2_of_components 0 0 hx hy]
  rfl

theorem decodeG2_eq_some_affine {input : ByteArray} {offset : Nat} {x y : Fp2}
    (hx : decodeFp2 input offset = some x)
    (hy : decodeFp2 input (offset + fp2Bytes) = some y)
    (hnonzero : ¬ G2WireZero x y)
    (hcurve : EvmSemantics.Crypto.G2.onCurve
      EvmSemantics.Crypto.Bls12381.g2Curve x y = true) :
    decodeG2 input offset = some (.affine x y) := by
  rw [decodeG2_of_components x y hx hy, if_neg hnonzero, if_pos hcurve]

theorem decodeG2_eq_none_of_offCurve
    {input : ByteArray} {offset : Nat} {x y : Fp2}
    (hx : decodeFp2 input offset = some x)
    (hy : decodeFp2 input (offset + fp2Bytes) = some y)
    (hnonzero : ¬ G2WireZero x y)
    (hcurve : EvmSemantics.Crypto.G2.onCurve
      EvmSemantics.Crypto.Bls12381.g2Curve x y = false) :
    decodeG2 input offset = none := by
  rw [decodeG2_of_components x y hx hy, if_neg hnonzero]
  simp [hcurve]

/-- Any non-all-zero coordinate tuple, including a partial-zero tuple, can
never be interpreted as the infinity encoding. -/
theorem decodeG2_nonzero_ne_infinity
    {input : ByteArray} {offset : Nat} {x y : Fp2}
    (hx : decodeFp2 input offset = some x)
    (hy : decodeFp2 input (offset + fp2Bytes) = some y)
    (hnonzero : ¬ G2WireZero x y) :
    decodeG2 input offset ≠ some .infinity := by
  rw [decodeG2_of_components x y hx hy, if_neg hnonzero]
  by_cases hcurve : EvmSemantics.Crypto.G2.onCurve
      EvmSemantics.Crypto.Bls12381.g2Curve x y = true
  · rw [if_pos hcurve]
    simp
  · rw [if_neg hcurve]
    simp

theorem decodeG2_eq_none_of_first_field {input : ByteArray} {offset : Nat}
    (hx : decodeFp2 input offset = none) : decodeG2 input offset = none := by
  unfold decodeG2 EvmSemantics.Crypto.Bls12381G2Add.decodePoint
  have hx' : EvmSemantics.Crypto.Bls12381Codec.decodeFp2 input offset = none :=
    by simpa [decodeFp2] using hx
  rw [hx']
  rfl

theorem decodeG2_eq_none_of_second_field {input : ByteArray} {offset : Nat}
    (hy : decodeFp2 input (offset + fp2Bytes) = none) :
    decodeG2 input offset = none := by
  unfold decodeG2 EvmSemantics.Crypto.Bls12381G2Add.decodePoint
  have hy' : EvmSemantics.Crypto.Bls12381Codec.decodeFp2 input
      (offset + 128) = none := by
    simpa [decodeFp2, fp2Bytes] using hy
  simp only [EvmSemantics.Crypto.Bls12381Codec.fp2Bytes]
  rw [hy']
  cases EvmSemantics.Crypto.Bls12381Codec.decodeFp2 input offset <;> rfl

theorem decodeG2_success_cases {input : ByteArray} {offset : Nat}
    {point : G2Point} (hdecode : decodeG2 input offset = some point) :
    ∃ x y, decodeFp2 input offset = some x ∧
      decodeFp2 input (offset + fp2Bytes) = some y ∧
      ((G2WireZero x y ∧ point = .infinity) ∨
       (¬ G2WireZero x y ∧
        EvmSemantics.Crypto.G2.onCurve
          EvmSemantics.Crypto.Bls12381.g2Curve x y = true ∧
        point = .affine x y)) := by
  cases hx : EvmSemantics.Crypto.Bls12381Codec.decodeFp2 input offset with
  | none =>
      have hx' : decodeFp2 input offset = none := by simpa [decodeFp2] using hx
      rw [decodeG2_eq_none_of_first_field hx'] at hdecode
      simp at hdecode
  | some x =>
      cases hy : EvmSemantics.Crypto.Bls12381Codec.decodeFp2 input
          (offset + 128) with
      | none =>
          have hy' : decodeFp2 input (offset + fp2Bytes) = none := by
            simpa [decodeFp2, fp2Bytes] using hy
          rw [decodeG2_eq_none_of_second_field hy'] at hdecode
          simp at hdecode
      | some y =>
          have hx' : decodeFp2 input offset = some x := by
            simpa [decodeFp2] using hx
          have hy' : decodeFp2 input (offset + fp2Bytes) = some y := by
            simpa [decodeFp2, fp2Bytes] using hy
          rw [decodeG2_of_components x y hx' hy'] at hdecode
          refine ⟨x, y, hx', hy', ?_⟩
          by_cases hzero : G2WireZero x y
          · left
            rw [if_pos hzero] at hdecode
            exact ⟨hzero, (Option.some.inj hdecode).symm⟩
          · right
            rw [if_neg hzero] at hdecode
            have hcurve : EvmSemantics.Crypto.G2.onCurve
                EvmSemantics.Crypto.Bls12381.g2Curve x y = true := by
              by_contra hnot
              rw [if_neg hnot] at hdecode
              simp at hdecode
            rw [if_pos hcurve] at hdecode
            exact ⟨hzero, hcurve, (Option.some.inj hdecode).symm⟩

theorem decodeG2_framed (pre suffix : ByteArray) (point : G2Point)
    (hpoint : ValidG2 point) :
    decodeG2 (pre ++ encodeG2 point ++ suffix) pre.size = some point := by
  cases point with
  | infinity =>
      unfold encodeG2 EvmSemantics.Crypto.Bls12381G2Add.encodePoint
      apply decodeG2_eq_some_infinity
      · simpa [ByteArray.append_assoc] using
          decodeFp2_framed pre (encodeFp2 0 ++ suffix) 0
      · have h := decodeFp2_framed (pre ++ encodeFp2 0) suffix 0
        rw [ByteArray.size_append, encodeFp2_size] at h
        simpa [fp2Bytes, ByteArray.append_assoc] using h
  | affine x y =>
      change EvmSemantics.Crypto.G2.onCurve
        EvmSemantics.Crypto.Bls12381.g2Curve x y = true at hpoint
      unfold encodeG2 EvmSemantics.Crypto.Bls12381G2Add.encodePoint
      have hx : decodeFp2 (pre ++ (encodeFp2 x ++ encodeFp2 y) ++ suffix)
          pre.size = some x := by
        simpa [ByteArray.append_assoc] using
          decodeFp2_framed pre (encodeFp2 y ++ suffix) x
      have hy : decodeFp2 (pre ++ (encodeFp2 x ++ encodeFp2 y) ++ suffix)
          (pre.size + fp2Bytes) = some y := by
        have h := decodeFp2_framed (pre ++ encodeFp2 x) suffix y
        rw [ByteArray.size_append, encodeFp2_size] at h
        simpa [fp2Bytes, ByteArray.append_assoc] using h
      have hnonzero : ¬ G2WireZero x y := by
        intro hzero
        rcases hzero with ⟨hx0, hx1, hy0, hy1⟩
        have hxc0 : x.c0 = 0 := Fin.ext hx0
        have hxc1 : x.c1 = 0 := Fin.ext hx1
        have hyc0 : y.c0 = 0 := Fin.ext hy0
        have hyc1 : y.c1 = 0 := Fin.ext hy1
        cases x
        cases y
        simp only at hxc0 hxc1 hyc0 hyc1
        subst_vars
        have hzeroCurve : EvmSemantics.Crypto.G2.onCurve
            EvmSemantics.Crypto.Bls12381.g2Curve
            ({ c0 := 0, c1 := 0 } : Fp2)
            ({ c0 := 0, c1 := 0 } : Fp2) = false := by decide
        rw [hzeroCurve] at hpoint
        exact Bool.noConfusion hpoint
      exact decodeG2_eq_some_affine hx hy hnonzero hpoint

theorem encodeG2_decodeG2 {input : ByteArray} {offset : Nat} {point : G2Point}
    (hdecode : decodeG2 input offset = some point) :
    encodeG2 point = input.extract offset (offset + g2Bytes) := by
  obtain ⟨x, y, hx, hy, hcase⟩ := decodeG2_success_cases hdecode
  have hex := encodeFp2_decodeFp2 hx
  have hey := encodeFp2_decodeFp2 hy
  rcases hcase with hzero | haffine
  · rcases hzero with ⟨hzero, rfl⟩
    rcases hzero with ⟨hx0, hx1, hy0, hy1⟩
    have hx' : x = 0 := by cases x; simp_all; rfl
    have hy' : y = 0 := by cases y; simp_all; rfl
    subst x
    subst y
    unfold encodeG2 EvmSemantics.Crypto.Bls12381G2Add.encodePoint
    change encodeFp2 0 ++ encodeFp2 0 = _
    calc
      encodeFp2 0 ++ encodeFp2 0 =
          input.extract offset (offset + fp2Bytes) ++ encodeFp2 0 := by rw [hex]
      _ = input.extract offset (offset + fp2Bytes) ++
          input.extract (offset + fp2Bytes) (offset + fp2Bytes + fp2Bytes) := by
            rw [hey]
      _ = input.extract offset (offset + g2Bytes) :=
        (ByteArray.extract_eq_extract_append_extract (offset + fp2Bytes)
          (by omega) (by simp [fp2Bytes])).symm
  · rcases haffine with ⟨_, _, rfl⟩
    unfold encodeG2 EvmSemantics.Crypto.Bls12381G2Add.encodePoint
    change encodeFp2 x ++ encodeFp2 y = _
    rw [hex, hey]
    exact (ByteArray.extract_eq_extract_append_extract (offset + fp2Bytes)
      (by omega) (by simp [fp2Bytes])).symm

theorem decodeG2_encodeG2 (point : G2Point) (hpoint : ValidG2 point) :
    decodeG2 (encodeG2 point) 0 = some point := by
  simpa using decodeG2_framed ByteArray.empty ByteArray.empty point hpoint

theorem decodeG2_eq_none_of_short {input : ByteArray} {offset : Nat}
    (hshort : input.size < offset + g2Bytes) : decodeG2 input offset = none := by
  have hsecond : input.size < (offset + fp2Bytes) + fp2Bytes := by
    simpa [g2Bytes, fp2Bytes, Nat.add_assoc] using hshort
  have hnone : decodeFp2 input (offset + fp2Bytes) = none :=
    decodeFp2_eq_none_of_short hsecond
  exact decodeG2_eq_none_of_second_field hnone

end Challenge.Bls12381.ProofSupport.Codec
