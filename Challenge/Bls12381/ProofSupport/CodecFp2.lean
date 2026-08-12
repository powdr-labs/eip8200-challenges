import Challenge.Bls12381.ProofSupport.CodecFp

set_option warningAsError true

/-! # Exact EIP-2537 quadratic-field codec boundary -/

namespace Challenge.Bls12381.ProofSupport.Codec

open EvmSemantics.Crypto.Bls12381

theorem decodeFp2_eq_some_iff_components
    (input : ByteArray) (offset : Nat) (a : Fp2) :
    decodeFp2 input offset = some a ↔
      decodeFp input offset = some a.c0 ∧
      decodeFp input (offset + fpBytes) = some a.c1 := by
  unfold decodeFp2 EvmSemantics.Crypto.Bls12381Codec.decodeFp2
  simp only [EvmSemantics.Crypto.Bls12381Codec.fpBytes]
  constructor
  · intro h
    cases h0 : EvmSemantics.Crypto.Bls12381Codec.decodeFp input offset with
    | none => simp [h0] at h
    | some b =>
        cases h1 : EvmSemantics.Crypto.Bls12381Codec.decodeFp input (offset + 64) with
        | none => simp [h0, h1] at h
        | some c =>
            simp only [h0, h1] at h
            have heq : ({ c0 := b, c1 := c } : Fp2) = a :=
              Option.some.inj h
            have hb : b = a.c0 := by simpa using congrArg Fp2.c0 heq
            have hc : c = a.c1 := by simpa using congrArg Fp2.c1 heq
            exact ⟨by simpa [decodeFp, h0] using congrArg some hb,
              by simpa [decodeFp, fpBytes, h1] using congrArg some hc⟩
  · rintro ⟨h0, h1⟩
    have h0' : EvmSemantics.Crypto.Bls12381Codec.decodeFp input offset =
        some a.c0 := by simpa [decodeFp] using h0
    have h1' : EvmSemantics.Crypto.Bls12381Codec.decodeFp input (offset + 64) =
        some a.c1 := by simpa [decodeFp, fpBytes] using h1
    rw [h0', h1']

theorem decodeFp2_eq_some_iff (input : ByteArray) (offset : Nat) (a : Fp2) :
    decodeFp2 input offset = some a ↔
      offset + fp2Bytes ≤ input.size ∧
      PaddingZero input offset ∧
      fpWindowValue input offset = a.c0.val ∧
      PaddingZero input (offset + fpBytes) ∧
      fpWindowValue input (offset + fpBytes) = a.c1.val := by
  rw [decodeFp2_eq_some_iff_components,
    decodeFp_eq_some_iff input offset a.c0,
    decodeFp_eq_some_iff input (offset + fpBytes) a.c1]
  constructor
  · rintro ⟨⟨hsize0, hpad0, hvalue0⟩, hsize1, hpad1, hvalue1⟩
    refine ⟨?_, hpad0, hvalue0, hpad1, hvalue1⟩
    simpa [fp2Bytes, fpBytes, Nat.add_assoc] using hsize1
  · rintro ⟨hsize, hpad0, hvalue0, hpad1, hvalue1⟩
    have hsize0 : offset + fpBytes ≤ input.size := by
      change offset + 128 ≤ input.size at hsize
      change offset + 64 ≤ input.size
      omega
    have hsize1 : offset + fpBytes + fpBytes ≤ input.size := by
      simpa [fp2Bytes, fpBytes, Nat.add_assoc] using hsize
    exact ⟨⟨hsize0, hpad0, hvalue0⟩, hsize1, hpad1, hvalue1⟩

theorem decodeFp2_eq_none_of_first_padding_nonzero
    {input : ByteArray} {offset i : Nat}
    (hsize : offset + fp2Bytes ≤ input.size) (hi : i < 16)
    (hnonzero : input[offset + i]! ≠ 0) : decodeFp2 input offset = none := by
  have hsize0 : offset + fpBytes ≤ input.size := by
    change offset + 128 ≤ input.size at hsize
    change offset + 64 ≤ input.size
    omega
  have hnone := decodeFp_eq_none_of_padding_nonzero hsize0 hi hnonzero
  unfold decodeFp2 EvmSemantics.Crypto.Bls12381Codec.decodeFp2
  have hnone' : EvmSemantics.Crypto.Bls12381Codec.decodeFp input offset = none :=
    by simpa [decodeFp] using hnone
  rw [hnone']

theorem decodeFp2_eq_none_of_second_padding_nonzero
    {input : ByteArray} {offset i : Nat}
    (hsize : offset + fp2Bytes ≤ input.size) (hi : i < 16)
    (hnonzero : input[offset + fpBytes + i]! ≠ 0) :
    decodeFp2 input offset = none := by
  have hsize1 : offset + fpBytes + fpBytes ≤ input.size := by
    simpa [fp2Bytes, fpBytes, Nat.add_assoc] using hsize
  have hnone := decodeFp_eq_none_of_padding_nonzero hsize1 hi hnonzero
  unfold decodeFp2 EvmSemantics.Crypto.Bls12381Codec.decodeFp2
  simp only [EvmSemantics.Crypto.Bls12381Codec.fpBytes]
  have hnone' : EvmSemantics.Crypto.Bls12381Codec.decodeFp input
      (offset + 64) = none := by
    simpa [decodeFp, fpBytes] using hnone
  rw [hnone']
  cases EvmSemantics.Crypto.Bls12381Codec.decodeFp input offset <;> rfl

theorem decodeFp2_eq_none_of_first_value_ge
    {input : ByteArray} {offset : Nat}
    (hsize : offset + fp2Bytes ≤ input.size)
    (hvalue : p ≤ fpWindowValue input offset) :
    decodeFp2 input offset = none := by
  have hsize0 : offset + fpBytes ≤ input.size := by
    change offset + 128 ≤ input.size at hsize
    change offset + 64 ≤ input.size
    omega
  have hnone := decodeFp_eq_none_of_value_ge hsize0 hvalue
  unfold decodeFp2 EvmSemantics.Crypto.Bls12381Codec.decodeFp2
  have hnone' : EvmSemantics.Crypto.Bls12381Codec.decodeFp input offset = none :=
    by simpa [decodeFp] using hnone
  rw [hnone']

theorem decodeFp2_eq_none_of_second_value_ge
    {input : ByteArray} {offset : Nat}
    (hsize : offset + fp2Bytes ≤ input.size)
    (hvalue : p ≤ fpWindowValue input (offset + fpBytes)) :
    decodeFp2 input offset = none := by
  have hsize1 : offset + fpBytes + fpBytes ≤ input.size := by
    simpa [fp2Bytes, fpBytes, Nat.add_assoc] using hsize
  have hnone := decodeFp_eq_none_of_value_ge hsize1 hvalue
  unfold decodeFp2 EvmSemantics.Crypto.Bls12381Codec.decodeFp2
  simp only [EvmSemantics.Crypto.Bls12381Codec.fpBytes]
  have hnone' : EvmSemantics.Crypto.Bls12381Codec.decodeFp input
      (offset + 64) = none := by
    simpa [decodeFp, fpBytes] using hnone
  rw [hnone']
  cases EvmSemantics.Crypto.Bls12381Codec.decodeFp input offset <;> rfl

theorem decodeFp2_framed (pre suffix : ByteArray) (a : Fp2) :
    decodeFp2 (pre ++ encodeFp2 a ++ suffix) pre.size = some a := by
  apply (decodeFp2_eq_some_iff_components _ _ _).2
  unfold encodeFp2 EvmSemantics.Crypto.Bls12381Codec.encodeFp2
  constructor
  · simpa [ByteArray.append_assoc] using
      decodeFp_framed pre (encodeFp a.c1 ++ suffix) a.c0
  · have h := decodeFp_framed (pre ++ encodeFp a.c0) suffix a.c1
    rw [ByteArray.size_append, encodeFp_size] at h
    simpa [fpBytes, ByteArray.append_assoc] using h

theorem encodeFp2_decodeFp2 {input : ByteArray} {offset : Nat} {a : Fp2}
    (hdecode : decodeFp2 input offset = some a) :
    encodeFp2 a = input.extract offset (offset + fp2Bytes) := by
  obtain ⟨h0, h1⟩ := (decodeFp2_eq_some_iff_components input offset a).1 hdecode
  have he0 := encodeFp_decodeFp h0
  have he1 := encodeFp_decodeFp h1
  unfold encodeFp2 EvmSemantics.Crypto.Bls12381Codec.encodeFp2
  change encodeFp a.c0 ++ encodeFp a.c1 = _
  rw [he0, he1]
  exact (ByteArray.extract_eq_extract_append_extract (offset + fpBytes)
    (by omega) (by simp [fpBytes])).symm

theorem decodeFp2_encodeFp2 (a : Fp2) :
    decodeFp2 (encodeFp2 a) 0 = some a := by
  simpa using decodeFp2_framed ByteArray.empty ByteArray.empty a

theorem decodeFp2_eq_none_of_short {input : ByteArray} {offset : Nat}
    (hshort : input.size < offset + fp2Bytes) : decodeFp2 input offset = none := by
  have hsecond : input.size < (offset + fpBytes) + fpBytes := by
    simpa [fp2Bytes, fpBytes, Nat.add_assoc] using hshort
  have hnone : decodeFp input (offset + fpBytes) = none :=
    decodeFp_eq_none_of_short hsecond
  unfold decodeFp2 EvmSemantics.Crypto.Bls12381Codec.decodeFp2
  simp only [EvmSemantics.Crypto.Bls12381Codec.fpBytes]
  have hnone' : EvmSemantics.Crypto.Bls12381Codec.decodeFp input
      (offset + 64) = none := by
    simpa [decodeFp, fpBytes] using hnone
  rw [hnone']
  cases EvmSemantics.Crypto.Bls12381Codec.decodeFp input offset <;> rfl

theorem decodeFp2_first (a b : Fp2) :
    decodeFp2 (encodeFp2 a ++ encodeFp2 b) 0 = some a := by
  simpa using decodeFp2_framed ByteArray.empty (encodeFp2 b) a

theorem decodeFp2_second (a b : Fp2) :
    decodeFp2 (encodeFp2 a ++ encodeFp2 b) fp2Bytes = some b := by
  simpa [fp2Bytes] using
    decodeFp2_framed (encodeFp2 a) ByteArray.empty b

end Challenge.Bls12381.ProofSupport.Codec
