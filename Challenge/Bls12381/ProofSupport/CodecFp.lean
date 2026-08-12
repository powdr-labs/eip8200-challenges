import Challenge.Bls12381.ProofSupport.CodecCore
import Challenge.EvmProof.ByteWindow

set_option warningAsError true

/-! # Exact EIP-2537 base-field codec boundary -/

namespace Challenge.Bls12381.ProofSupport.Codec

open EvmSemantics.Crypto.Bls12381

/-- The EIP-2537 requirement that every byte in the 16-byte high padding
window is zero. -/
def PaddingZero (input : ByteArray) (offset : Nat) : Prop :=
  input[offset]! = 0 ∧
  input[offset + 1]! = 0 ∧
  input[offset + 2]! = 0 ∧
  input[offset + 3]! = 0 ∧
  input[offset + 4]! = 0 ∧
  input[offset + 5]! = 0 ∧
  input[offset + 6]! = 0 ∧
  input[offset + 7]! = 0 ∧
  input[offset + 8]! = 0 ∧
  input[offset + 9]! = 0 ∧
  input[offset + 10]! = 0 ∧
  input[offset + 11]! = 0 ∧
  input[offset + 12]! = 0 ∧
  input[offset + 13]! = 0 ∧
  input[offset + 14]! = 0 ∧
  input[offset + 15]! = 0

/-- The unsigned big-endian value carried by the trailing 48-byte field
window. -/
def fpWindowValue (input : ByteArray) (offset : Nat) : Nat :=
  EvmSemantics.Data.Bytes.bytesToBigEndianNat
    (input.extract (offset + 16) (offset + fpBytes))

private def fpPaddingCheck (input : ByteArray) (offset : Nat) : Bool := Id.run do
  for i in [0:16] do
    if input[offset + i]! ≠ 0 then return false
  return true

private theorem fpPaddingCheck_eq_true_iff (input : ByteArray) (offset : Nat) :
    fpPaddingCheck input offset = true ↔ PaddingZero input offset := by
  unfold fpPaddingCheck PaddingZero
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  norm_num [List.range']
  by_cases h0 : input[offset]! = 0 <;> simp_all
  by_cases h1 : input[offset + 1]! = 0 <;> simp_all
  by_cases h2 : input[offset + 2]! = 0 <;> simp_all
  by_cases h3 : input[offset + 3]! = 0 <;> simp_all
  by_cases h4 : input[offset + 4]! = 0 <;> simp_all
  by_cases h5 : input[offset + 5]! = 0 <;> simp_all
  by_cases h6 : input[offset + 6]! = 0 <;> simp_all
  by_cases h7 : input[offset + 7]! = 0 <;> simp_all
  by_cases h8 : input[offset + 8]! = 0 <;> simp_all
  by_cases h9 : input[offset + 9]! = 0 <;> simp_all
  by_cases h10 : input[offset + 10]! = 0 <;> simp_all
  by_cases h11 : input[offset + 11]! = 0 <;> simp_all
  by_cases h12 : input[offset + 12]! = 0 <;> simp_all
  by_cases h13 : input[offset + 13]! = 0 <;> simp_all
  by_cases h14 : input[offset + 14]! = 0 <;> simp_all
  by_cases h15 : input[offset + 15]! = 0 <;> simp_all

private theorem decodeFp_eq_model (input : ByteArray) (offset : Nat) :
    decodeFp input offset =
      if offset + EvmSemantics.Crypto.Bls12381Codec.fpBytes > input.size then none
      else if ¬ fpPaddingCheck input offset then none
      else
        let n := EvmSemantics.Data.Bytes.bytesToBigEndianNat
          (input.extract (offset + 16) (offset + 64))
        if n ≥ p then none else some (Fin.ofNat _ n) := by
  rfl

theorem paddingZero_iff_forall (input : ByteArray) (offset : Nat) :
    PaddingZero input offset ↔
      ∀ i, i < 16 → input[offset + i]! = 0 := by
  constructor
  · intro h i hi
    interval_cases i <;> simp_all [PaddingZero]
  · intro h
    unfold PaddingZero
    exact ⟨h 0 (by omega), h 1 (by omega), h 2 (by omega),
      h 3 (by omega), h 4 (by omega), h 5 (by omega), h 6 (by omega),
      h 7 (by omega), h 8 (by omega), h 9 (by omega), h 10 (by omega),
      h 11 (by omega), h 12 (by omega), h 13 (by omega), h 14 (by omega),
      h 15 (by omega)⟩

theorem decodeFp_eq_none_of_short {input : ByteArray} {offset : Nat}
    (hshort : input.size < offset + fpBytes) : decodeFp input offset = none := by
  change input.size < offset + 64 at hshort
  unfold decodeFp EvmSemantics.Crypto.Bls12381Codec.decodeFp
  rw [if_pos (by
    simpa [EvmSemantics.Crypto.Bls12381Codec.fpBytes] using hshort)]

theorem decodeFp_eq_none_of_padding_nonzero {input : ByteArray} {offset i : Nat}
    (hsize : offset + fpBytes ≤ input.size) (hi : i < 16)
    (hnonzero : input[offset + i]! ≠ 0) : decodeFp input offset = none := by
  have hpadding : ¬ PaddingZero input offset := by
    rw [paddingZero_iff_forall]
    push Not
    exact ⟨i, hi, hnonzero⟩
  have hcheck : fpPaddingCheck input offset = false := by
    cases h : fpPaddingCheck input offset <;> simp_all [fpPaddingCheck_eq_true_iff]
  rw [decodeFp_eq_model]
  rw [if_neg (by simpa [EvmSemantics.Crypto.Bls12381Codec.fpBytes]
    using hsize)]
  simp [hcheck]

theorem decodeFp_eq_none_of_first_padding_nonzero
    {input : ByteArray} {offset : Nat}
    (hsize : offset + fpBytes ≤ input.size) (hnonzero : input[offset]! ≠ 0) :
    decodeFp input offset = none :=
  decodeFp_eq_none_of_padding_nonzero (i := 0) hsize (by omega)
    (by simpa using hnonzero)

theorem decodeFp_some_isCanonical {input : ByteArray} {offset : Nat} {a : Fp}
    (_hdecode : decodeFp input offset = some a) : a.val < p := a.isLt

theorem decodeFp_eq_none_of_value_ge {input : ByteArray} {offset : Nat}
    (hsize : offset + fpBytes ≤ input.size)
    (hvalue : p ≤ fpWindowValue input offset) :
    decodeFp input offset = none := by
  by_cases hpadding : PaddingZero input offset
  · have hcheck : fpPaddingCheck input offset = true :=
      (fpPaddingCheck_eq_true_iff input offset).2 hpadding
    have hraw : p ≤ EvmSemantics.Data.Bytes.bytesToBigEndianNat
        (input.extract (offset + 16) (offset + 64)) := by
      simpa [fpWindowValue, EvmSemantics.Crypto.Bls12381Codec.fpBytes]
        using hvalue
    rw [decodeFp_eq_model]
    rw [if_neg (by simpa [EvmSemantics.Crypto.Bls12381Codec.fpBytes]
      using hsize)]
    simp [hcheck, hraw]
  · rw [paddingZero_iff_forall] at hpadding
    push Not at hpadding
    obtain ⟨i, hi, hnonzero⟩ := hpadding
    exact decodeFp_eq_none_of_padding_nonzero hsize hi hnonzero

theorem decodeFp_eq_some_iff (input : ByteArray) (offset : Nat) (a : Fp) :
    decodeFp input offset = some a ↔
      offset + fpBytes ≤ input.size ∧
      PaddingZero input offset ∧ fpWindowValue input offset = a.val := by
  constructor
  · intro hdecode
    have hsize : offset + fpBytes ≤ input.size := by
      by_contra h
      have hshort : input.size < offset + fpBytes := by omega
      rw [decodeFp_eq_none_of_short hshort] at hdecode
      simp at hdecode
    have hpadding : PaddingZero input offset := by
      apply (paddingZero_iff_forall input offset).2
      intro i hi
      by_contra hnonzero
      have hnone := decodeFp_eq_none_of_padding_nonzero hsize hi hnonzero
      rw [hnone] at hdecode
      simp at hdecode
    have hvalueLt : fpWindowValue input offset < p := by
      by_contra h
      have hnone := decodeFp_eq_none_of_value_ge hsize (by omega)
      rw [hnone] at hdecode
      simp at hdecode
    refine ⟨hsize, hpadding, ?_⟩
    have hcheck : fpPaddingCheck input offset = true :=
      (fpPaddingCheck_eq_true_iff input offset).2 hpadding
    rw [decodeFp_eq_model] at hdecode
    rw [if_neg (by simpa [EvmSemantics.Crypto.Bls12381Codec.fpBytes]
      using hsize)] at hdecode
    simp [hcheck] at hdecode
    have hrawLt := hdecode.1
    have ha := hdecode.2
    have hval := congrArg Fin.val ha
    simpa [fpWindowValue, EvmSemantics.Crypto.Bls12381Codec.fpBytes,
      Nat.mod_eq_of_lt hrawLt] using hval
  · rintro ⟨hsize, hpadding, hvalue⟩
    have hvalueLt : fpWindowValue input offset < p := hvalue.symm ▸ a.isLt
    have hcheck : fpPaddingCheck input offset = true :=
      (fpPaddingCheck_eq_true_iff input offset).2 hpadding
    have hrawLt : EvmSemantics.Data.Bytes.bytesToBigEndianNat
        (input.extract (offset + 16) (offset + 64)) < p := by
      simpa [fpWindowValue, EvmSemantics.Crypto.Bls12381Codec.fpBytes]
        using hvalueLt
    rw [decodeFp_eq_model]
    rw [if_neg (by simpa [EvmSemantics.Crypto.Bls12381Codec.fpBytes]
      using hsize)]
    simp [hcheck]
    refine ⟨hrawLt, ?_⟩
    apply Fin.ext
    simpa [fpWindowValue, EvmSemantics.Crypto.Bls12381Codec.fpBytes,
      Nat.mod_eq_of_lt hrawLt] using hvalue

theorem decodeFp_isSome_iff (input : ByteArray) (offset : Nat) :
    (decodeFp input offset).isSome = true ↔
      offset + fpBytes ≤ input.size ∧
      PaddingZero input offset ∧ fpWindowValue input offset < p := by
  constructor
  · intro hsome
    cases hdecode : decodeFp input offset with
    | none => simp [hdecode] at hsome
    | some a =>
        obtain ⟨hsize, hpadding, hvalue⟩ :=
          (decodeFp_eq_some_iff input offset a).1 hdecode
        exact ⟨hsize, hpadding, hvalue.symm ▸ a.isLt⟩
  · rintro ⟨hsize, hpadding, hvalue⟩
    let a : Fp := ⟨fpWindowValue input offset, hvalue⟩
    have hdecode : decodeFp input offset = some a :=
      (decodeFp_eq_some_iff input offset a).2 ⟨hsize, hpadding, rfl⟩
    simp [hdecode]

theorem encodeFp_decodeFp {input : ByteArray} {offset : Nat} {a : Fp}
    (hdecode : decodeFp input offset = some a) :
    encodeFp a = input.extract offset (offset + fpBytes) := by
  obtain ⟨hsize, hpadding, hvalue⟩ :=
    (decodeFp_eq_some_iff input offset a).1 hdecode
  let tail := input.extract (offset + 16) (offset + fpBytes)
  have htailSize : tail.size = 48 := by
    dsimp only [tail, fpBytes]
    rw [ByteArray.size_extract]
    have hsize64 : offset + 64 ≤ input.size := by
      simpa [fpBytes] using hsize
    omega
  have htail :
      EvmSemantics.Data.Bytes.natToBytesPadded a.val 48 = tail := by
    rw [← htailSize, ← hvalue]
    exact Challenge.EvmProof.ByteWindow.natToBytesPadded_bytesToBigEndianNat tail
  have ha48 : a.val < 256 ^ 48 := by
    exact a.isLt.trans (by norm_num [p, absU])
  unfold encodeFp EvmSemantics.Crypto.Bls12381Codec.encodeFp
  change EvmSemantics.Data.Bytes.natToBytesPadded a.val 64 = _
  rw [show 64 = 16 + 48 by omega,
    Challenge.EvmProof.ByteWindow.natToBytesPadded_prefix_zeros
      a.val 16 48 ha48, htail]
  have hsize64 : offset + 64 ≤ input.size := by
    simpa [fpBytes] using hsize
  rw [ByteArray.extract_eq_extract_append_extract (offset + 16)
    (by omega) (by simp [fpBytes])]
  congr 1
  apply ByteArray.ext_getElem
  · change (Array.replicate 16 (0 : UInt8)).size = _
    rw [Array.size_replicate, ByteArray.size_extract]
    have hsize16 : offset + 16 ≤ input.size := by omega
    rw [min_eq_left hsize16]
    omega
  · intro i hiLeft hiRight
    have hi : i < 16 := by
      change i < (Array.replicate 16 (0 : UInt8)).size at hiLeft
      rw [Array.size_replicate] at hiLeft
      exact hiLeft
    rw [ByteArray.getElem_extract]
    have htop := (paddingZero_iff_forall input offset).1 hpadding i hi
    change (Array.replicate 16 (0 : UInt8))[i] = _
    rw [Array.getElem_replicate]
    have hbound : offset + i < input.size := by omega
    rw [getElem!_pos input (offset + i) hbound] at htop
    simpa [Nat.add_comm] using htop.symm

/-- Decoding is local to its exact 64-byte window. -/
theorem decodeFp_framed (pre suffix : ByteArray) (a : Fp) :
    decodeFp (pre ++ encodeFp a ++ suffix) pre.size = some a := by
  have hp : p < 256 ^ 48 := by norm_num [p, absU]
  have ha48 : a.val < 256 ^ 48 := a.isLt.trans hp
  let encoded := encodeFp a
  let input := pre ++ encoded ++ suffix
  have hencodedSize : encoded.size = 64 := by
    exact YulEvmCompiler.BytesLemmas.natToBytesPadded_size _ _
  have hinputSize : input.size = pre.size + 64 + suffix.size := by
    simp [input, hencodedSize]
  have hbyte : ∀ i, i < 64 →
      input[pre.size + i]?.getD 0 = encoded[i]?.getD 0 := by
    intro i hi
    simp only [input, Challenge.EvmProof.Memory.getElem?_getD_append]
    rw [if_pos (by simp [hencodedSize]; omega)]
    rw [if_neg (by omega)]
    congr 2
    omega
  have htop : ∀ i, i < 16 → input[pre.size + i]! = 0 := by
    intro i hi
    rw [← Challenge.EvmProof.Memory.getD0_eq_getElem!]
    rw [hbyte i (by omega)]
    change (EvmSemantics.Data.Bytes.natToBytesPadded a.val 64)[i]?.getD 0 = 0
    rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_getElem?_getD _ 64 i
      (by omega)]
    have hexp : 48 ≤ 64 - 1 - i := by omega
    have hpow : 256 ^ 48 ≤ 256 ^ (64 - 1 - i) :=
      Nat.pow_le_pow_right (by omega) hexp
    rw [Nat.div_eq_of_lt (ha48.trans_le hpow)]
    rfl
  have htop0 : input[pre.size]! = 0 := by
    simpa using htop 0 (by omega)
  have htail : input.extract (pre.size + 16) (pre.size + 64) =
      EvmSemantics.Data.Bytes.natToBytesPadded a.val 48 := by
    apply ByteArray.ext_getElem
    · rw [ByteArray.size_extract,
        YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
      omega
    · intro i hiLeft hiRight
      have hi : i < 48 := by
        rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size] at hiRight
        exact hiRight
      rw [ByteArray.getElem_extract]
      rw [← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hiRight]
      rw [← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ (by
        rw [hinputSize]
        omega)]
      rw [show pre.size + 16 + i = pre.size + (16 + i) by omega]
      rw [hbyte (16 + i) (by omega)]
      change (EvmSemantics.Data.Bytes.natToBytesPadded a.val 64)[16 + i]?.getD 0 = _
      rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_getElem?_getD _ 64
        (16 + i) (by omega)]
      rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_getElem?_getD _ 48 i hi]
      rw [show 64 - 1 - (16 + i) = 48 - 1 - i by omega]
  change EvmSemantics.Crypto.Bls12381Codec.decodeFp input pre.size = some a
  unfold EvmSemantics.Crypto.Bls12381Codec.decodeFp
  rw [if_neg (by simp [EvmSemantics.Crypto.Bls12381Codec.fpBytes, hinputSize])]
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  norm_num [List.range', htop, htop0, htail]
  rw [Challenge.EvmProof.Memory.bytesToBigEndianNat_natToBytesPadded _ 48 ha48]
  exact ⟨a.isLt, by apply Fin.ext; simp⟩

theorem decodeFp_encodeFp (a : Fp) : decodeFp (encodeFp a) 0 = some a := by
  simpa using decodeFp_framed ByteArray.empty ByteArray.empty a

theorem decodeFp_first (a b : Fp) :
    decodeFp (encodeFp a ++ encodeFp b) 0 = some a := by
  simpa using decodeFp_framed ByteArray.empty (encodeFp b) a

theorem decodeFp_second (a b : Fp) :
    decodeFp (encodeFp a ++ encodeFp b) fpBytes = some b := by
  simpa [fpBytes] using decodeFp_framed (encodeFp a) ByteArray.empty b

end Challenge.Bls12381.ProofSupport.Codec
