import Challenge.EvmProof.ByteWindow

set_option warningAsError true

/-! # EIP-2537 scalar codec boundary

Scalars in the MSM wire format are unsigned 256-bit integers.  Decoding does
not reduce them modulo the BLS subgroup order.
-/

namespace Challenge.Bls12381.ProofSupport.Codec

/-- Width of an EIP-2537 MSM scalar. -/
def scalarBytes : Nat := 32

/-- The exact unsigned big-endian value in a scalar window. -/
def scalarWindowValue (input : ByteArray) (offset : Nat) : Nat :=
  EvmSemantics.Data.Bytes.bytesToBigEndianNat
    (input.extract offset (offset + scalarBytes))

/-- Decode one fixed-width unsigned scalar, without subgroup-order reduction.
-/
def decodeScalar (input : ByteArray) (offset : Nat) : Option Nat :=
  if offset + scalarBytes > input.size then none
  else some (scalarWindowValue input offset)

/-- Encode a scalar in the 32-byte EIP window.  The proof argument makes the
no-truncation precondition explicit at every call site. -/
def encodeScalar (scalar : Nat) (_hscalar : scalar < 2 ^ 256) : ByteArray :=
  EvmSemantics.Data.Bytes.natToBytesPadded scalar scalarBytes

@[simp] theorem encodeScalar_size (scalar : Nat) (hscalar : scalar < 2 ^ 256) :
    (encodeScalar scalar hscalar).size = scalarBytes := by
  simp [encodeScalar, scalarBytes,
    YulEvmCompiler.BytesLemmas.natToBytesPadded_size]

theorem decodeScalar_eq_some_iff (input : ByteArray) (offset scalar : Nat) :
    decodeScalar input offset = some scalar ↔
      offset + scalarBytes ≤ input.size ∧
      scalarWindowValue input offset = scalar := by
  unfold decodeScalar
  by_cases hsize : offset + scalarBytes ≤ input.size
  · rw [if_neg (by omega)]
    constructor
    · intro h
      exact ⟨hsize, Option.some.inj h⟩
    · rintro ⟨_, hvalue⟩
      exact congrArg some hvalue
  · rw [if_pos (by omega)]
    simp [hsize]

theorem decodeScalar_eq_none_iff (input : ByteArray) (offset : Nat) :
    decodeScalar input offset = none ↔ input.size < offset + scalarBytes := by
  unfold decodeScalar
  by_cases hsize : offset + scalarBytes ≤ input.size
  · rw [if_neg (by omega)]
    simp [hsize]
  · rw [if_pos (by omega)]
    constructor
    · intro _
      omega
    · intro _
      rfl

theorem scalarWindowValue_lt (input : ByteArray) (offset : Nat) :
    scalarWindowValue input offset < 2 ^ 256 := by
  unfold scalarWindowValue
  have h := Challenge.EvmProof.Bytes.bytesNat_lt_pow
    (input.extract offset (offset + scalarBytes)).toList
  rw [← Challenge.EvmProof.Bytes.bytesNat_toList]
  have hlength :
      (input.extract offset (offset + scalarBytes)).toList.length ≤ 32 := by
    simp only [YulEvmCompiler.ByteArray.toList_eq_data, Array.length_toList]
    change (input.extract offset (offset + scalarBytes)).size ≤ 32
    rw [ByteArray.size_extract]
    simp [scalarBytes]
    omega
  exact h.trans_le (Nat.pow_le_pow_right (by omega) hlength)

theorem decodeScalar_value_lt {input : ByteArray} {offset scalar : Nat}
    (hdecode : decodeScalar input offset = some scalar) : scalar < 2 ^ 256 := by
  obtain ⟨_, hvalue⟩ :=
    (decodeScalar_eq_some_iff input offset scalar).1 hdecode
  rw [← hvalue]
  exact scalarWindowValue_lt input offset

theorem decodeScalar_framed (pre suffix : ByteArray) (scalar : Nat)
    (hscalar : scalar < 2 ^ 256) :
    decodeScalar (pre ++ encodeScalar scalar hscalar ++ suffix) pre.size =
      some scalar := by
  apply (decodeScalar_eq_some_iff _ _ _).2
  constructor
  · simp [encodeScalar_size]
  · unfold scalarWindowValue
    rw [← encodeScalar_size scalar hscalar]
    rw [Challenge.EvmProof.ByteWindow.extract_append_window]
    apply Challenge.EvmProof.Memory.bytesToBigEndianNat_natToBytesPadded
    simpa [show 256 ^ scalarBytes = 2 ^ 256 by norm_num [scalarBytes]]
      using hscalar

theorem encodeScalar_decodeScalar {input : ByteArray} {offset scalar : Nat}
    (hdecode : decodeScalar input offset = some scalar) :
    encodeScalar scalar (decodeScalar_value_lt hdecode) =
      input.extract offset (offset + scalarBytes) := by
  obtain ⟨hsize, hvalue⟩ :=
    (decodeScalar_eq_some_iff input offset scalar).1 hdecode
  let window := input.extract offset (offset + scalarBytes)
  unfold scalarWindowValue at hvalue
  change EvmSemantics.Data.Bytes.bytesToBigEndianNat window = scalar at hvalue
  unfold encodeScalar
  change EvmSemantics.Data.Bytes.natToBytesPadded scalar scalarBytes = window
  rw [← hvalue]
  have hwindowSize : window.size = scalarBytes := by
    dsimp only [window]
    rw [ByteArray.size_extract, min_eq_left hsize]
    omega
  rw [← hwindowSize]
  exact Challenge.EvmProof.ByteWindow.natToBytesPadded_bytesToBigEndianNat _

theorem scalarWindowValue_framed (pre window suffix : ByteArray)
    (hwindow : window.size = scalarBytes) :
    scalarWindowValue (pre ++ window ++ suffix) pre.size =
      EvmSemantics.Data.Bytes.bytesToBigEndianNat window := by
  unfold scalarWindowValue
  have hend : pre.size + scalarBytes = pre.size + window.size := by omega
  rw [hend, Challenge.EvmProof.ByteWindow.extract_append_window]

end Challenge.Bls12381.ProofSupport.Codec
