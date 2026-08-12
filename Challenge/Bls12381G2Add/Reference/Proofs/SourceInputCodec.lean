import Challenge.Bls12381G2Add.Reference.Proofs.SourceInputWords
import Challenge.Bls12381.ProofSupport.CodecFp2

set_option warningAsError true

/-! # G2ADD source-word/codec bridge

Only single-field windows are expanded here.  The Fp2 and point adapters
compose these compiled lemmas instead of normalizing byte extraction again.
-/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics.EVM
open Challenge.Bls12381.ProofSupport

def sourceField (yst : EvmState) (offset : Nat) : Fp.Limbs :=
  fpWords (mainDecodedWord yst offset) (mainDecodedWord yst (offset + 32))

private theorem inputWord_toNat (input : ByteArray) (offset : Nat) :
    (wordFrom input.toList offset).toNat =
      EvmSemantics.EVM.Precompile.bytesToNatPadded input offset 32 := by
  have hload := YulEvmCompiler.MemMatch.loadWord
    (Challenge.EvmProof.Bytes.memMatch_toList input) offset
  change YulEvmCompiler.conv (wordFrom input.toList offset) = _ at hload
  have hnat := congrArg EvmSemantics.UInt256.toNat hload
  simpa only [YulEvmCompiler.conv_toNat,
    Challenge.EvmProof.Bytes.readWord_toNat] using hnat

private theorem bytesNat_eq_zero_iff (bytes : List UInt8) :
    Challenge.EvmProof.Bytes.bytesNat bytes = 0 ↔
      ∀ byte ∈ bytes, byte = 0 := by
  induction bytes with
  | nil => simp [Challenge.EvmProof.Bytes.bytesNat]
  | cons head tail ih =>
      rw [Challenge.EvmProof.Bytes.bytesNat_cons]
      constructor
      · intro h
        have hpow : 0 < 256 ^ tail.length := Nat.pow_pos (by omega)
        have hmul : head.toNat * 256 ^ tail.length = 0 := by omega
        have hheadNat : head.toNat = 0 :=
          (Nat.mul_eq_zero.mp hmul).resolve_right (ne_of_gt hpow)
        have hhead : head = 0 := UInt8.ext hheadNat
        have htailNat : Challenge.EvmProof.Bytes.bytesNat tail = 0 := by omega
        simpa [hhead, ih.mp htailNat] using ih.mp htailNat
      · intro h
        have hhead : head = 0 := h head (by simp)
        have htail : ∀ byte ∈ tail, byte = 0 := by
          intro byte hmem
          exact h byte (by simp [hmem])
        simp [hhead, ih.mpr htail]

private theorem paddingZero_iff_prefix_zero (input : ByteArray) (offset : Nat)
    (hsize : offset + 64 ≤ input.size) :
    Codec.PaddingZero input offset ↔
      EvmSemantics.EVM.Precompile.bytesToNatPadded input offset 16 = 0 := by
  rw [Codec.paddingZero_iff_forall]
  unfold EvmSemantics.EVM.Precompile.bytesToNatPadded
  rw [← Challenge.EvmProof.Bytes.bytesNat_toList,
    Challenge.EvmProof.Bytes.readPadded_toList, bytesNat_eq_zero_iff]
  constructor
  · intro h byte hbyte
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hbyte
    rw [List.mem_range] at hi
    have hindex : offset + i < input.data.size := by
      change offset + i < input.size
      omega
    unfold byteFrom
    rw [List.getD_eq_getElem?_getD, YulEvmCompiler.ByteArray.toList_eq_data,
      Array.getElem?_toList, Array.getElem?_eq_getElem hindex]
    have hz := h i hi
    rw [getElem!_pos input (offset + i) (by omega)] at hz
    rw [← ByteArray.getElem_eq_getElem_data]
    exact hz
  · intro h i hi
    have hbyte := h (byteFrom input.toList (offset + i))
      (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)
    have hindex : offset + i < input.data.size := by
      change offset + i < input.size
      omega
    unfold byteFrom at hbyte
    rw [List.getD_eq_getElem?_getD, YulEvmCompiler.ByteArray.toList_eq_data,
      Array.getElem?_toList, Array.getElem?_eq_getElem hindex] at hbyte
    rw [getElem!_pos input (offset + i) (by omega)]
    rw [ByteArray.getElem_eq_getElem_data]
    exact hbyte

private theorem paddingZero_iff_inputWord_lt (input : ByteArray) (offset : Nat)
    (hsize : offset + 64 ≤ input.size) :
    Codec.PaddingZero input offset ↔
      (wordFrom input.toList offset).toNat < 2 ^ 128 := by
  rw [paddingZero_iff_prefix_zero input offset hsize, inputWord_toNat,
    Challenge.EvmProof.Bytes.bytesToNatPadded_add input offset 16 16]
  have htail := Challenge.EvmProof.Bytes.bytesToNatPadded_lt_pow
    input (offset + 16) 16
  have hpow : (256 : Nat) ^ 16 = 2 ^ 128 := by norm_num [pow_mul]
  constructor
  · intro h
    rw [h, Nat.zero_mul, Nat.zero_add, ← hpow]
    exact htail
  · intro h
    rw [← hpow] at h
    have hprefix :
        EvmSemantics.EVM.Precompile.bytesToNatPadded input offset 16 = 0 := by
      by_contra hne
      have : 256 ^ 16 ≤
          EvmSemantics.EVM.Precompile.bytesToNatPadded input offset 16 *
            256 ^ 16 := Nat.le_mul_of_pos_left _ (Nat.zero_lt_of_ne_zero hne)
      omega
    exact hprefix

private theorem word_shift_128_eq_zero_iff (word : U256) :
    word >>> 128 = (0#256 : U256) ↔ word.toNat < 2 ^ 128 := by
  constructor
  · intro h
    have hnat := congrArg BitVec.toNat h
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] at hnat
    simpa using (Nat.div_eq_zero_iff.mp hnat)
  · intro h
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
      Nat.div_eq_of_lt h]
    rfl

private theorem fpWindowValue_eq_sourceField (yst : EvmState)
    (input : ByteArray) (hcalldata : yst.env.calldata = input.toList)
    (i : Nat) (hi : i < 8) (hsize : 64 * i + 64 ≤ input.size)
    (hpadding : Codec.PaddingZero input (64 * i)) :
    Codec.fpWindowValue input (64 * i) =
      Fp.value (sourceField yst (64 * i)) := by
  have hwordHi := mainDecodedWord_eq_input yst input hcalldata (2 * i) (by omega)
  have hwordLo := mainDecodedWord_eq_input yst input hcalldata (2 * i + 1) (by omega)
  have hprefix := (paddingZero_iff_prefix_zero input (64 * i) hsize).mp hpadding
  have hfull := Challenge.EvmProof.Bytes.bytesToNatPadded_add input (64 * i) 32 32
  have hfield := Challenge.EvmProof.Bytes.bytesToNatPadded_add input (64 * i) 16 48
  have htail : EvmSemantics.EVM.Precompile.bytesToNatPadded input
      (64 * i + 16) 48 = Codec.fpWindowValue input (64 * i) := by
    unfold EvmSemantics.EVM.Precompile.bytesToNatPadded Codec.fpWindowValue
    rw [Challenge.EvmProof.Bytes.readPadded_eq_extract]
    · rfl
    · omega
  rw [hprefix, Nat.zero_mul, Nat.zero_add, htail] at hfield
  have hwordHi' : mainDecodedWord yst (64 * i) =
      wordFrom input.toList (64 * i) := by
    simpa [show 32 * (2 * i) = 64 * i by omega] using hwordHi
  have hwordLo' : mainDecodedWord yst (64 * i + 32) =
      wordFrom input.toList (64 * i + 32) := by
    simpa [show 32 * (2 * i + 1) = 64 * i + 32 by omega] using hwordLo
  calc
    Codec.fpWindowValue input (64 * i) =
        EvmSemantics.EVM.Precompile.bytesToNatPadded input (64 * i) 64 := by
      simpa using hfield.symm
    _ = EvmSemantics.EVM.Precompile.bytesToNatPadded input (64 * i) 32 *
          256 ^ 32 +
        EvmSemantics.EVM.Precompile.bytesToNatPadded input (64 * i + 32) 32 := by
      simpa using hfull
    _ = Fp.value (sourceField yst (64 * i)) := by
      unfold sourceField fpWords Fp.value Challenge.EvmProof.Limbs.radix
      rw [hwordHi', hwordLo', YulEvmCompiler.conv_toNat,
        YulEvmCompiler.conv_toNat, inputWord_toNat, inputWord_toNat]
      norm_num [pow_mul]
      ring

theorem decodeFp_eq_some_sourceField (yst : EvmState) (input : ByteArray)
    (hcalldata : yst.env.calldata = input.toList) (i : Nat) (hi : i < 8)
    (hsize : 64 * i + 64 ≤ input.size) :
    Codec.decodeFp input (64 * i) =
      some (Fp.toField (sourceField yst (64 * i))) ↔
      Codec.PaddingZero input (64 * i) ∧
        Fp.Canonical (sourceField yst (64 * i)) := by
  rw [Codec.decodeFp_eq_some_iff]
  constructor
  · rintro ⟨_, hpadding, hvalue⟩
    refine ⟨hpadding, ?_⟩
    have hfield := fpWindowValue_eq_sourceField yst input hcalldata i hi
      hsize hpadding
    constructor
    · have hword := mainDecodedWord_eq_input yst input hcalldata (2 * i) (by omega)
      have hword' : mainDecodedWord yst (64 * i) =
          wordFrom input.toList (64 * i) := by
        simpa [show 32 * (2 * i) = 64 * i by omega] using hword
      unfold sourceField fpWords
      rw [hword', YulEvmCompiler.conv_toNat]
      exact (paddingZero_iff_inputWord_lt input (64 * i) hsize).mp hpadding
    · calc
        Fp.value (sourceField yst (64 * i)) =
            Codec.fpWindowValue input (64 * i) := hfield.symm
        _ = (Fp.toField (sourceField yst (64 * i))).val := hvalue
        _ < EvmSemantics.Crypto.Bls12381.p :=
          (Fp.toField (sourceField yst (64 * i))).isLt
  · rintro ⟨hpadding, hcanonical⟩
    refine ⟨hsize, hpadding, ?_⟩
    rw [fpWindowValue_eq_sourceField yst input hcalldata i hi hsize hpadding]
    unfold Fp.toField
    rw [Fin.val_ofNat, Nat.mod_eq_of_lt hcanonical.2]

/-- A complete source-word characterization of field-decoder rejection. -/
theorem decodeFp_eq_none_iff_sourceField (yst : EvmState) (input : ByteArray)
    (hcalldata : yst.env.calldata = input.toList) (i : Nat) (hi : i < 8)
    (hsize : 64 * i + 64 ≤ input.size) :
    Codec.decodeFp input (64 * i) = none ↔
      ¬ Codec.PaddingZero input (64 * i) ∨
        ¬ Fp.Canonical (sourceField yst (64 * i)) := by
  have hsome := decodeFp_eq_some_sourceField yst input hcalldata i hi hsize
  constructor
  · intro hnone
    by_contra hvalid
    push Not at hvalid
    rw [hsome.mpr hvalid] at hnone
    contradiction
  · intro hinvalid
    cases hdecode : Codec.decodeFp input (64 * i) with
    | none => rfl
    | some a =>
        have ha := (Codec.decodeFp_eq_some_iff input (64 * i) a).mp hdecode
        have hfield := fpWindowValue_eq_sourceField yst input hcalldata i hi
          hsize ha.2.1
        have hvalue : Fp.value (sourceField yst (64 * i)) <
            EvmSemantics.Crypto.Bls12381.p := by
          rw [← hfield, ha.2.2]
          exact a.isLt
        have hcanon : Fp.Canonical (sourceField yst (64 * i)) :=
          Fp.canonical_of_value_lt _ hvalue
        exact False.elim (hinvalid.elim (fun h => h ha.2.1)
          (fun h => h hcanon))

theorem sourceFp2_eq_fields (yst : EvmState) (i : Nat) (hi : i < 4) :
    sourceFp2 yst (128 * i) = Fp2.mkRepr
      (sourceField yst (128 * i)) (sourceField yst (128 * i + 64)) := by
  interval_cases i <;>
    simp [sourceFp2, fp2At, Fp2.mkRepr, sourceField, fpWords,
      mainDecodedWord]

theorem decodeFp2_eq_some_sourceFp2 (yst : EvmState) (input : ByteArray)
    (hcalldata : yst.env.calldata = input.toList) (i : Nat) (hi : i < 4)
    (hsize : 128 * i + 128 ≤ input.size) :
    Codec.decodeFp2 input (128 * i) =
      some (Fp2.toField (sourceFp2 yst (128 * i))) ↔
      Codec.PaddingZero input (128 * i) ∧
      Codec.PaddingZero input (128 * i + 64) ∧
      Fp2.Canonical (sourceFp2 yst (128 * i)) := by
  rw [Codec.decodeFp2_eq_some_iff_components]
  have h0 := decodeFp_eq_some_sourceField yst input hcalldata (2 * i) (by omega)
    (by omega)
  have h1 := decodeFp_eq_some_sourceField yst input hcalldata (2 * i + 1)
    (by omega) (by omega)
  rw [show 64 * (2 * i) = 128 * i by omega] at h0
  rw [show 64 * (2 * i + 1) = 128 * i + 64 by omega] at h1
  rw [sourceFp2_eq_fields yst i hi, Fp2.toField_mkRepr,
    Fp2.canonical_iff]
  simp only [Codec.fpBytes, Fp2.mkRepr]
  change (_ = some (Fp.toField (sourceField yst (128 * i))) ∧
    _ = some (Fp.toField (sourceField yst (128 * i + 64)))) ↔ _
  rw [h0, h1]
  constructor
  · rintro ⟨⟨hp0, hc0⟩, hp1, hc1⟩
    exact ⟨hp0, hp1, hc0, hc1⟩
  · rintro ⟨hp0, hp1, hc0, hc1⟩
    exact ⟨⟨hp0, hc0⟩, hp1, hc1⟩

theorem decodeFp2_eq_none_iff_sourceFp2 (yst : EvmState) (input : ByteArray)
    (hcalldata : yst.env.calldata = input.toList) (i : Nat) (hi : i < 4)
    (hsize : 128 * i + 128 ≤ input.size) :
    Codec.decodeFp2 input (128 * i) = none ↔
      ¬ Codec.PaddingZero input (128 * i) ∨
      ¬ Codec.PaddingZero input (128 * i + 64) ∨
      ¬ Fp2.Canonical (sourceFp2 yst (128 * i)) := by
  have hsome := decodeFp2_eq_some_sourceFp2 yst input hcalldata i hi hsize
  constructor
  · intro hnone
    by_contra hvalid
    push Not at hvalid
    rw [hsome.mpr hvalid] at hnone
    contradiction
  · intro hinvalid
    cases hdecode : Codec.decodeFp2 input (128 * i) with
    | none => rfl
    | some a =>
        obtain ⟨h0, h1⟩ :=
          (Codec.decodeFp2_eq_some_iff_components input (128 * i) a).mp hdecode
        rcases hinvalid with hp0 | hp1 | hcanonical
        · have hnone := (decodeFp_eq_none_iff_sourceField yst input hcalldata
              (2 * i) (by omega) (by omega)).mpr (Or.inl (by
                simpa [show 64 * (2 * i) = 128 * i by omega] using hp0))
          rw [show 64 * (2 * i) = 128 * i by omega] at hnone
          rw [hnone] at h0
          contradiction
        · have hnone := (decodeFp_eq_none_iff_sourceField yst input hcalldata
              (2 * i + 1) (by omega) (by omega)).mpr (Or.inl (by
                simpa [show 64 * (2 * i + 1) = 128 * i + 64 by omega]
                  using hp1))
          rw [show 64 * (2 * i + 1) = 128 * i + 64 by omega] at hnone
          have h1' : Codec.decodeFp input (128 * i + 64) = some a.c1 := by
            simpa [Codec.fpBytes] using h1
          rw [hnone] at h1'
          contradiction
        · have hc : ¬ Fp.Canonical (sourceField yst (128 * i)) ∨
              ¬ Fp.Canonical (sourceField yst (128 * i + 64)) := by
            rw [sourceFp2_eq_fields yst i hi, Fp2.canonical_iff] at hcanonical
            simpa only [Fp2.mkRepr, not_and_or] using hcanonical
          rcases hc with hc0 | hc1
          · have hnone := (decodeFp_eq_none_iff_sourceField yst input hcalldata
                (2 * i) (by omega) (by omega)).mpr (Or.inr (by
                  simpa [show 64 * (2 * i) = 128 * i by omega] using hc0))
            rw [show 64 * (2 * i) = 128 * i by omega] at hnone
            rw [hnone] at h0
            contradiction
          · have hnone := (decodeFp_eq_none_iff_sourceField yst input hcalldata
                (2 * i + 1) (by omega) (by omega)).mpr (Or.inr (by
                  simpa [show 64 * (2 * i + 1) = 128 * i + 64 by omega]
                    using hc1))
            rw [show 64 * (2 * i + 1) = 128 * i + 64 by omega] at hnone
            have h1' : Codec.decodeFp input (128 * i + 64) = some a.c1 := by
              simpa [Codec.fpBytes] using h1
            rw [hnone] at h1'
            contradiction

theorem pointPaddingZero_iff_codec (yst : EvmState) (input : ByteArray)
    (hcalldata : yst.env.calldata = input.toList) (point : Nat)
    (halign : point % 256 = 0) (hpoint : point ≤ 256)
    (hsize : input.size = 512) :
    PointPaddingZero (mainDecodedState yst) (BitVec.ofNat 256 point) ↔
      Codec.PaddingZero input point ∧ Codec.PaddingZero input (point + 64) ∧
      Codec.PaddingZero input (point + 128) ∧
      Codec.PaddingZero input (point + 192) := by
  have hp : point = 0 ∨ point = 256 := by omega
  rcases hp with rfl | rfl
  · change (((mainDecodedWord yst 0 >>> 128) |||
        (mainDecodedWord yst 64 >>> 128)) |||
      ((mainDecodedWord yst 128 >>> 128) |||
        (mainDecodedWord yst 192 >>> 128)) = (0#256 : U256)) ↔ _
    rw [BitVec.or_eq_zero_iff (x := (mainDecodedWord yst 0 >>> 128) |||
        (mainDecodedWord yst 64 >>> 128))
      (y := (mainDecodedWord yst 128 >>> 128) |||
        (mainDecodedWord yst 192 >>> 128)),
      BitVec.or_eq_zero_iff (x := mainDecodedWord yst 0 >>> 128)
        (y := mainDecodedWord yst 64 >>> 128),
      BitVec.or_eq_zero_iff (x := mainDecodedWord yst 128 >>> 128)
        (y := mainDecodedWord yst 192 >>> 128)]
    rw [mainDecodedWord_eq_input yst input hcalldata 0 (by omega),
      mainDecodedWord_eq_input yst input hcalldata 2 (by omega),
      mainDecodedWord_eq_input yst input hcalldata 4 (by omega),
      mainDecodedWord_eq_input yst input hcalldata 6 (by omega)]
    norm_num
    rw [word_shift_128_eq_zero_iff, word_shift_128_eq_zero_iff,
      word_shift_128_eq_zero_iff, word_shift_128_eq_zero_iff,
      ← paddingZero_iff_inputWord_lt input 0 (by omega),
      ← paddingZero_iff_inputWord_lt input 64 (by omega),
      ← paddingZero_iff_inputWord_lt input 128 (by omega),
      ← paddingZero_iff_inputWord_lt input 192 (by omega)]
    tauto
  · change (((mainDecodedWord yst 256 >>> 128) |||
        (mainDecodedWord yst 320 >>> 128)) |||
      ((mainDecodedWord yst 384 >>> 128) |||
        (mainDecodedWord yst 448 >>> 128)) = (0#256 : U256)) ↔ _
    rw [BitVec.or_eq_zero_iff (x := (mainDecodedWord yst 256 >>> 128) |||
        (mainDecodedWord yst 320 >>> 128))
      (y := (mainDecodedWord yst 384 >>> 128) |||
        (mainDecodedWord yst 448 >>> 128)),
      BitVec.or_eq_zero_iff (x := mainDecodedWord yst 256 >>> 128)
        (y := mainDecodedWord yst 320 >>> 128),
      BitVec.or_eq_zero_iff (x := mainDecodedWord yst 384 >>> 128)
        (y := mainDecodedWord yst 448 >>> 128)]
    rw [mainDecodedWord_eq_input yst input hcalldata 8 (by omega),
      mainDecodedWord_eq_input yst input hcalldata 10 (by omega),
      mainDecodedWord_eq_input yst input hcalldata 12 (by omega),
      mainDecodedWord_eq_input yst input hcalldata 14 (by omega)]
    norm_num
    rw [word_shift_128_eq_zero_iff, word_shift_128_eq_zero_iff,
      word_shift_128_eq_zero_iff, word_shift_128_eq_zero_iff,
      ← paddingZero_iff_inputWord_lt input 256 (by omega),
      ← paddingZero_iff_inputWord_lt input 320 (by omega),
      ← paddingZero_iff_inputWord_lt input 384 (by omega),
      ← paddingZero_iff_inputWord_lt input 448 (by omega)]
    tauto

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
