import Challenge.Bls12381G1Add.Reference.Proofs.SourceMainFull

set_option warningAsError true

/-! # G1ADD calldata/source-word bridge -/

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics.EVM
open Challenge.Bls12381.ProofSupport

private theorem mainDecodedState_memory (yst : EvmState) :
    (mainDecodedState yst).memory =
      storeWord
        (storeWord
          (storeWord
            (storeWord
              (storeWord
                (storeWord
                  (storeWord
                    (storeWord yst.memory 0 (mainInputWord yst 0))
                    32 (mainInputWord yst 32))
                  64 (mainInputWord yst 64))
                96 (mainInputWord yst 96))
              128 (mainInputWord yst 128))
            160 (mainInputWord yst 160))
          192 (mainInputWord yst 192))
        224 (mainInputWord yst 224) := by
  rfl

private theorem loadWord_eq_wordFrom_of_readBytes
    (memory : Nat → UInt8) (offset source : Nat) (input : ByteArray)
    (hbytes : readBytes memory offset 32 =
      (EvmSemantics.MachineState.readPadded input source 32).toList) :
    loadWord memory offset = wordFrom input.toList source := by
  have hload : loadWord memory offset =
      (readBytes memory offset 32).foldl
        (fun (acc : U256) byte =>
          (acc <<< (8 : Nat)) ||| BitVec.ofNat 256 byte.toNat) 0 := by
    unfold loadWord readBytes
    rw [List.foldl_map]
  rw [hload, hbytes, Challenge.EvmProof.Bytes.readPadded_toList]
  unfold wordFrom
  rw [List.foldl_map]

private theorem mainDecodedState_read (yst : EvmState) (input : ByteArray)
    (hcalldata : yst.env.calldata = input.toList) (i : Nat) (hi : i < 8) :
    readBytes (mainDecodedState yst).memory (32 * i) 32 =
      (EvmSemantics.MachineState.readPadded input (32 * i) 32).toList := by
  rw [mainDecodedState_memory]
  simp only [mainInputWord, hcalldata]
  interval_cases i
  · repeat' first
      | rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
          _ 0 32 224 _ (by omega)]
      | rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
          _ 0 32 192 _ (by omega)]
      | rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
          _ 0 32 160 _ (by omega)]
      | rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
          _ 0 32 128 _ (by omega)]
      | rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
          _ 0 32 96 _ (by omega)]
      | rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
          _ 0 32 64 _ (by omega)]
      | rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
          _ 0 32 32 _ (by omega)]
    exact Challenge.EvmProof.ModexpMemory.readBytes_storeWord_wordFrom _ 0 0 input
  · norm_num
    repeat' first
      | rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
          _ 32 32 224 _ (by omega)]
      | rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
          _ 32 32 192 _ (by omega)]
      | rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
          _ 32 32 160 _ (by omega)]
      | rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
          _ 32 32 128 _ (by omega)]
      | rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
          _ 32 32 96 _ (by omega)]
      | rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
          _ 32 32 64 _ (by omega)]
    exact Challenge.EvmProof.ModexpMemory.readBytes_storeWord_wordFrom _ 32 32 input
  · norm_num
    repeat' first
      | rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
          _ 64 32 224 _ (by omega)]
      | rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
          _ 64 32 192 _ (by omega)]
      | rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
          _ 64 32 160 _ (by omega)]
      | rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
          _ 64 32 128 _ (by omega)]
      | rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
          _ 64 32 96 _ (by omega)]
    exact Challenge.EvmProof.ModexpMemory.readBytes_storeWord_wordFrom _ 64 64 input
  · norm_num
    repeat' first
      | rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
          _ 96 32 224 _ (by omega)]
      | rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
          _ 96 32 192 _ (by omega)]
      | rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
          _ 96 32 160 _ (by omega)]
      | rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
          _ 96 32 128 _ (by omega)]
    exact Challenge.EvmProof.ModexpMemory.readBytes_storeWord_wordFrom _ 96 96 input
  · norm_num
    repeat' first
      | rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
          _ 128 32 224 _ (by omega)]
      | rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
          _ 128 32 192 _ (by omega)]
      | rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
          _ 128 32 160 _ (by omega)]
    exact Challenge.EvmProof.ModexpMemory.readBytes_storeWord_wordFrom _ 128 128 input
  · norm_num
    repeat' first
      | rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
          _ 160 32 224 _ (by omega)]
      | rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
          _ 160 32 192 _ (by omega)]
    exact Challenge.EvmProof.ModexpMemory.readBytes_storeWord_wordFrom _ 160 160 input
  · norm_num
    rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
      _ 192 32 224 _ (by omega)]
    exact Challenge.EvmProof.ModexpMemory.readBytes_storeWord_wordFrom _ 192 192 input
  · norm_num
    exact Challenge.EvmProof.ModexpMemory.readBytes_storeWord_wordFrom _ 224 224 input

/-- Every frozen decoded word is exactly the corresponding padded calldata
word. -/
theorem mainDecodedWord_eq_input (yst : EvmState) (input : ByteArray)
    (hcalldata : yst.env.calldata = input.toList) (i : Nat) (hi : i < 8) :
    mainDecodedWord yst (32 * i) = wordFrom input.toList (32 * i) := by
  unfold mainDecodedWord
  exact loadWord_eq_wordFrom_of_readBytes _ _ _ input
    (mainDecodedState_read yst input hcalldata i hi)

/-- The source's two-word representation of one EIP field window. -/
def sourceField (yst : EvmState) (offset : Nat) : Fp.Limbs :=
  onCurveX (mainDecodedWord yst offset) (mainDecodedWord yst (offset + 32))

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
    Challenge.EvmProof.Bytes.readPadded_toList,
    bytesNat_eq_zero_iff]
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
            256 ^ 16 := by
        exact Nat.le_mul_of_pos_left _ (Nat.zero_lt_of_ne_zero hne)
      omega
    exact hprefix

private theorem word_shift_128_eq_zero_iff (word : U256) :
    word >>> 128 = 0 ↔ word.toNat < 2 ^ 128 := by
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

/-- The source's four-way high-half OR is zero exactly when all four EIP
field padding windows are canonical zero padding. -/
theorem mainPaddingValue_eq_zero_iff_codec (yst : EvmState)
    (input : ByteArray) (hcalldata : yst.env.calldata = input.toList)
    (hsize : input.size = 256) :
    mainPaddingValue yst = 0 ↔
      Codec.PaddingZero input 0 ∧ Codec.PaddingZero input 64 ∧
      Codec.PaddingZero input 128 ∧ Codec.PaddingZero input 192 := by
  rw [mainPaddingValue_eq_zero_iff]
  have h0 := mainDecodedWord_eq_input yst input hcalldata 0 (by omega)
  have h64 := mainDecodedWord_eq_input yst input hcalldata 2 (by omega)
  have h128 := mainDecodedWord_eq_input yst input hcalldata 4 (by omega)
  have h192 := mainDecodedWord_eq_input yst input hcalldata 6 (by omega)
  norm_num at h0 h64 h128 h192
  rw [h0, h64, h128, h192]
  repeat rw [word_shift_128_eq_zero_iff]
  rw [← paddingZero_iff_inputWord_lt input 0 (by omega),
    ← paddingZero_iff_inputWord_lt input 64 (by omega),
    ← paddingZero_iff_inputWord_lt input 128 (by omega),
    ← paddingZero_iff_inputWord_lt input 192 (by omega)]

private theorem fpWindowValue_eq_sourceField (yst : EvmState)
    (input : ByteArray) (hcalldata : yst.env.calldata = input.toList)
    (i : Nat) (hi : i < 4) (hsize : 64 * i + 64 ≤ input.size)
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
      unfold sourceField Fp.value onCurveX Challenge.EvmProof.Limbs.radix
      rw [hwordHi', hwordLo', YulEvmCompiler.conv_toNat,
        YulEvmCompiler.conv_toNat, inputWord_toNat, inputWord_toNat]
      norm_num [pow_mul]
      ring

/-- Successful EIP field decoding agrees with the exact two source words. -/
theorem decodeFp_eq_some_sourceField (yst : EvmState) (input : ByteArray)
    (hcalldata : yst.env.calldata = input.toList) (i : Nat) (hi : i < 4)
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
      unfold sourceField onCurveX
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
    (hcalldata : yst.env.calldata = input.toList) (i : Nat) (hi : i < 4)
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

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
