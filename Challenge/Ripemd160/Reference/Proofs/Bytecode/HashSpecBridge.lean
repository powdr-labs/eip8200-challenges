import Challenge.Ripemd160.Reference.Proofs.Bytecode.SpecBridge
set_option warningAsError true
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
/-!
# One-pass padded-message bridge to `Crypto.Ripemd160.hash`
-/

namespace Challenge.Ripemd160.Reference.Proofs.Bytecode.HashSpecBridge

open EvmSemantics.Crypto

private theorem foldl_congr_on {α β : Type} (xs : List α)
    (left right : β → α → β) (init : β)
    (h : ∀ acc x, x ∈ xs → left acc x = right acc x) :
    xs.foldl left init = xs.foldl right init := by
  induction xs generalizing init with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [h init x (by simp)]
      apply ih
      intro acc y hy
      exact h acc y (by simp [hy])

private theorem id_run_map {α β : Type} (x : Id α) (f : α → β) :
    (do let value ← x; pure (f value)).run = f x.run := rfl

theorem readLE32_eq_of_byte (left right : ByteArray)
    (leftOff rightOff : Nat)
    (hbyte : ∀ i < 4,
      (if h : leftOff + i < left.size then left[leftOff + i].toUInt32 else 0) =
        (if h : rightOff + i < right.size then right[rightOff + i].toUInt32 else 0)) :
    Ripemd160.readLE32 left leftOff = Ripemd160.readLE32 right rightOff := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure]
  apply foldl_congr_on
  intro w i hi
  have hlt : i < 4 := by simpa using hi
  rw [hbyte i hlt]

theorem compressBlock_eq_of_readLE32 (h : Array UInt32)
    (left right : ByteArray) (leftOff rightOff : Nat)
    (hread : ∀ i < 16,
      Ripemd160.readLE32 left (leftOff + i * 4) =
        Ripemd160.readLE32 right (rightOff + i * 4)) :
    Ripemd160.compressBlock h left leftOff =
      Ripemd160.compressBlock h right rightOff := by
  have hwords :
      (List.range' 0 16).foldl
          (fun words i => words.set! i
            (Ripemd160.readLE32 left (leftOff + i * 4)))
          (Array.replicate 16 0) =
        (List.range' 0 16).foldl
          (fun words i => words.set! i
            (Ripemd160.readLE32 right (rightOff + i * 4)))
          (Array.replicate 16 0) := by
    apply foldl_congr_on
    intro words i hi
    rw [hread i]
    simpa using hi
  unfold Ripemd160.compressBlock
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl]
  rw [hwords]

theorem compressBlock_append_left (h : Array UInt32)
    (input suffix : ByteArray) (off : Nat) (hblock : off + 64 ≤ input.size) :
    Ripemd160.compressBlock h (input ++ suffix) off =
      Ripemd160.compressBlock h input off := by
  apply compressBlock_eq_of_readLE32
  intro i hi
  apply readLE32_eq_of_byte
  intro j hj
  have hindex : off + i * 4 + j < input.size := by omega
  simp only [ByteArray.size_append]
  rw [dif_pos (by omega), dif_pos hindex]
  exact congrArg UInt8.toUInt32 (ByteArray.get_append_left hindex)

theorem compressBlock_append_right (h : Array UInt32)
    (pre tail : ByteArray) (off : Nat) :
    Ripemd160.compressBlock h (pre ++ tail) (pre.size + off) =
      Ripemd160.compressBlock h tail off := by
  apply compressBlock_eq_of_readLE32
  intro i hi
  apply readLE32_eq_of_byte
  intro j hj
  simp only [ByteArray.size_append]
  by_cases hindex : off + i * 4 + j < tail.size
  · rw [dif_pos (by omega), dif_pos hindex]
    have hget := ByteArray.get_append_right
      (a := pre) (b := tail) (i := pre.size + off + i * 4 + j)
      (by omega) (by simp; omega)
    have hget32 := congrArg UInt8.toUInt32 hget
    simpa only [Nat.add_assoc, Nat.add_sub_cancel_left] using hget32
  · rw [dif_neg (by omega), dif_neg hindex]

theorem absorbBlocks_append_prefix (h : Array UInt32)
    (pre tail : ByteArray) (count : Nat) (hsize : count * 64 ≤ pre.size) :
    SpecBridge.absorbBlocks h (pre ++ tail) 0 count =
      SpecBridge.absorbBlocks h pre 0 count := by
  induction count generalizing h with
  | zero => simp
  | succ count ih =>
      rw [SpecBridge.absorbBlocks_succ, SpecBridge.absorbBlocks_succ,
        ih h (by omega)]
      apply compressBlock_append_left
      omega

theorem absorbBlocks_append (h : Array UInt32)
    (pre tail : ByteArray) (preBlocks tailBlocks : Nat)
    (hsize : pre.size = preBlocks * 64) :
    SpecBridge.absorbBlocks h (pre ++ tail) 0 (preBlocks + tailBlocks) =
      SpecBridge.absorbBlocks
        (SpecBridge.absorbBlocks h pre 0 preBlocks) tail 0 tailBlocks := by
  induction tailBlocks with
  | zero =>
      simp only [Nat.add_zero, SpecBridge.absorbBlocks_zero]
      exact absorbBlocks_append_prefix h pre tail preBlocks hsize.ge
  | succ tailBlocks ih =>
      rw [Nat.add_succ, SpecBridge.absorbBlocks_succ,
        SpecBridge.absorbBlocks_succ, ih]
      have hoff : (preBlocks + tailBlocks) * 64 =
          pre.size + tailBlocks * 64 := by omega
      rw [hoff]
      simpa only [Nat.zero_add] using compressBlock_append_right
        (SpecBridge.absorbBlocks
          (SpecBridge.absorbBlocks h pre 0 preBlocks) tail 0 tailBlocks)
        pre tail (tailBlocks * 64)

def copyRange (input : ByteArray) (start count : Nat) : ByteArray :=
  (List.range' 0 count).foldl
    (fun output i => output.push input[start + i]!) ByteArray.empty

@[simp] theorem copyRange_size (input : ByteArray) (start count : Nat) :
    (copyRange input start count).size = count := by
  induction count with
  | zero => simp [copyRange]
  | succ count ih =>
      rw [copyRange, List.range'_concat, List.foldl_append]
      simp only [Nat.one_mul, Nat.zero_add, List.foldl_cons, List.foldl_nil,
        ByteArray.size_push]
      simpa [copyRange] using congrArg (fun b : ByteArray => b.size) rfl |>.trans ih

theorem copyRange_getElem (input : ByteArray) (start count i : Nat)
    (hi : i < count) :
    (copyRange input start count)[i]! = input[start + i]! := by
  induction count with
  | zero => omega
  | succ count ih =>
      change getElem! ((List.range' 0 (count + 1)).foldl
        (fun output j => output.push input[start + j]!) ByteArray.empty) i = _
      rw [List.range'_concat, List.foldl_append]
      simp only [Nat.one_mul, Nat.zero_add, List.foldl_cons, List.foldl_nil]
      let previous := (List.range' 0 count).foldl
        (fun output j => output.push input[start + j]!) ByteArray.empty
      have hprevious : previous.size = count := by
        simpa [previous, copyRange] using copyRange_size input start count
      change (previous.push input[start + count]!)[i]! = _
      by_cases hlt : i < count
      · rw [getElem!_pos _ i (by simp [hprevious]; omega),
          ByteArray.get_push_lt previous input[start + count]! i
            (by simpa [hprevious] using hlt),
          ← getElem!_pos previous i (by simpa [hprevious] using hlt)]
        simpa [previous, copyRange] using ih hlt
      · have hieq : i = count := by omega
        subst i
        rw [getElem!_pos _ count (by simp [hprevious])]
        convert ByteArray.get_push_eq previous input[start + count]! using 1
        exact getElem_congr_idx hprevious.symm

theorem copyRange_eq_extract (input : ByteArray) (start count : Nat)
    (hbound : start + count ≤ input.size) :
    copyRange input start count = input.extract start (start + count) := by
  apply ByteArray.ext_getElem
  · simp [copyRange_size, ByteArray.size_extract]
    omega
  · intro i hleft hright
    have hi : i < count := by simpa using hleft
    rw [← getElem!_pos _ i hleft, copyRange_getElem input start count i hi,
      ByteArray.getElem_extract, getElem!_pos input (start + i) (by omega)]

def padZeros (tail : ByteArray) : ByteArray :=
  Id.run (Lean.Loop.forIn (m := Id) {} tail fun _ tail =>
    if tail.size % 64 ≠ 56 then pure (.yield (tail.push 0))
    else pure (.done tail))

theorem padZeros_eq (tail : ByteArray) :
    padZeros tail =
      if tail.size % 64 ≠ 56 then padZeros (tail.push 0) else tail := by
  unfold padZeros
  rw [Lean.Loop.forIn_eq_of_monadTail]
  split <;> rfl

def pushZeros : ByteArray → Nat → ByteArray
  | tail, 0 => tail
  | tail, count + 1 => pushZeros (tail.push 0) count

@[simp] theorem pushZeros_zero (tail : ByteArray) : pushZeros tail 0 = tail := rfl

theorem pushZeros_succ (tail : ByteArray) (count : Nat) :
    pushZeros tail (count + 1) = pushZeros (tail.push 0) count := rfl

@[simp] theorem pushZeros_size (tail : ByteArray) (count : Nat) :
    (pushZeros tail count).size = tail.size + count := by
  induction count generalizing tail with
  | zero => simp
  | succ count ih => rw [pushZeros_succ, ih, ByteArray.size_push]; omega

theorem padZeros_eq_pushZeros (tail : ByteArray) (count : Nat)
    (hfinal : (tail.size + count) % 64 = 56)
    (hbefore : ∀ i < count, (tail.size + i) % 64 ≠ 56) :
    padZeros tail = pushZeros tail count := by
  induction count generalizing tail with
  | zero =>
      rw [padZeros_eq, if_neg]
      · rfl
      · simpa using hfinal
  | succ count ih =>
      have hzero : tail.size % 64 ≠ 56 := by
        simpa using hbefore 0 (by omega)
      rw [padZeros_eq, if_pos hzero, pushZeros_succ]
      apply ih
      · simpa only [ByteArray.size_push, Nat.add_assoc, Nat.add_comm count 1]
          using hfinal
      · intro i hi
        simpa only [ByteArray.size_push, Nat.add_assoc, Nat.add_comm 1 i]
          using hbefore (i + 1) (by omega)

theorem pushZeros_eq_append (tail : ByteArray) (count : Nat) :
    pushZeros tail count =
      tail ++ ByteArray.mk (Array.replicate count 0) := by
  induction count generalizing tail with
  | zero => apply ByteArray.ext; simp
  | succ count ih =>
      rw [pushZeros_succ, ih, Array.replicate_succ']
      apply ByteArray.ext
      simp

theorem zeroCount_eq (n : Nat) :
    Padding.zeroCount n =
      if n % 64 < 56 then 55 - n % 64 else 119 - n % 64 := by
  have hn := Nat.div_add_mod' n 64
  have hr := Nat.mod_lt n (by omega : 0 < 64)
  have hp := Nat.div_add_mod' (n + 72) 64
  have hpr := Nat.mod_lt (n + 72) (by omega : 0 < 64)
  unfold Padding.zeroCount Padding.paddedLength
  split <;> rename_i hrem <;> omega

theorem remainder_eq_mod (n : Nat) :
    n - n / 64 * 64 = n % 64 := by
  have := Nat.div_add_mod' n 64
  omega

theorem canonical_padZeros (input : ByteArray) :
    padZeros ((copyRange input (input.size / 64 * 64)
      (input.size - input.size / 64 * 64)).push 0x80) =
      (copyRange input (input.size / 64 * 64)
        (input.size - input.size / 64 * 64)).push 0x80 ++
        Padding.zeroBytes input.size := by
  let rem := input.size % 64
  have hrem : rem < 64 := Nat.mod_lt _ (by omega)
  have hcopy :
      (copyRange input (input.size / 64 * 64)
        (input.size - input.size / 64 * 64)).size = rem := by
    simp [rem, remainder_eq_mod]
  rw [Padding.zeroBytes, ← pushZeros_eq_append]
  apply padZeros_eq_pushZeros
  · rw [ByteArray.size_push, hcopy, zeroCount_eq]
    dsimp only [rem]
    split <;> rename_i hlt
    · have hle : rem ≤ 55 := by omega
      change (rem + 1 + (55 - rem)) % 64 = 56
      have : rem + 1 + (55 - rem) = 56 := by omega
      rw [this]
    · have hle : rem ≤ 119 := by omega
      change (rem + 1 + (119 - rem)) % 64 = 56
      have : rem + 1 + (119 - rem) = 120 := by omega
      rw [this]
  · intro i hi
    rw [zeroCount_eq] at hi
    rw [ByteArray.size_push, hcopy]
    dsimp only [rem] at hi ⊢
    by_cases hlt : rem < 56
    · rw [if_pos hlt] at hi
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    · rw [if_neg hlt] at hi
      by_cases hs : rem + 1 + i < 64
      · rw [Nat.mod_eq_of_lt hs]
        omega
      · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
        omega

def lengthLoop (n : Nat) : ByteArray :=
  (List.range' 0 8).foldl
    (fun output i => output.push ((n >>> (8 * i)) &&& 0xff).toUInt8)
    ByteArray.empty

@[simp] theorem lengthLoop_size (n : Nat) : (lengthLoop n).size = 8 := by rfl

theorem lengthLoop_getElem (n i : Nat) (hi : i < 8) :
    (lengthLoop n)[i] = ((n >>> (8 * i)) &&& 0xff).toUInt8 := by
  interval_cases i <;> rfl

private theorem lengthDigit_eq (n i : Nat) (hi : i < 8) :
    ((n >>> (8 * i)) &&& 0xff).toUInt8 =
      UInt8.ofNat (n / 256 ^ i % 256) := by
  interval_cases i <;>
    rw [show (255 : Nat) = 2 ^ 8 - 1 by decide,
      Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow] <;>
    norm_num [pow_mul]

theorem lengthLoop_eq_lengthBytes (input : ByteArray) :
    lengthLoop (input.size * 8) = Padding.lengthBytes input := by
  apply ByteArray.ext_getElem
  · simp
  · intro i hleft hright
    have hi : i < 8 := by simpa using hleft
    calc
      (lengthLoop (input.size * 8))[i] =
          (((input.size * 8) >>> (8 * i)) &&& 0xff).toUInt8 :=
        lengthLoop_getElem _ _ hi
      _ = UInt8.ofNat ((input.size * 8) / 256 ^ i % 256) :=
        lengthDigit_eq _ _ hi
      _ = (Padding.lengthBytes input)[i] := by
        convert (Padding.lengthByte input i hi).symm using 1
        · congr 2
          rw [show 2 ^ (8 * i) = 256 ^ i by rw [Nat.pow_mul]]
        · congr

def appendLength (tail : ByteArray) (n : Nat) : ByteArray :=
  (List.range' 0 8).foldl
    (fun output i => output.push ((n >>> (8 * i)) &&& 0xff).toUInt8) tail

private theorem foldl_push_append {α : Type} (xs : List α)
    (tail : ByteArray) (f : α → UInt8) :
    xs.foldl (fun output x => output.push (f x)) tail =
      tail ++ xs.foldl (fun output x => output.push (f x)) ByteArray.empty := by
  induction xs generalizing tail with
  | nil => apply ByteArray.ext; simp
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [ih (tail.push (f x)), ih (ByteArray.empty.push (f x))]
      apply ByteArray.ext
      simp

theorem appendLength_eq (tail : ByteArray) (n : Nat) :
    appendLength tail n = tail ++ lengthLoop n := by
  exact foldl_push_append (List.range' 0 8) tail
    (fun i => ((n >>> (8 * i)) &&& 0xff).toUInt8)

def loopTail (input : ByteArray) : ByteArray :=
  Id.run (Lean.Loop.forIn (m := Id) {}
    ((copyRange input (input.size / 64 * 64)
      (input.size - input.size / 64 * 64)).push 0x80) fun _ tail =>
      if tail.size % 64 ≠ 56 then pure (.yield (tail.push 0))
      else pure (.done tail))

theorem loopTail_eq_padZeros (input : ByteArray) :
    loopTail input = padZeros ((copyRange input (input.size / 64 * 64)
      (input.size - input.size / 64 * 64)).push 0x80) := rfl

def canonicalTail (input : ByteArray) : ByteArray :=
  appendLength (loopTail input) (input.size * 8)

theorem canonicalTail_eq (input : ByteArray) :
    canonicalTail input =
      input.extract (input.size / 64 * 64) input.size ++
        ByteArray.mk #[0x80] ++ Padding.zeroBytes input.size ++
          Padding.lengthBytes input := by
  have hbase : input.size / 64 * 64 ≤ input.size := by
    simpa [Nat.mul_comm] using Nat.mul_div_le input.size 64
  rw [canonicalTail, loopTail_eq_padZeros, appendLength_eq,
    canonical_padZeros, lengthLoop_eq_lengthBytes,
    copyRange_eq_extract input (input.size / 64 * 64)
      (input.size - input.size / 64 * 64) (by omega)]
  rw [Nat.add_sub_of_le hbase]
  apply ByteArray.ext
  simp

def fullPrefix (input : ByteArray) : ByteArray :=
  input.extract 0 (input.size / 64 * 64)

@[simp] theorem fullPrefix_size (input : ByteArray) :
    (fullPrefix input).size = input.size / 64 * 64 := by
  unfold fullPrefix
  have hbase : input.size / 64 * 64 ≤ input.size := by
    simpa [Nat.mul_comm] using Nat.mul_div_le input.size 64
  rw [ByteArray.size_extract, Nat.min_eq_left hbase]
  simp

theorem paddedMessage_eq_prefix_tail (input : ByteArray) :
    Padding.paddedMessage input = fullPrefix input ++ canonicalTail input := by
  rw [canonicalTail_eq]
  unfold Padding.paddedMessage fullPrefix
  have hbase : input.size / 64 * 64 ≤ input.size := by
    simpa [Nat.mul_comm] using Nat.mul_div_le input.size 64
  have hsplit : input = input.extract 0 (input.size / 64 * 64) ++
      input.extract (input.size / 64 * 64) input.size := by
    rw [← ByteArray.extract_eq_extract_append_extract
      (input.size / 64 * 64) (by omega) hbase,
      ByteArray.extract_zero_size]
  simp only [ByteArray.append_assoc]
  let suffix := ByteArray.mk #[0x80] ++
    (Padding.zeroBytes input.size ++ Padding.lengthBytes input)
  change input ++ suffix =
    input.extract 0 (input.size / 64 * 64) ++
      (input.extract (input.size / 64 * 64) input.size ++ suffix)
  calc
    input ++ suffix =
        (input.extract 0 (input.size / 64 * 64) ++
          input.extract (input.size / 64 * 64) input.size) ++ suffix :=
      congrArg (fun bytes => bytes ++ suffix) hsplit
    _ = _ := ByteArray.append_assoc

theorem paddedBlockCount_eq (input : ByteArray) :
    Padding.paddedLength input.size / 64 =
      input.size / 64 + (canonicalTail input).size / 64 := by
  have hsizes := congrArg ByteArray.size (paddedMessage_eq_prefix_tail input)
  simp only [Padding.paddedMessage_size, ByteArray.size_append,
    fullPrefix_size] at hsizes
  rw [hsizes]
  simpa [Nat.mul_comm] using
    Nat.add_div_of_dvd_right (dvd_mul_right 64 (input.size / 64))

theorem hash_eq_two_phase (input : ByteArray) :
    Ripemd160.hash input =
      SpecBridge.emitDigest
        (SpecBridge.absorbBlocks
          (SpecBridge.absorbBlocks Ripemd160.H0 input 0 (input.size / 64))
          (canonicalTail input) 0 ((canonicalTail input).size / 64)) := by
  unfold Ripemd160.hash
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl]
  rw [id_run_map]
  unfold SpecBridge.emitDigest SpecBridge.absorbBlocks canonicalTail loopTail
    appendLength copyRange
  simp only [← List.range_eq_range', Nat.zero_add]
  rfl

theorem absorbBlocks_fullPrefix_eq_input (h : Array UInt32)
    (input : ByteArray) :
    SpecBridge.absorbBlocks h (fullPrefix input) 0 (input.size / 64) =
      SpecBridge.absorbBlocks h input 0 (input.size / 64) := by
  have hsplit : input = fullPrefix input ++
      input.extract (input.size / 64 * 64) input.size := by
    unfold fullPrefix
    have hbase : input.size / 64 * 64 ≤ input.size := by
      simpa [Nat.mul_comm] using Nat.mul_div_le input.size 64
    rw [← ByteArray.extract_eq_extract_append_extract
      (input.size / 64 * 64) (by omega) hbase,
      ByteArray.extract_zero_size]
  have happ := absorbBlocks_append_prefix h (fullPrefix input)
    (input.extract (input.size / 64 * 64) input.size) (input.size / 64)
    (by simp)
  rw [← hsplit] at happ
  exact happ.symm

/-- Absorbing the direct bytecode's one-pass padded image and serializing the
five words little-endian is exactly the RIPEMD-160 function in the challenge
specification. -/
theorem paddedHash_eq_hash (input : ByteArray) :
    SpecBridge.paddedHash input = Ripemd160.hash input := by
  rw [hash_eq_two_phase]
  unfold SpecBridge.paddedHash
  rw [paddedMessage_eq_prefix_tail, paddedBlockCount_eq,
    absorbBlocks_append Ripemd160.H0 (fullPrefix input) (canonicalTail input)
      (input.size / 64) ((canonicalTail input).size / 64)
      (fullPrefix_size input),
    absorbBlocks_fullPrefix_eq_input]

end Challenge.Ripemd160.Reference.Proofs.Bytecode.HashSpecBridge
