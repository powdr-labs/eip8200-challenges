import Challenge.EvmProof.Bytecode
import EvmSemantics.Machine.MachineState
import Lean.Elab.Tactic.Omega
import YulEvmCompiler.Instr
set_option warningAsError true
/-!
# Pointwise EVM memory reasoning

Reusable bridges from the executable `ByteArray` memory helpers to list and
pointwise views suitable for functional bytecode proofs.
-/

namespace Challenge.EvmProof.Memory

open EvmSemantics

theorem getD0_eq_getElem! (c : ByteArray) (i : Nat) :
    c[i]?.getD 0 = c[i]! := by
  rw [getElem!_def]
  cases c[i]? <;> rfl

theorem getD0_eq_getElem (c : ByteArray) (i : Nat) (h : i < c.size) :
    c[i]?.getD 0 = c[i] := by
  rw [getD0_eq_getElem!, getElem!_pos c i h]

theorem getElem?_getD_eq_zero_of_size_le (bs : ByteArray) (i : Nat)
    (h : bs.size ≤ i) : bs[i]?.getD 0 = 0 := by
  change (bs.data[i]?).getD 0 = 0
  rw [Array.getElem?_eq_none]
  · rfl
  · exact h

theorem getElem?_getD_append (a b : ByteArray) (i : Nat) :
    (a ++ b)[i]?.getD 0 =
      if i < a.size then a[i]?.getD 0 else b[i - a.size]?.getD 0 := by
  rw [getD0_eq_getElem!, getD0_eq_getElem!]
  by_cases ha : i < a.size
  · rw [if_pos ha, getElem!_pos (a ++ b) i (by
        rw [ByteArray.size_append]; omega), getElem!_pos a i ha]
    exact ByteArray.getElem_append_left ha
  · rw [if_neg ha]
    by_cases hb : i - a.size < b.size
    · have hai : a.size ≤ i := by omega
      rw [getD0_eq_getElem!]
      rw [getElem!_pos (a ++ b) i (by rw [ByteArray.size_append]; omega),
        getElem!_pos b (i - a.size) hb]
      exact ByteArray.getElem_append_right hai
    · rw [getD0_eq_getElem!,
        getElem!_neg (a ++ b) i (by rw [ByteArray.size_append]; omega),
        getElem!_neg b (i - a.size) hb]

private def lowBytes (n : Nat) : Nat → List UInt8
  | 0 => []
  | w + 1 => UInt8.ofNat (n % 256) :: lowBytes (n / 256) w

@[simp] private theorem length_lowBytes (n width : Nat) :
    (lowBytes n width).length = width := by
  induction width generalizing n with
  | zero => rfl
  | succ width ih => simp [lowBytes, ih]

private def pullBytes : Nat → Array UInt8 → Nat → MProd Nat (Array UInt8)
  | n, acc, 0 => ⟨n, acc⟩
  | n, acc, w + 1 => pullBytes (n / 256) (acc.push (UInt8.ofNat (n % 256))) w

private theorem foldl_pullBytes (xs : List Nat) (n : Nat) (acc : Array UInt8) :
    xs.foldl
        (fun (b : MProd Nat (Array UInt8)) _ =>
          ⟨b.fst / 256, b.snd.push (UInt8.ofNat (b.fst % 256))⟩)
        ⟨n, acc⟩ =
      pullBytes n acc xs.length := by
  induction xs generalizing n acc with
  | nil => rfl
  | cons _ xs ih =>
      simp only [List.foldl_cons, List.length_cons, pullBytes]
      exact ih _ _

private theorem pullBytes_eq (n : Nat) (acc : Array UInt8) (w : Nat) :
    (pullBytes n acc w).snd = acc ++ (lowBytes n w).toArray := by
  induction w generalizing n acc with
  | zero => simp [pullBytes, lowBytes]
  | succ w ih =>
      rw [pullBytes, ih]
      simp [lowBytes]

private theorem map_reverse_get (l : List UInt8) :
    (List.range' 0 l.length).map (fun i => l[l.length - 1 - i]!) =
      l.reverse := by
  apply List.ext_get
  · simp
  · intro i _ hi
    simp [List.getElem_reverse]
    have hi' : i < l.length := by simpa using hi
    rw [List.getElem?_eq_getElem (by omega)]
    rfl

private theorem reverse_lowBytes (n width : Nat) :
    (lowBytes n width).reverse = YulEvmCompiler.natToBE n width := by
  induction width generalizing n with
  | zero => rfl
  | succ width ih =>
      simp [lowBytes, YulEvmCompiler.natToBE, ih]

theorem natToBytesPadded_eq_natToBE (n width : Nat) :
    Data.Bytes.natToBytesPadded n width =
      ByteArray.mk (YulEvmCompiler.natToBE n width).toArray := by
  have hpull := foldl_pullBytes (List.range' 0 width) n #[]
  have hsnd := congrArg MProd.snd hpull
  rw [pullBytes_eq] at hsnd
  simp at hsnd
  apply ByteArray.ext
  simp [Data.Bytes.natToBytesPadded]
  rw [hsnd]
  calc
    _ = (lowBytes n width).reverse := by
      simpa only [length_lowBytes, List.getElem!_toArray] using
        map_reverse_get (lowBytes n width)
    _ = _ := reverse_lowBytes n width

private theorem foldl_natToBE (width : Nat) :
    ∀ n acc : Nat, n < 256 ^ width →
      (YulEvmCompiler.natToBE n width).foldl
          (fun acc b => acc * 256 + b.toNat) acc =
        acc * 256 ^ width + n := by
  induction width with
  | zero =>
      intro n acc h
      have hn : n = 0 := by omega
      subst n
      simp [YulEvmCompiler.natToBE]
  | succ width ih =>
      intro n acc h
      rw [YulEvmCompiler.natToBE, List.foldl_append]
      have hdiv : n / 256 < 256 ^ width := by
        rw [Nat.div_lt_iff_lt_mul (by omega)]
        calc
          n < 256 ^ (width + 1) := h
          _ = 256 ^ width * 256 := by rw [Nat.pow_succ]
      rw [ih (n / 256) acc hdiv]
      have hmod : (UInt8.ofNat (n % 256)).toNat = n % 256 := by simp
      simp only [List.foldl_cons, List.foldl_nil, hmod]
      have hsplit := Nat.div_add_mod n 256
      rw [Nat.pow_succ]
      rw [Nat.add_mul, ← Nat.mul_assoc]
      omega

theorem bytesToBigEndianNat_natToBytesPadded (n width : Nat)
    (h : n < 256 ^ width) :
    Data.Bytes.bytesToBigEndianNat (Data.Bytes.natToBytesPadded n width) = n := by
  rw [natToBytesPadded_eq_natToBE]
  unfold Data.Bytes.bytesToBigEndianNat
  rw [Challenge.EvmProof.Bytecode.toList_eq_data]
  change (YulEvmCompiler.natToBE n width).foldl
    (fun acc b => acc * 256 + b.toNat) 0 = n
  rw [foldl_natToBE width n 0 h]
  simp

theorem readPadded_toList (bs : ByteArray) (start n : Nat) :
    (MachineState.readPadded bs start n).toList =
      (bs.data.toList.drop (min start bs.size)).take
          (min (bs.size - min start bs.size) n) ++
        List.replicate (n - min (bs.size - min start bs.size) n) 0 := by
  simp [MachineState.readPadded, Challenge.EvmProof.Bytecode.toList_eq_data,
    ByteArray.data_extract, Array.toList_extract, List.extract_eq_take_drop]

theorem readPadded_zero_size (bs : ByteArray) :
    MachineState.readPadded bs 0 bs.size = bs := by
  unfold MachineState.readPadded
  simp only [Nat.min_eq_left (Nat.zero_le _), Nat.sub_zero, Nat.min_self,
    Nat.add_comm 0, Nat.sub_self, Array.replicate_zero]
  apply ByteArray.ext
  simp

/-- Pointwise form of the EVM's zero-padded byte read. -/
theorem readPadded_getElem?_getD (bs : ByteArray) (start n i : Nat) :
    (MachineState.readPadded bs start n)[i]?.getD 0 =
      if i < n then bs[start + i]?.getD 0 else 0 := by
  unfold MachineState.readPadded
  let start' := min start bs.size
  let take := min (bs.size - start') n
  change ((bs.extract start' (start' + take) ++
    ByteArray.mk (Array.replicate (n - take) 0))[i]?.getD 0) = _
  have hstartLe : start' ≤ bs.size := Nat.min_le_right _ _
  have htakeLe : take ≤ bs.size - start' := Nat.min_le_left _ _
  have htakeN : take ≤ n := Nat.min_le_right _ _
  have hstop : start' + take ≤ bs.size := by omega
  have hextractSize : (bs.extract start' (start' + take)).size = take := by
    rw [ByteArray.size_extract, Nat.min_eq_left hstop]
    omega
  rw [getElem?_getD_append, hextractSize]
  by_cases hi : i < n
  · rw [if_pos hi]
    by_cases hitake : i < take
    · rw [if_pos hitake]
      have hsle : start ≤ bs.size := by
        by_cases hsle : start ≤ bs.size
        · exact hsle
        · have hge : bs.size ≤ start := by omega
          have hstartEq : start' = bs.size := by simp [start', hge]
          rw [hstartEq] at htakeLe
          simp at htakeLe
          omega
      have hstartEq : start' = start := by simp [start', hsle]
      simp only [hstartEq] at hstop hextractSize ⊢
      have hextract : i < (bs.extract start (start + take)).size := by
        simpa [hextractSize] using hitake
      rw [getD0_eq_getElem!]
      rw [getElem!_pos _ i hextract]
      rw [ByteArray.getElem_extract]
      rw [getD0_eq_getElem!]
      rw [getElem!_pos bs (start + i) (by omega)]
    · rw [if_neg hitake]
      have hpad : i - take < (ByteArray.mk (Array.replicate (n - take) 0)).size := by
        change i - take < (Array.replicate (n - take) 0).size
        rw [Array.size_replicate]
        omega
      rw [getD0_eq_getElem!]
      rw [getElem!_pos _ (i - take) hpad]
      change (Array.replicate (n - take) 0)[i - take] = _
      rw [Array.getElem_replicate]
      apply (getElem?_getD_eq_zero_of_size_le bs (start + i) ?_).symm
      by_cases hsle : start ≤ bs.size
      · have hstartEq : start' = start := by simp [start', hsle]
        dsimp only [take] at hitake
        rw [hstartEq] at hitake
        omega
      · omega
  · rw [if_neg hi]
    rw [if_neg (by omega)]
    apply getElem?_getD_eq_zero_of_size_le
    change (Array.replicate (n - take) 0).size ≤ i - take
    rw [Array.size_replicate]
    omega

@[simp] theorem readPadded_size (bs : ByteArray) (start n : Nat) :
    (MachineState.readPadded bs start n).size = n := by
  let start' := min start bs.size
  let take := min (bs.size - start') n
  have hstop : start' + take ≤ bs.size := by
    dsimp only [start', take]
    omega
  unfold MachineState.readPadded
  change (bs.extract start' (start' + take) ++
    ByteArray.mk (Array.replicate (n - take) 0)).size = n
  rw [ByteArray.size_append, ByteArray.size_extract, Nat.min_eq_left hstop]
  change start' + take - start' + (Array.replicate (n - take) 0).size = n
  rw [Array.size_replicate]
  omega

/-- A zero-padded read depends only on the addressed byte window. -/
theorem readPadded_congr (a b : ByteArray) (start n : Nat)
    (h : ∀ i, i < n → a[start + i]?.getD 0 = b[start + i]?.getD 0) :
    MachineState.readPadded a start n = MachineState.readPadded b start n := by
  apply ByteArray.ext_getElem
  · simp
  · intro i hia hib
    rw [← getD0_eq_getElem _ _ hia, ← getD0_eq_getElem _ _ hib,
      readPadded_getElem?_getD, readPadded_getElem?_getD]
    have hi : i < n := by simpa using hia
    rw [if_pos hi, if_pos hi]
    exact h i hi

/-- Writing outside a read window leaves the read unchanged. -/
theorem readPadded_writeBytes_disjoint (bs bytes : ByteArray)
    (readStart readSize writeStart : Nat)
    (hdisjoint : readStart + readSize ≤ writeStart ∨
      writeStart + bytes.size ≤ readStart) :
    MachineState.readPadded (MachineState.writeBytes bs bytes writeStart)
        readStart readSize =
      MachineState.readPadded bs readStart readSize := by
  apply readPadded_congr
  intro i hi
  rw [MachineState.writeBytes_getElem?_getD]
  rw [if_neg]
  rcases hdisjoint with hbefore | hafter
  · omega
  · omega

theorem readWord_writeBytes_disjoint (bs bytes : ByteArray)
    (readStart writeStart : Nat)
    (hdisjoint : readStart + 32 ≤ writeStart ∨
      writeStart + bytes.size ≤ readStart) :
    MachineState.readWord (MachineState.writeBytes bs bytes writeStart) readStart =
      MachineState.readWord bs readStart := by
  unfold MachineState.readWord
  rw [readPadded_writeBytes_disjoint bs bytes readStart 32 writeStart hdisjoint]

theorem writeBytes_extract_same (bs bytes : ByteArray) (start : Nat) :
    (MachineState.writeBytes bs bytes start).extract start (start + bytes.size) =
      bytes := by
  apply ByteArray.ext
  apply Array.ext
  · rw [ByteArray.data_extract, Array.size_extract]
    change min (start + bytes.size)
      (MachineState.writeBytes bs bytes start).size - start = bytes.size
    rw [MachineState.writeBytes_size]
    split <;> omega
  · intro i hi₁ hi₂
    simp only [ByteArray.data_extract] at hi₁ ⊢
    rw [Array.getElem_extract]
    have hi₂' : i < bytes.size := hi₂
    have h := MachineState.writeBytes_getElem?_getD bs bytes start (start + i)
    rw [if_pos (by omega)] at h
    have hn : bytes.size ≠ 0 := by omega
    have hw : start + i < (MachineState.writeBytes bs bytes start).size := by
      rw [MachineState.writeBytes_size, if_neg hn]
      omega
    rw [Nat.add_sub_cancel_left] at h
    change ((MachineState.writeBytes bs bytes start).data[start + i]?).getD 0 =
      (bytes.data[i]?).getD 0 at h
    have hw' : start + i < (MachineState.writeBytes bs bytes start).data.size := hw
    rw [Array.getElem?_eq_getElem hw', Array.getElem?_eq_getElem hi₂] at h
    simp only [Option.getD_some] at h
    exact h

theorem readPadded_writeBytes_same (bs bytes : ByteArray) (start : Nat) :
    MachineState.readPadded (MachineState.writeBytes bs bytes start)
      start bytes.size = bytes := by
  unfold MachineState.readPadded
  rw [MachineState.writeBytes_size]
  by_cases hz : bytes.size = 0
  · have hb : bytes = ByteArray.empty := by
      apply ByteArray.ext
      apply Array.ext <;> simp [hz]
    subst bytes
    simp [MachineState.writeBytes]
    apply ByteArray.ext
    rfl
  · simp only [hz, if_false]
    have hsize : start ≤ max bs.size (start + bytes.size) := by omega
    have havail : bytes.size ≤ max bs.size (start + bytes.size) - start := by omega
    simp only [Nat.min_eq_left hsize, Nat.min_eq_right havail,
      Nat.sub_self, Array.replicate_zero, writeBytes_extract_same]
    apply ByteArray.ext
    simp

/-- Adjacent memory writes compose into one write of the concatenated bytes.
This is the main bridge from byte-at-a-time EVM loops to a functional byte
array specification. -/
theorem writeBytes_append_adjacent (bs a b : ByteArray) (start : Nat) :
    MachineState.writeBytes (MachineState.writeBytes bs a start) b
        (start + a.size) =
      MachineState.writeBytes bs (a ++ b) start := by
  by_cases ha : a.size = 0
  · have haempty : a = ByteArray.empty := by
      apply ByteArray.ext
      apply Array.ext
      · simpa using ha
      · intro i hi
        simp [ha] at hi
    subst a
    simp [MachineState.writeBytes]
  by_cases hb : b.size = 0
  · have hbempty : b = ByteArray.empty := by
      apply ByteArray.ext
      apply Array.ext
      · simpa using hb
      · intro i hi
        simp [hb] at hi
    subst b
    simp [MachineState.writeBytes]
  apply ByteArray.ext_getElem
  · simp only [MachineState.writeBytes_size, ha, hb, if_false,
      ByteArray.size_append]
    have hab : a.size + b.size ≠ 0 := by omega
    rw [if_neg hab]
    omega
  · intro i hi₁ hi₂
    rw [← getD0_eq_getElem _ _ hi₁, ← getD0_eq_getElem _ _ hi₂]
    rw [MachineState.writeBytes_getElem?_getD,
      MachineState.writeBytes_getElem?_getD,
      MachineState.writeBytes_getElem?_getD]
    simp only [ByteArray.size_append]
    by_cases hbwin : start + a.size ≤ i ∧
        i < start + a.size + b.size
    · rw [if_pos hbwin, if_pos (by omega)]
      rw [getElem?_getD_append, if_neg (by omega)]
      rw [show i - start - a.size = i - (start + a.size) by omega]
    · rw [if_neg hbwin]
      by_cases hawin : start ≤ i ∧ i < start + a.size
      · rw [if_pos hawin, if_pos (by omega)]
        rw [getElem?_getD_append, if_pos (by omega)]
      · rw [if_neg hawin, if_neg (by omega)]

theorem readWord_writeBytes (bs : ByteArray) (start value : Nat) :
    MachineState.readWord
        (MachineState.writeBytes bs (Data.Bytes.natToBytesPadded value 32) start)
        start =
      UInt256.ofNat
        (Data.Bytes.bytesToBigEndianNat (Data.Bytes.natToBytesPadded value 32)) := by
  unfold MachineState.readWord
  have hsize : (Data.Bytes.natToBytesPadded value 32).size = 32 := by
    simp [Data.Bytes.natToBytesPadded, ByteArray.size]
  have hr := readPadded_writeBytes_same bs
    (Data.Bytes.natToBytesPadded value 32) start
  have hr32 : MachineState.readPadded
      (MachineState.writeBytes bs (Data.Bytes.natToBytesPadded value 32) start)
      start 32 = Data.Bytes.natToBytesPadded value 32 := by
    simpa only [hsize] using hr
  rw [hr32]

theorem readWord_writeBytes_of_lt (bs : ByteArray) (start value : Nat)
    (hvalue : value < 256 ^ 32) :
    MachineState.readWord
        (MachineState.writeBytes bs (Data.Bytes.natToBytesPadded value 32) start)
        start = UInt256.ofNat value := by
  rw [readWord_writeBytes, bytesToBigEndianNat_natToBytesPadded value 32 hvalue]

private theorem pow_256_32 : (256 : Nat) ^ 32 = 2 ^ 256 := by
  have h8 : (256 : Nat) = 2 ^ 8 := by decide
  calc
    (256 : Nat) ^ 32 = (2 ^ 8) ^ 32 := by rw [h8]
    _ = 2 ^ (8 * 32) := (Nat.pow_mul 2 8 32).symm
    _ = 2 ^ 256 := by rfl

theorem readWord_writeWord (bs : ByteArray) (start : Nat) (value : UInt256) :
    MachineState.readWord
        (MachineState.writeBytes bs
          (Data.Bytes.natToBytesPadded value.toNat 32) start)
        start = value := by
  rw [readWord_writeBytes_of_lt]
  · cases value with
    | mk value =>
        unfold UInt256.ofNat
        apply congrArg
        apply Fin.ext
        exact Nat.mod_eq_of_lt value.isLt
  · rw [pow_256_32]
    exact value.val.isLt

end Challenge.EvmProof.Memory
