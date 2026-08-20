import Challenge.Ripemd160.Reference.Proofs.Bytecode.DriverTrace
import Challenge.Ripemd160.Reference.Proofs.Bytecode.CompressionTrace
import Challenge.Ripemd160.Reference.Proofs.Bytecode.CompressionFullTrace
import Challenge.Ripemd160.Reference.Proofs.Bytecode.CompressionFunctionalTrace
import Batteries.Tactic.OpenPrivate

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 100000

/-!
# Active-memory endpoint of one RIPEMD-160 compression call

The schedule's last unaligned `MLOAD` is the unique high-water access.  The
remaining compressor accesses are to the fixed scratch area below word 67.
-/

namespace Challenge.Ripemd160.Reference.Proofs.Bytecode.CompressionActiveWords

open Challenge.Ripemd160
open Challenge.EvmProof
open EvmSemantics
open EvmSemantics.EVM
open CompressionTrace
open CompressionRightTrace
open CompressionTailTrace

open private afterLoads xReturnedState afterFirstStores genericAfterThirdStore
  genericReturned from
  Challenge.Ripemd160.Reference.Proofs.Bytecode.RoundTrace

open private leftSelector_lt rightSelector_lt leftStates_tableByte
  rightStates_tableByte from
  Challenge.Ripemd160.Reference.Proofs.Bytecode.CompressionFunctionalTrace

private theorem activeWordsAfter_eq_of_end_le (curr offset size : Nat)
    (hend : offset + size ≤ curr * 32) :
    MachineState.activeWordsAfter curr offset size = curr := by
  unfold MachineState.activeWordsAfter
  split
  · rfl
  · dsimp only
    apply Nat.max_eq_left
    have hq : (offset + size - 1) / 32 < curr :=
      (Nat.div_lt_iff_lt_mul (by omega)).2 (by omega)
    omega

private theorem activeWordsAfter_le (curr offset size bound : Nat)
    (hcurr : curr ≤ bound) (hend : offset + size ≤ bound * 32) :
    MachineState.activeWordsAfter curr offset size ≤ bound := by
  unfold MachineState.activeWordsAfter
  split
  · exact hcurr
  · dsimp only
    apply (Nat.max_le).2
    constructor
    · exact hcurr
    have hq : (offset + size - 1) / 32 < bound :=
      (Nat.div_lt_iff_lt_mul (by omega)).2 (by omega)
    omega

private theorem activeWordsAfter_ge (curr offset size : Nat) :
    curr ≤ MachineState.activeWordsAfter curr offset size := by
  unfold MachineState.activeWordsAfter
  split
  · exact Nat.le_refl _
  · exact Nat.le_max_left _ _

private theorem ofNat_toNat (w : UInt256) : UInt256.ofNat w.toNat = w := by
  cases w with
  | mk val =>
      unfold UInt256.ofNat UInt256.toNat
      congr 1
      apply Fin.ext
      simp [Fin.ofNat, Nat.mod_eq_of_lt val.isLt]

private theorem activeWordsAfterUInt256_eq (s : State) (offset size : Nat)
    (hend : offset + size ≤ s.activeWords.toNat * 32) :
    s.activeWordsAfterUInt256 offset size = s.activeWords := by
  rw [State.activeWordsAfterUInt256,
    activeWordsAfter_eq_of_end_le _ _ _ hend, ofNat_toNat]

private theorem activeWordsAfterUInt256_toNat (s : State)
    (offset size : Nat)
    (hlt : MachineState.activeWordsAfter s.activeWords.toNat offset size <
      2 ^ 256) :
    (s.activeWordsAfterUInt256 offset size).toNat =
      MachineState.activeWordsAfter s.activeWords.toNat offset size := by
  rw [State.activeWordsAfterUInt256, Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt hlt]

private theorem messageLoadOffset (input : ByteArray)
    (hfit : CalldataFits input) (i k : Nat)
    (hi : i < DriverTrace.blockCount input) (hk : k < 16) :
    (Schedule.loadOffsetWord (DriverTrace.messageOffsetWord i) k).toNat =
      Padding.messageOffset + 64 * i + 4 * k := by
  have hpadded := Padding.paddedLength_lt input.size
  have hoff : 64 * i < Padding.paddedLength input.size := by
    rw [DriverTrace.paddedLength_eq_blockCount input]
    omega
  have hload : Padding.messageOffset + 64 * i + 4 * k < 2 ^ 256 := by
    unfold CalldataFits at hfit
    norm_num [Padding.messageOffset] at hfit ⊢
    omega
  unfold Schedule.loadOffsetWord DriverTrace.messageOffsetWord
    DriverTrace.blockOffset
  rw [Challenge.EvmProof.Word.shiftLeft_ofNat (by omega) (by decide)
      (by omega : k * 2 ^ 2 < 2 ^ 256)]
  rw [show k * 2 ^ 2 = 4 * k by omega]
  rw [Challenge.EvmProof.Word.ofNat_add_ofNat (by omega)]
  rw [Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt (by omega :
      4 * k + (Padding.messageOffset + i * 64) < 2 ^ 256)]
  omega

private theorem xSlotOffset (k : Nat) (hk : k < 16) :
    (Schedule.xSlotWord k).toNat = 0x2a0 + 32 * k := by
  unfold Schedule.xSlotWord
  rw [Challenge.EvmProof.Word.shiftLeft_ofNat (by omega) (by decide)
      (by omega : k * 2 ^ 5 < 2 ^ 256)]
  rw [show k * 2 ^ 5 = 32 * k by omega]
  rw [Challenge.EvmProof.Word.ofNat_add_ofNat (by omega)]
  rw [Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : 32 * k + 0x2a0 < 2 ^ 256)]
  omega

private theorem scheduleIteration_activeWords_le (s : State)
    (input : ByteArray) (hfit : CalldataFits input) (block k : Nat)
    (hblock : block < DriverTrace.blockCount input) (hk : k < 16)
    (returnDest : UInt256) (rest : List UInt256) (bound : Nat)
    (hs : s.activeWords.toNat ≤ bound)
    (hbound : 67 + 2 * block ≤ bound) (hlt : bound < 2 ^ 256) :
    (Schedule.afterIteration s (DriverTrace.messageOffsetWord block)
      returnDest rest k).activeWords.toNat ≤ bound := by
  have hload := messageLoadOffset input hfit block k hblock hk
  have hx := xSlotOffset k hk
  let loadedWords := MachineState.activeWordsAfter s.activeWords.toNat
    (Schedule.loadOffsetWord (DriverTrace.messageOffsetWord block) k).toNat 32
  have hloaded : loadedWords ≤ bound := by
    apply activeWordsAfter_le _ _ _ _ hs
    rw [hload]
    simp [Padding.messageOffset]
    omega
  have hloadedLt : loadedWords < 2 ^ 256 := lt_of_le_of_lt hloaded hlt
  let loaded := Schedule.afterRead s (DriverTrace.messageOffsetWord block)
    returnDest rest k
  have hloadedEq : loaded.activeWords.toNat = loadedWords := by
    unfold loaded Schedule.afterRead loadedWords
    exact activeWordsAfterUInt256_toNat s _ _ hloadedLt
  have hstored : MachineState.activeWordsAfter loaded.activeWords.toNat
      (Schedule.xSlotWord k).toNat 32 ≤ bound := by
    apply activeWordsAfter_le _ _ _ _ (by rw [hloadedEq]; exact hloaded)
    rw [hx]
    omega
  have hstoredLt : MachineState.activeWordsAfter loaded.activeWords.toNat
      (Schedule.xSlotWord k).toNat 32 < 2 ^ 256 :=
    lt_of_le_of_lt hstored hlt
  change ((loaded.activeWordsAfterUInt256
    (Schedule.xSlotWord k).toNat 32).toNat ≤ bound)
  rw [activeWordsAfterUInt256_toNat loaded _ _ hstoredLt]
  exact hstored

private theorem scheduleLoopPrefix_activeWords_le (s : State)
    (input : ByteArray) (hfit : CalldataFits input) (block : Nat)
    (hblock : block < DriverTrace.blockCount input)
    (returnDest : UInt256) (rest : List UInt256) (n : Nat) (hn : n ≤ 16) :
    (Schedule.loopState s (DriverTrace.messageOffsetWord block)
      returnDest rest n).activeWords.toNat ≤
      max s.activeWords.toNat (67 + 2 * block) := by
  let bound := max s.activeWords.toNat (67 + 2 * block)
  have hlt : bound < 2 ^ 256 := by
    unfold bound
    exact (Nat.max_lt).2 ⟨s.activeWords.val.isLt, by
      have hpadded := Padding.paddedLength_lt input.size
      have hoff : 64 * block < Padding.paddedLength input.size := by
        rw [DriverTrace.paddedLength_eq_blockCount input]
        omega
      unfold CalldataFits at hfit
      norm_num [Padding.messageOffset] at hfit ⊢
      omega⟩
  have hloop : ∀ n, n ≤ 16 →
      (Schedule.loopState s (DriverTrace.messageOffsetWord block)
        returnDest rest n).activeWords.toNat ≤ bound := by
    intro n hn
    induction n with
    | zero => exact Nat.le_max_left _ _
    | succ n ih =>
        rw [Schedule.loopState]
        apply scheduleIteration_activeWords_le
          (Schedule.loopState s (DriverTrace.messageOffsetWord block)
            returnDest rest n)
          input hfit block n hblock (by omega) returnDest rest bound
          (ih (by omega)) (Nat.le_max_right _ _) hlt
  exact hloop n hn

private theorem scheduleLoop_activeWords_le (s : State)
    (input : ByteArray) (hfit : CalldataFits input) (block : Nat)
    (hblock : block < DriverTrace.blockCount input)
    (returnDest : UInt256) (rest : List UInt256) :
    (Schedule.loopState s (DriverTrace.messageOffsetWord block)
      returnDest rest 16).activeWords.toNat ≤
      max s.activeWords.toNat (67 + 2 * block) :=
  scheduleLoopPrefix_activeWords_le s input hfit block hblock returnDest rest
    16 (by omega)

private theorem scheduleIteration_activeWords_ge (s : State)
    (input : ByteArray) (hfit : CalldataFits input) (block k : Nat)
    (hblock : block < DriverTrace.blockCount input) (hk : k < 16)
    (returnDest : UInt256) (rest : List UInt256) (bound : Nat)
    (hs : s.activeWords.toNat ≤ bound)
    (hbound : 67 + 2 * block ≤ bound) (hlt : bound < 2 ^ 256) :
    s.activeWords.toNat ≤
      (Schedule.afterIteration s (DriverTrace.messageOffsetWord block)
        returnDest rest k).activeWords.toNat := by
  have hload := messageLoadOffset input hfit block k hblock hk
  have hx := xSlotOffset k hk
  let loadedWords := MachineState.activeWordsAfter s.activeWords.toNat
    (Schedule.loadOffsetWord (DriverTrace.messageOffsetWord block) k).toNat 32
  have hloaded : loadedWords ≤ bound := by
    apply activeWordsAfter_le _ _ _ _ hs
    rw [hload]
    simp [Padding.messageOffset]
    omega
  have hloadedLt : loadedWords < 2 ^ 256 := lt_of_le_of_lt hloaded hlt
  let loaded := Schedule.afterRead s (DriverTrace.messageOffsetWord block)
    returnDest rest k
  have hloadedEq : loaded.activeWords.toNat = loadedWords := by
    unfold loaded Schedule.afterRead loadedWords
    exact activeWordsAfterUInt256_toNat s _ _ hloadedLt
  have hstored : MachineState.activeWordsAfter loaded.activeWords.toNat
      (Schedule.xSlotWord k).toNat 32 ≤ bound := by
    apply activeWordsAfter_le _ _ _ _ (by rw [hloadedEq]; exact hloaded)
    rw [hx]
    omega
  have hstoredLt : MachineState.activeWordsAfter loaded.activeWords.toNat
      (Schedule.xSlotWord k).toNat 32 < 2 ^ 256 :=
    lt_of_le_of_lt hstored hlt
  change s.activeWords.toNat ≤ (loaded.activeWordsAfterUInt256
    (Schedule.xSlotWord k).toNat 32).toNat
  rw [activeWordsAfterUInt256_toNat loaded _ _ hstoredLt]
  exact le_trans (activeWordsAfter_ge _ _ _)
    (by rw [hloadedEq]
        exact activeWordsAfter_ge _ _ _)

private theorem scheduleLoopPrefix_activeWords_ge (s : State)
    (input : ByteArray) (hfit : CalldataFits input) (block : Nat)
    (hblock : block < DriverTrace.blockCount input)
    (returnDest : UInt256) (rest : List UInt256) (n : Nat) (hn : n ≤ 16) :
    s.activeWords.toNat ≤
      (Schedule.loopState s (DriverTrace.messageOffsetWord block)
        returnDest rest n).activeWords.toNat := by
  let bound := max s.activeWords.toNat (67 + 2 * block)
  have hlt : bound < 2 ^ 256 := by
    exact (Nat.max_lt).2 ⟨s.activeWords.val.isLt, by
      have hpadded := Padding.paddedLength_lt input.size
      have hoff : 64 * block < Padding.paddedLength input.size := by
        rw [DriverTrace.paddedLength_eq_blockCount input]
        omega
      unfold CalldataFits at hfit
      norm_num [Padding.messageOffset] at hfit ⊢
      omega⟩
  have hloop : ∀ n, n ≤ 16 →
      s.activeWords.toNat ≤
        (Schedule.loopState s (DriverTrace.messageOffsetWord block)
          returnDest rest n).activeWords.toNat := by
    intro n hn
    induction n with
    | zero => exact Nat.le_refl _
    | succ n ih =>
        rw [Schedule.loopState]
        exact le_trans (ih (by omega))
          (scheduleIteration_activeWords_ge
            (Schedule.loopState s (DriverTrace.messageOffsetWord block)
              returnDest rest n)
            input hfit block n hblock (by omega) returnDest rest bound
            (by
              exact scheduleLoopPrefix_activeWords_le s input hfit block hblock
                returnDest rest n (by omega))
            (Nat.le_max_right _ _) hlt)
  exact hloop n hn

private theorem scheduleLoop_activeWords_ge (s : State)
    (input : ByteArray) (hfit : CalldataFits input) (block : Nat)
    (hblock : block < DriverTrace.blockCount input)
    (returnDest : UInt256) (rest : List UInt256) :
    s.activeWords.toNat ≤
      (Schedule.loopState s (DriverTrace.messageOffsetWord block)
        returnDest rest 16).activeWords.toNat :=
  scheduleLoopPrefix_activeWords_ge s input hfit block hblock returnDest rest
    16 (by omega)

/-- The sixteen schedule iterations end exactly at the last unaligned message
load's high-water mark. -/
theorem scheduledState_activeWords (s : State) (input : ByteArray)
    (hfit : CalldataFits input) (block : Nat)
    (hblock : block < DriverTrace.blockCount input)
    (returnDest : UInt256) (rest : List UInt256) :
    (Schedule.loopState s (DriverTrace.messageOffsetWord block)
      returnDest rest 16).activeWords.toNat =
      max s.activeWords.toNat (67 + 2 * block) := by
  let prev := Schedule.loopState s (DriverTrace.messageOffsetWord block)
    returnDest rest 15
  let target := 67 + 2 * block
  let bound := max s.activeWords.toNat target
  have hprevLe : prev.activeWords.toNat ≤ bound :=
    scheduleLoopPrefix_activeWords_le s input hfit block hblock returnDest rest
      15 (by omega)
  have hprevGe : s.activeWords.toNat ≤ prev.activeWords.toNat :=
    scheduleLoopPrefix_activeWords_ge s input hfit block hblock returnDest rest
      15 (by omega)
  have hload := messageLoadOffset input hfit block 15 hblock (by omega)
  have hword :
      ((Schedule.loadOffsetWord (DriverTrace.messageOffsetWord block) 15).toNat +
          32 - 1) / 32 + 1 = target := by
    rw [hload]
    simp [target, Padding.messageOffset]
    omega
  have hloadedWords : MachineState.activeWordsAfter prev.activeWords.toNat
      (Schedule.loadOffsetWord (DriverTrace.messageOffsetWord block) 15).toNat
        32 = max prev.activeWords.toNat target := by
    simp only [MachineState.activeWordsAfter, if_neg (by omega : (32 : Nat) ≠ 0)]
    rw [hword]
  have htargetLt : target < 2 ^ 256 := by
    have hpadded := Padding.paddedLength_lt input.size
    have hoff : 64 * block < Padding.paddedLength input.size := by
      rw [DriverTrace.paddedLength_eq_blockCount input]
      omega
    unfold CalldataFits at hfit
    norm_num [target, Padding.messageOffset] at hfit ⊢
    omega
  have hloadedLt : MachineState.activeWordsAfter prev.activeWords.toNat
      (Schedule.loadOffsetWord (DriverTrace.messageOffsetWord block) 15).toNat
        32 < 2 ^ 256 := by
    rw [hloadedWords]
    exact (Nat.max_lt).2 ⟨prev.activeWords.val.isLt, htargetLt⟩
  let loaded := Schedule.afterRead prev (DriverTrace.messageOffsetWord block)
    returnDest rest 15
  have hloaded : loaded.activeWords.toNat =
      max prev.activeWords.toNat target := by
    unfold loaded Schedule.afterRead
    rw [activeWordsAfterUInt256_toNat prev _ _ hloadedLt, hloadedWords]
  have hx := xSlotOffset 15 (by omega)
  have hstore : loaded.activeWordsAfterUInt256
      (Schedule.xSlotWord 15).toNat 32 = loaded.activeWords := by
    apply activeWordsAfterUInt256_eq
    rw [hx, hloaded]
    have ht : target ≤ max prev.activeWords.toNat target := Nat.le_max_right _ _
    simp [target] at ht ⊢
    omega
  rw [show Schedule.loopState s (DriverTrace.messageOffsetWord block)
      returnDest rest 16 =
      Schedule.afterIteration prev (DriverTrace.messageOffsetWord block)
        returnDest rest 15 by rfl]
  change (loaded.activeWordsAfterUInt256
      (Schedule.xSlotWord 15).toNat 32).toNat = bound
  rw [hstore, hloaded]
  apply Nat.le_antisymm
  · apply (Nat.max_le).2
    exact ⟨hprevLe, Nat.le_max_right _ _⟩
  · apply (Nat.max_le).2
    exact ⟨hprevGe.trans (Nat.le_max_left _ _), Nat.le_max_right _ _⟩

private theorem activeWordsAfterUInt256_2_eq (s : State)
    (off₁ size₁ off₂ size₂ : Nat)
    (hend₁ : off₁ + size₁ ≤ s.activeWords.toNat * 32)
    (hend₂ : off₂ + size₂ ≤ s.activeWords.toNat * 32) :
    s.activeWordsAfterUInt256_2 off₁ size₁ off₂ size₂ = s.activeWords := by
  unfold State.activeWordsAfterUInt256_2
  rw [activeWordsAfter_eq_of_end_le _ _ _ hend₁,
    activeWordsAfter_eq_of_end_le _ _ _ hend₂, ofNat_toNat]

private theorem copyRegion_activeWords (s : State) (dest src size : Nat)
    (hdest : dest + size ≤ s.activeWords.toNat * 32)
    (hsrc : src + size ≤ s.activeWords.toNat * 32) :
    (copyRegion s dest src size).activeWords = s.activeWords := by
  unfold copyRegion
  exact activeWordsAfterUInt256_2_eq s dest size src size hdest hsrc

theorem copiedWorkingState_activeWords (s : State)
    (hactive : 21 ≤ s.activeWords.toNat) :
    (copiedWorkingState s).activeWords = s.activeWords := by
  let q₁ := copyRegion s 192 32 160
  let q₂ := copyRegion q₁ 352 32 160
  have h₁ : q₁.activeWords = s.activeWords := by
    apply copyRegion_activeWords <;> omega
  have h₂ : q₂.activeWords = s.activeWords := by
    exact (copyRegion_activeWords q₁ 352 32 160
      (by rw [h₁]; omega) (by rw [h₁]; omega)).trans h₁
  unfold copiedWorkingState
  exact (copyRegion_activeWords q₂ 512 32 160
    (by rw [h₂]; omega) (by rw [h₂]; omega)).trans h₂

private theorem slotAddress_toNat (base : Nat) (i : UInt256)
    (hi : i.toNat < 16) (hbase : base + 32 * i.toNat < 2 ^ 256) :
    (TableTrace.slotAddress (UInt256.ofNat base) i).toNat =
      base + 32 * i.toNat := by
  have hshift : UInt256.shiftLeft i (UInt256.ofNat 5) =
      UInt256.ofNat (32 * i.toNat) := by
    conv_lhs => rw [← ofNat_toNat i]
    rw [Challenge.EvmProof.Word.shiftLeft_ofNat (by omega) (by decide)
        (by omega : i.toNat * 2 ^ 5 < 2 ^ 256)]
    congr 1
    omega
  unfold TableTrace.slotAddress
  rw [hshift]
  rw [Challenge.EvmProof.Word.ofNat_add_ofNat (by omega)]
  rw [Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt (by omega)]
  omega

private theorem tableAddress_toNat (base i : Nat) (hi : i < 80)
    (hbase : base + 32 * (i / 32) < 2 ^ 256) :
    (TableTrace.tableAddress (UInt256.ofNat base) (UInt256.ofNat i)).toNat =
      base + 32 * (i / 32) := by
  unfold TableTrace.tableAddress
  rw [Challenge.EvmProof.Word.shiftRight_ofNat (by omega) (by decide)]
  rw [Nat.shiftRight_eq_div_pow]
  norm_num
  rw [Challenge.EvmProof.Word.shiftLeft_ofNat (by omega) (by decide)
      (by omega : (i / 32) * 2 ^ 5 < 2 ^ 256)]
  rw [show (i / 32) * 2 ^ 5 = 32 * (i / 32) by omega]
  rw [Challenge.EvmProof.Word.ofNat_add_ofNat (by omega)]
  rw [Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt (by omega)]
  omega

private theorem tableAtReturned_activeWords (s : State) (base i : Nat)
    (hi : i < 80) (hactive : 67 ≤ s.activeWords.toNat)
    (hbase : base + 96 + 32 ≤ 67 * 32) (returnDest : UInt256)
    (rest : List UInt256) :
    (TableTrace.tableAtReturned s (UInt256.ofNat base) (UInt256.ofNat i)
      returnDest rest).activeWords = s.activeWords := by
  unfold TableTrace.tableAtReturned
  apply activeWordsAfterUInt256_eq
  rw [tableAddress_toNat base i hi (by omega)]
  have hdiv : i / 32 ≤ 2 := by omega
  omega

private theorem afterConstantLoad_activeWords (s : State) (base i : Nat)
    (hi : i < 80) (hactive : 67 ≤ s.activeWords.toNat)
    (hbase : base + 4 * 32 + 32 ≤ 67 * 32) :
    (afterConstantLoad s base i).activeWords = s.activeWords := by
  unfold afterConstantLoad roundIndex
  apply activeWordsAfterUInt256_eq
  have hdiv : i / 16 ≤ 4 := by omega
  omega

private theorem addWord_toNat (base off : Nat)
    (hlt : base + off < 2 ^ 256) :
    (UInt256.ofNat base + UInt256.ofNat off).toNat = base + off := by
  rw [Challenge.EvmProof.Word.ofNat_add_ofNat hlt,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hlt]

private theorem afterLoads_activeWords (s : State) (base : Nat)
    (hactive : 67 ≤ s.activeWords.toNat)
    (hbase : base + 0x80 + 32 ≤ 67 * 32) :
    (afterLoads s (UInt256.ofNat base)).activeWords = s.activeWords := by
  let q₀ := { s with activeWords :=
    s.activeWordsAfterUInt256 (UInt256.ofNat base).toNat 32 }
  let q₁ := { q₀ with activeWords := (q₀.activeWordsAfterUInt256
    (UInt256.ofNat base + UInt256.ofNat 0x20).toNat 32) }
  let q₂ := { q₁ with activeWords := (q₁.activeWordsAfterUInt256
    (UInt256.ofNat base + UInt256.ofNat 0x40).toNat 32) }
  let q₃ := { q₂ with activeWords := (q₂.activeWordsAfterUInt256
    (UInt256.ofNat base + UInt256.ofNat 0x60).toNat 32) }
  have h₀ : q₀.activeWords = s.activeWords := by
    apply activeWordsAfterUInt256_eq
    rw [Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : base < 2 ^ 256)]
    omega
  have h₁ : q₁.activeWords = s.activeWords := by
    apply Eq.trans (activeWordsAfterUInt256_eq q₀ _ 32 (by
      rw [addWord_toNat base 0x20 (by omega), h₀]
      omega)) h₀
  have h₂ : q₂.activeWords = s.activeWords := by
    apply Eq.trans (activeWordsAfterUInt256_eq q₁ _ 32 (by
      rw [addWord_toNat base 0x40 (by omega), h₁]
      omega)) h₁
  have h₃ : q₃.activeWords = s.activeWords := by
    apply Eq.trans (activeWordsAfterUInt256_eq q₂ _ 32 (by
      rw [addWord_toNat base 0x60 (by omega), h₂]
      omega)) h₂
  unfold afterLoads
  change (q₃.activeWordsAfterUInt256
    (UInt256.ofNat base + UInt256.ofNat 0x80).toNat 32) = _
  exact (activeWordsAfterUInt256_eq q₃ _ 32 (by
    rw [addWord_toNat base 0x80 (by omega), h₃]
    omega)).trans h₃

private theorem storedWord_activeWords (s : State) (base index : Nat)
    (hindex : index < 16) (hactive : 67 ≤ s.activeWords.toNat)
    (hbase : base + 32 * index + 32 ≤ 67 * 32) (value : UInt256) :
    (TableTrace.storedWord s (UInt256.ofNat base) (UInt256.ofNat index)
      value).activeWords = s.activeWords := by
  unfold TableTrace.storedWord
  apply activeWordsAfterUInt256_eq
  rw [slotAddress_toNat base (UInt256.ofNat index)
    (by
      rw [Challenge.EvmProof.Word.word_toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : index < 2 ^ 256)]
      exact hindex)
    (by
      rw [Challenge.EvmProof.Word.word_toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : index < 2 ^ 256)]
      omega)]
  rw [Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : index < 2 ^ 256)]
  omega

/-- A compiled round only touches fixed scratch words, provided its X selector
is one of the sixteen schedule entries. -/
theorem roundReturned_activeWords (s : State) (base : Nat)
    (hbase : base + 0x80 + 32 ≤ 67 * 32) (j : Nat)
    (wordIndex rotation k returnDest : UInt256) (hword : wordIndex.toNat < 16)
    (rest : List UInt256) (hactive : 67 ≤ s.activeWords.toNat) :
    (RoundTrace.roundReturned s (UInt256.ofNat base) j wordIndex rotation k
      returnDest rest).activeWords = s.activeWords := by
  let loaded := afterLoads s (UInt256.ofNat base)
  have hloaded : loaded.activeWords = s.activeWords :=
    afterLoads_activeWords s base hactive hbase
  let xret := xReturnedState s (UInt256.ofNat base) j wordIndex rotation k
    returnDest rest
  have hx : xret.activeWords = s.activeWords := by
    unfold xret xReturnedState TableTrace.atReturned
    apply Eq.trans (activeWordsAfterUInt256_eq loaded _ 32 (by
      rw [slotAddress_toNat 0x2a0 wordIndex hword (by omega), hloaded]
      omega)) hloaded
  let first := afterFirstStores xret (UInt256.ofNat base)
  have hfirst : first.activeWords = s.activeWords := by
    unfold first afterFirstStores
    have h₀ := storedWord_activeWords xret base 0 (by omega)
      (by rw [hx]; exact hactive) (by omega) (RoundTrace.loadedE xret (UInt256.ofNat base))
    exact (storedWord_activeWords
      (TableTrace.storedWord xret (UInt256.ofNat base) (UInt256.ofNat 0)
        (RoundTrace.loadedE xret (UInt256.ofNat base)))
      base 4 (by omega) (by rw [h₀, hx]; exact hactive) (by omega)
      (RoundTrace.loadedD xret (UInt256.ofNat base))).trans (h₀.trans hx)
  have hthird : (genericAfterThirdStore first (UInt256.ofNat base)
      (RoundTrace.loadedC s (UInt256.ofNat base))).activeWords = s.activeWords := by
    unfold genericAfterThirdStore
    exact (storedWord_activeWords first base 3 (by omega)
      (by rw [hfirst]; exact hactive) (by omega) _).trans hfirst
  unfold RoundTrace.roundReturned genericReturned
  dsimp only
  have h₂ := storedWord_activeWords
    (genericAfterThirdStore first (UInt256.ofNat base)
      (RoundTrace.loadedC s (UInt256.ofNat base)))
    base 2 (by omega) (by rw [hthird]; exact hactive) (by omega)
    (RoundTrace.loadedB s (UInt256.ofNat base))
  exact (storedWord_activeWords
    (TableTrace.storedWord
      (genericAfterThirdStore first (UInt256.ofNat base)
        (RoundTrace.loadedC s (UInt256.ofNat base)))
      (UInt256.ofNat base) (UInt256.ofNat 2)
      (RoundTrace.loadedB s (UInt256.ofNat base)))
    base 1 (by omega) (by rw [h₂, hthird]; exact hactive) (by omega) _).trans
      (h₂.trans hthird)

private theorem leftRoundState_activeWords (s : State)
    (messageOffset returnDest : UInt256) (rest : List UInt256)
    (i : Nat) (hi : i < 80)
    (htables : InitializationCorrect.TablesCorrect s.memory)
    (hactive : 67 ≤ s.activeWords.toNat) :
    (leftRoundState s messageOffset returnDest rest i).activeWords =
      s.activeWords := by
  let q₀ := afterConstantLoad s 1568 i
  have h₀ : q₀.activeWords = s.activeWords :=
    afterConstantLoad_activeWords s 1568 i hi hactive (by omega)
  let q₁ := leftFirstReturned s messageOffset returnDest rest i
  have h₁ : q₁.activeWords = s.activeWords := by
    unfold q₁ leftFirstReturned
    exact (tableAtReturned_activeWords q₀ 1376 i hi
      (by rw [h₀]; exact hactive) (by omega) _ _).trans h₀
  let q₂ := leftSecondReturned s messageOffset returnDest rest i
  have h₂ : q₂.activeWords = s.activeWords := by
    unfold q₂ leftSecondReturned
    exact (tableAtReturned_activeWords q₁ 1184 i hi
      (by rw [h₁]; exact hactive) (by omega) _ _).trans h₁
  have hword :
      (TableTrace.tableValue q₁ (UInt256.ofNat 1184)
        (UInt256.ofNat i)).toNat < 16 := by
    rw [TableTrace.tableValue_tableByte q₁ 1184 i (by omega) hi]
    change (InitializationCorrect.tableByte s.memory 1184 i).toNat < 16
    rw [htables.1 i hi, Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt (lt_trans (leftSelector_lt i hi) (by norm_num))]
    exact leftSelector_lt i hi
  unfold leftRoundState
  exact (roundReturned_activeWords q₂ 192 (by omega) (roundIndex i)
    (TableTrace.tableValue q₁ (UInt256.ofNat 1184) (UInt256.ofNat i))
    (TableTrace.tableValue s (UInt256.ofNat 1376) (UInt256.ofNat i))
    (constantAt s 1568 i) (UInt256.ofNat 714) hword _
    (by rw [h₂]; exact hactive)).trans h₂

private theorem leftStates_tables_preserved (s : State)
    (messageOffset returnDest : UInt256) (rest : List UInt256) (n : Nat)
    (htables : InitializationCorrect.TablesCorrect s.memory) :
    InitializationCorrect.TablesCorrect
      (leftStates s messageOffset returnDest rest n).memory := by
  rcases htables with ⟨hr, hrP, hs, hsP⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [leftStates_tableByte s messageOffset returnDest rest n 1184 i
      (by omega)]
    exact hr i hi
  · intro i hi
    rw [leftStates_tableByte s messageOffset returnDest rest n 1280 i
      (by omega)]
    exact hrP i hi
  · intro i hi
    rw [leftStates_tableByte s messageOffset returnDest rest n 1376 i
      (by omega)]
    exact hs i hi
  · intro i hi
    rw [leftStates_tableByte s messageOffset returnDest rest n 1472 i
      (by omega)]
    exact hsP i hi

theorem leftStates_activeWords (s : State)
    (messageOffset returnDest : UInt256) (rest : List UInt256)
    (htables : InitializationCorrect.TablesCorrect s.memory)
    (hactive : 67 ≤ s.activeWords.toNat) :
    (leftStates s messageOffset returnDest rest 80).activeWords =
      s.activeWords := by
  have hloop : ∀ n, n ≤ 80 →
      (leftStates s messageOffset returnDest rest n).activeWords =
        s.activeWords := by
    intro n hn
    induction n with
    | zero => rfl
    | succ n ih =>
        rw [leftStates_succ]
        exact (leftRoundState_activeWords
          (leftStates s messageOffset returnDest rest n)
          messageOffset returnDest rest n (by omega)
          (leftStates_tables_preserved s messageOffset returnDest rest n htables)
          (by rw [ih (by omega)]; exact hactive)).trans (ih (by omega))
  exact hloop 80 (by omega)

private theorem rightRoundState_activeWords (s : State)
    (messageOffset returnDest : UInt256) (rest : List UInt256)
    (i : Nat) (hi : i < 80)
    (htables : InitializationCorrect.TablesCorrect s.memory)
    (hactive : 67 ≤ s.activeWords.toNat) :
    (rightRoundState s messageOffset returnDest rest i).activeWords =
      s.activeWords := by
  let q₀ := afterConstantLoad s 1728 i
  have h₀ : q₀.activeWords = s.activeWords :=
    afterConstantLoad_activeWords s 1728 i hi hactive (by omega)
  let q₁ := rightFirstReturned s messageOffset returnDest rest i
  have h₁ : q₁.activeWords = s.activeWords := by
    unfold q₁ rightFirstReturned
    exact (tableAtReturned_activeWords q₀ 1472 i hi
      (by rw [h₀]; exact hactive) (by omega) _ _).trans h₀
  let q₂ := rightSecondReturned s messageOffset returnDest rest i
  have h₂ : q₂.activeWords = s.activeWords := by
    unfold q₂ rightSecondReturned
    exact (tableAtReturned_activeWords q₁ 1280 i hi
      (by rw [h₁]; exact hactive) (by omega) _ _).trans h₁
  have hword :
      (TableTrace.tableValue q₁ (UInt256.ofNat 1280)
        (UInt256.ofNat i)).toNat < 16 := by
    rw [TableTrace.tableValue_tableByte q₁ 1280 i (by omega) hi]
    change (InitializationCorrect.tableByte s.memory 1280 i).toNat < 16
    rw [htables.2.1 i hi, Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt (lt_trans (rightSelector_lt i hi) (by norm_num))]
    exact rightSelector_lt i hi
  unfold rightRoundState
  exact (roundReturned_activeWords q₂ 352 (by omega) (rightRoundIndex i)
    (TableTrace.tableValue q₁ (UInt256.ofNat 1280) (UInt256.ofNat i))
    (TableTrace.tableValue s (UInt256.ofNat 1472) (UInt256.ofNat i))
    (constantAt s 1728 i) (UInt256.ofNat 792) hword _
    (by rw [h₂]; exact hactive)).trans h₂

private theorem rightStates_tables_preserved (s : State)
    (messageOffset returnDest : UInt256) (rest : List UInt256) (n : Nat)
    (htables : InitializationCorrect.TablesCorrect s.memory) :
    InitializationCorrect.TablesCorrect
      (rightStates s messageOffset returnDest rest n).memory := by
  rcases htables with ⟨hr, hrP, hs, hsP⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [rightStates_tableByte s messageOffset returnDest rest n 1184 i
      (by omega)]
    exact hr i hi
  · intro i hi
    rw [rightStates_tableByte s messageOffset returnDest rest n 1280 i
      (by omega)]
    exact hrP i hi
  · intro i hi
    rw [rightStates_tableByte s messageOffset returnDest rest n 1376 i
      (by omega)]
    exact hs i hi
  · intro i hi
    rw [rightStates_tableByte s messageOffset returnDest rest n 1472 i
      (by omega)]
    exact hsP i hi

theorem rightStates_activeWords (s : State)
    (messageOffset returnDest : UInt256) (rest : List UInt256)
    (htables : InitializationCorrect.TablesCorrect s.memory)
    (hactive : 67 ≤ s.activeWords.toNat) :
    (rightStates s messageOffset returnDest rest 80).activeWords =
      s.activeWords := by
  have hloop : ∀ n, n ≤ 80 →
      (rightStates s messageOffset returnDest rest n).activeWords =
        s.activeWords := by
    intro n hn
    induction n with
    | zero => rfl
    | succ n ih =>
        rw [rightStates_succ]
        exact (rightRoundState_activeWords
          (rightStates s messageOffset returnDest rest n)
          messageOffset returnDest rest n (by omega)
          (rightStates_tables_preserved s messageOffset returnDest rest n htables)
          (by rw [ih (by omega)]; exact hactive)).trans (ih (by omega))
  exact hloop 80 (by omega)

private def touchWords : State → List Nat → State
  | s, [] => s
  | s, off :: rest => touchWords (touchWord s off) rest

private theorem touchWords_activeWords (s : State) (offsets : List Nat)
    (hactive : 21 ≤ s.activeWords.toNat)
    (hoffsets : ∀ off ∈ offsets, off ≤ 640) :
    (touchWords s offsets).activeWords = s.activeWords := by
  induction offsets generalizing s with
  | nil => rfl
  | cons off rest ih =>
      have hoff : off ≤ 640 := hoffsets off (by simp)
      have htail : ∀ next ∈ rest, next ≤ 640 := by
        intro next hnext
        exact hoffsets next (by simp [hnext])
      have htouch : (touchWord s off).activeWords = s.activeWords := by
        unfold touchWord
        exact activeWords_unchanged s hactive off hoff
      exact (ih (touchWord s off) (by rw [htouch]; exact hactive) htail).trans
        htouch

private theorem touched4_activeWords (s : State)
    (hactive : 67 ≤ s.activeWords.toNat) :
    (touched4 s).activeWords = s.activeWords := by
  change (touchWords s
    [448, 256, 544, 480, 288, 576, 64, 352, 320, 608, 96,
      384, 192, 640, 128, 416, 224, 512, 160, 32]).activeWords = _
  apply touchWords_activeWords s _ (by omega)
  simp

private theorem combination4_activeWords_eq (s : State)
    (messageOffset returnDest : UInt256) (rest : List UInt256) :
    (combination4 s messageOffset returnDest rest).activeWords =
      (touched4 s).activeWords := rfl

private theorem combinationReturned_activeWords_eq (s : State)
    (messageOffset returnDest : UInt256) (rest : List UInt256) :
    (combinationReturned s messageOffset returnDest rest).activeWords =
      (combination4 s messageOffset returnDest rest).activeWords := rfl

private theorem rightTailResult_outer_activeWords (s : State)
    (messageOffset returnDest : UInt256) (rest : List UInt256) :
    (rightTailResult s messageOffset returnDest rest).activeWords =
      (combinationReturned (rightStates s messageOffset returnDest rest 80)
        messageOffset returnDest rest).activeWords := rfl

private theorem rightTailResult_activeWords (s : State)
    (messageOffset returnDest : UInt256) (rest : List UInt256)
    (htables : InitializationCorrect.TablesCorrect s.memory)
    (hactive : 67 ≤ s.activeWords.toNat) :
    (rightTailResult s messageOffset returnDest rest).activeWords =
      s.activeWords := by
  have hrounded :
      (rightStates s messageOffset returnDest rest 80).activeWords =
        s.activeWords :=
    rightStates_activeWords s messageOffset returnDest rest htables hactive
  rw [rightTailResult_outer_activeWords, combinationReturned_activeWords_eq,
    combination4_activeWords_eq]
  exact (touched4_activeWords
    (rightStates s messageOffset returnDest rest 80)
    (by rw [hrounded]; exact hactive)).trans hrounded

private theorem leftInitialState_tables_preserved (s : State)
    (messageOffset returnDest : UInt256) (rest : List UInt256)
    (htables : InitializationCorrect.TablesCorrect s.memory) :
    InitializationCorrect.TablesCorrect
      (leftInitialState s messageOffset returnDest rest).memory := by
  rcases htables with ⟨hr, hrP, hs, hsP⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i hi
    unfold InitializationCorrect.tableByte
    change UInt256.byteAt (UInt256.ofNat (i % 32))
      (wordAt (leftInitialState s messageOffset returnDest rest)
        (0x4a0 + 32 * (i / 32))) = _
    rw [CompressionFunctionalTrace.leftInitialState_words s messageOffset
      returnDest rest _ (by omega)]
    exact hr i hi
  · intro i hi
    unfold InitializationCorrect.tableByte
    change UInt256.byteAt (UInt256.ofNat (i % 32))
      (wordAt (leftInitialState s messageOffset returnDest rest)
        (0x500 + 32 * (i / 32))) = _
    rw [CompressionFunctionalTrace.leftInitialState_words s messageOffset
      returnDest rest _ (by omega)]
    exact hrP i hi
  · intro i hi
    unfold InitializationCorrect.tableByte
    change UInt256.byteAt (UInt256.ofNat (i % 32))
      (wordAt (leftInitialState s messageOffset returnDest rest)
        (0x560 + 32 * (i / 32))) = _
    rw [CompressionFunctionalTrace.leftInitialState_words s messageOffset
      returnDest rest _ (by omega)]
    exact hs i hi
  · intro i hi
    unfold InitializationCorrect.tableByte
    change UInt256.byteAt (UInt256.ofNat (i % 32))
      (wordAt (leftInitialState s messageOffset returnDest rest)
        (0x5c0 + 32 * (i / 32))) = _
    rw [CompressionFunctionalTrace.leftInitialState_words s messageOffset
      returnDest rest _ (by omega)]
    exact hsP i hi

/-- One complete compression call reaches exactly the schedule's last
unaligned message load. All subsequent scratch and table accesses stay below
that high-water mark. -/
theorem resultState_activeWords (s : State) (input : ByteArray)
    (hfit : CalldataFits input) (block : Nat)
    (hblock : block < DriverTrace.blockCount input)
    (htables : InitializationCorrect.TablesCorrect s.memory) :
    (CompressionFullTrace.resultState s input block).activeWords.toNat =
      max s.activeWords.toNat (67 + 2 * block) := by
  let messageOffset := DriverTrace.messageOffsetWord block
  let returnDest := UInt256.ofNat 0x643
  let rest := CompressionFullTrace.driverRest input block
  let scheduled := scheduledState s messageOffset returnDest rest
  have hscheduled : scheduled.activeWords.toNat =
      max s.activeWords.toNat (67 + 2 * block) := by
    unfold scheduled messageOffset
    simpa [scheduledState] using
      scheduledState_activeWords s input hfit block hblock
        (UInt256.ofNat 630) (DriverTrace.messageOffsetWord block ::
          returnDest :: rest)
  have hscheduledActive : 67 ≤ scheduled.activeWords.toNat := by
    rw [hscheduled]
    exact le_trans (by omega : 67 ≤ 67 + 2 * block)
      (Nat.le_max_right _ _)
  let initial := leftInitialState s messageOffset returnDest rest
  have hinitial : initial.activeWords = scheduled.activeWords := by
    unfold initial leftInitialState
    exact copiedWorkingState_activeWords scheduled (by omega)
  have hinitialActive : 67 ≤ initial.activeWords.toNat := by
    rw [hinitial]
    exact hscheduledActive
  have hinitialTables : InitializationCorrect.TablesCorrect initial.memory := by
    unfold initial
    exact leftInitialState_tables_preserved s messageOffset returnDest rest htables
  let leftFinal := leftFinalState s messageOffset returnDest rest
  have hleft : leftFinal.activeWords = initial.activeWords := by
    unfold leftFinal initial
    exact leftStates_activeWords _ messageOffset returnDest rest hinitialTables
      hinitialActive
  have hleftActive : 67 ≤ leftFinal.activeWords.toNat := by
    rw [hleft]
    exact hinitialActive
  have hleftTables : InitializationCorrect.TablesCorrect leftFinal.memory := by
    unfold leftFinal
    exact leftStates_tables_preserved initial messageOffset returnDest rest 80
      hinitialTables
  have htail := rightTailResult_activeWords leftFinal messageOffset returnDest
    rest hleftTables hleftActive
  calc
    (CompressionFullTrace.resultState s input block).activeWords.toNat =
        (rightTailResult leftFinal messageOffset returnDest rest).activeWords.toNat := by
      rfl
    _ = leftFinal.activeWords.toNat := congrArg UInt256.toNat htail
    _ = initial.activeWords.toNat := congrArg UInt256.toNat hleft
    _ = scheduled.activeWords.toNat := congrArg UInt256.toNat hinitial
    _ = max s.activeWords.toNat (67 + 2 * block) := hscheduled

end Challenge.Ripemd160.Reference.Proofs.Bytecode.CompressionActiveWords
