import Challenge.Sha256.Reference.Proofs.Bytecode.Driver
import Challenge.Sha256.Reference.Proofs.Bytecode.PaddingGas

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
# Active-memory endpoints of the reference SHA-256 driver

The padding routine leaves memory active through the end of the padded input.
The compression loop then reads four-byte schedule inputs using `MLOAD`; the
last such read extends 28 bytes beyond the padded input and therefore adds one
active word.  All schedule, hash-state, and compression scratch accesses are
below this high-water mark.
-/

namespace Challenge.Sha256.Reference.Proofs.Bytecode.DriverMemory

open Challenge.Sha256
open EvmSemantics
open EvmSemantics.EVM

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

private theorem ofNat_toNat (w : UInt256) : UInt256.ofNat w.toNat = w := by
  exact (Challenge.EvmProof.Word.word_eq_ofNat_toNat w).symm

private theorem activeWordsAfterUInt256_eq (s : State) (offset size : Nat)
    (hend : offset + size ≤ s.activeWords.toNat * 32) :
    s.activeWordsAfterUInt256 offset size = s.activeWords := by
  rw [State.activeWordsAfterUInt256,
    activeWordsAfter_eq_of_end_le _ _ _ hend, ofNat_toNat]

private theorem slotOffset_ofNat (base j : Nat) (hj : j < 64)
    (hresult : base + 32 * j < 2 ^ 256) :
    Accessors.slotOffset base (UInt256.ofNat j) = base + 32 * j := by
  unfold Accessors.slotOffset
  rw [Challenge.EvmProof.Word.shiftLeft_ofNat (by omega) (by decide)
      (by omega : j * 2 ^ 5 < 2 ^ 256)]
  rw [show j * 2 ^ 5 = 32 * j by omega]
  rw [Challenge.EvmProof.Word.ofNat_add_ofNat (by omega)]
  rw [Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : 32 * j + base < 2 ^ 256)]
  omega

private theorem scheduleSlot_ofNat (j : Nat) (hj : j < 64) :
    Schedule.scheduleSlot j = 800 + 32 * j := by
  unfold Schedule.scheduleSlot
  exact slotOffset_ofNat 800 j hj (by omega)

private theorem loadReturned_activeWords_eq (s : State) (base j : Nat)
    (returnDest : UInt256) (rest : List UInt256) (hj : j < 64)
    (hresult : base + 32 * j < 2 ^ 256)
    (hend : base + 32 * j + 32 ≤ s.activeWords.toNat * 32) :
    (Accessors.loadReturned s base (UInt256.ofNat j) returnDest rest).activeWords =
      s.activeWords := by
  unfold Accessors.loadReturned
  rw [activeWordsAfterUInt256_eq s _ _ (by
    rw [slotOffset_ofNat base j hj hresult]
    exact hend)]

private theorem storeReturned_activeWords_eq (s : State) (base j : Nat)
    (value returnDest : UInt256) (rest : List UInt256) (hj : j < 64)
    (hresult : base + 32 * j < 2 ^ 256)
    (hend : base + 32 * j + 32 ≤ s.activeWords.toNat * 32) :
    (Accessors.storeReturned s base (UInt256.ofNat j) value returnDest rest).activeWords =
      s.activeWords := by
  unfold Accessors.storeReturned
  rw [activeWordsAfterUInt256_eq s _ _ (by
    rw [slotOffset_ofNat base j hj hresult]
    exact hend)]

private theorem kAtReturned_activeWords_eq (s : State) (j : Nat)
    (returnDest : UInt256) (rest : List UInt256) (hj : j < 64)
    (hend : 32 + 4 * j + 32 ≤ s.activeWords.toNat * 32) :
    (Accessors.kAtReturned s (UInt256.ofNat j) returnDest rest).activeWords =
      s.activeWords := by
  have hoff :
      (UInt256.shiftLeft (UInt256.ofNat j) (UInt256.ofNat 2) +
        UInt256.ofNat 32).toNat = 32 + 4 * j := by
    rw [Challenge.EvmProof.Word.shiftLeft_ofNat (by omega) (by decide)
        (by omega : j * 2 ^ 2 < 2 ^ 256)]
    rw [show j * 2 ^ 2 = 4 * j by omega]
    rw [Challenge.EvmProof.Word.ofNat_add_ofNat (by omega)]
    rw [Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : 4 * j + 32 < 2 ^ 256)]
    omega
  unfold Accessors.kAtReturned
  dsimp only
  rw [activeWordsAfterUInt256_eq s _ _ (by rw [hoff]; exact hend)]

private theorem blockCount_pos (input : ByteArray) : 0 < Driver.blockCount input := by
  unfold Driver.blockCount Padding.paddedLength
  omega

private theorem paddedEnd (input : ByteArray) :
    Padding.messageOffset + Padding.paddedLength input.size =
      (89 + 2 * Driver.blockCount input) * 32 := by
  rw [Driver.paddedLength_eq_blockCount]
  simp [Padding.messageOffset]
  omega

theorem blockLoopState_zero_activeWords (input : ByteArray)
    (hfit : CalldataFits input) :
    (Driver.blockLoopState input 0).activeWords.toNat =
      89 + 2 * Driver.blockCount input := by
  rw [show (Driver.blockLoopState input 0).activeWords =
      (PaddingTrace.lengthLoopState input 8).activeWords by rfl]
  change (PaddingTrace.lengthLoopActiveWords input 8).toNat = _
  simpa [Driver.blockCount, Padding.paddedLength] using
    PaddingGas.lengthLoopActiveWords_eight input hfit

theorem blockLoopState_zero_activeWords_ge_seventeen (input : ByteArray)
    (hfit : CalldataFits input) :
    17 ≤ (Driver.blockLoopState input 0).activeWords.toNat := by
  rw [blockLoopState_zero_activeWords input hfit]
  omega

private theorem messageLoadOffset (input : ByteArray) (hfit : CalldataFits input)
    (i j : Nat) (hi : i < Driver.blockCount input) (hj : j < 16) :
    Schedule.loadOffset (Driver.messageOffsetWord i) j =
      Padding.messageOffset + 64 * i + 4 * j := by
  have hiOffset : 64 * i < Padding.paddedLength input.size := by
    rw [Driver.paddedLength_eq_blockCount]
    omega
  have hpaddedLt := Padding.paddedLength_lt input.size
  have hload : Padding.messageOffset + 64 * i + 4 * j < 2 ^ 256 := by
    unfold CalldataFits at hfit
    norm_num [Padding.messageOffset] at hfit ⊢
    omega
  unfold Schedule.loadOffset Driver.messageOffsetWord Driver.blockOffset
  rw [Challenge.EvmProof.Word.shiftLeft_ofNat (by omega) (by decide)
      (by omega : j * 2 ^ 2 < 2 ^ 256)]
  rw [show j * 2 ^ 2 = 4 * j by omega]
  rw [Challenge.EvmProof.Word.ofNat_add_ofNat (by omega)]
  rw [Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : 4 * j + (Padding.messageOffset + i * 64) < 2 ^ 256)]
  omega

private theorem activeWordsAfterUInt256_toNat_eq_succ (s : State)
    (offset size words : Nat) (hsize : 0 < size)
    (hwords : s.activeWords.toNat = words)
    (hlower : words * 32 < offset + size)
    (hupper : offset + size ≤ (words + 1) * 32)
    (hlt : words + 1 < 2 ^ 256) :
    (s.activeWordsAfterUInt256 offset size).toNat = words + 1 := by
  rw [State.activeWordsAfterUInt256]
  unfold MachineState.activeWordsAfter
  rw [if_neg (by omega)]
  dsimp only
  have hquot : (offset + size - 1) / 32 = words := by
    apply Nat.div_eq_of_lt_le
    · omega
    · omega
  rw [hquot, hwords]
  have hmax : words.max (words + 1) = words + 1 := Nat.max_eq_right (by omega)
  rw [hmax]
  rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hlt]

private theorem afterFirstIteration_activeWords_eq
    (s : State) (input : ByteArray) (hfit : CalldataFits input)
    (i j words : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hi : i < Driver.blockCount input) (hj : j < 16)
    (hwords : s.activeWords.toNat = words)
    (hload : Padding.messageOffset + 64 * i + 4 * j + 32 ≤ words * 32)
    (hschedule : 800 + 32 * j + 32 ≤ words * 32) :
    (Schedule.afterFirstIteration s (Driver.messageOffsetWord i)
      returnDest rest j).activeWords =
      s.activeWords := by
  have hloadOffset := messageLoadOffset input hfit i j hi hj
  have hscheduleOffset := scheduleSlot_ofNat j (by omega)
  let loaded := Schedule.afterFirstLoad s (Driver.messageOffsetWord i)
    returnDest rest j
  have hloaded : loaded.activeWords = s.activeWords := by
    unfold loaded Schedule.afterFirstLoad
    apply activeWordsAfterUInt256_eq
    rw [hloadOffset, hwords]
    exact hload
  unfold Schedule.afterFirstIteration Schedule.afterFirstStore
  change (loaded.activeWordsAfterUInt256 (Schedule.scheduleSlot j) 32) = _
  rw [activeWordsAfterUInt256_eq loaded _ _ (by
    rw [hscheduleOffset, hloaded, hwords]
    exact hschedule), hloaded]

private theorem afterFirstIteration_activeWords_succ
    (s : State) (input : ByteArray) (hfit : CalldataFits input)
    (i j words : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hi : i < Driver.blockCount input) (hj : j < 16)
    (hwords : s.activeWords.toNat = words)
    (hlower : words * 32 <
      Padding.messageOffset + 64 * i + 4 * j + 32)
    (hupper : Padding.messageOffset + 64 * i + 4 * j + 32 ≤
      (words + 1) * 32)
    (hschedule : 800 + 32 * j + 32 ≤ (words + 1) * 32)
    (hlt : words + 1 < 2 ^ 256) :
    (Schedule.afterFirstIteration s (Driver.messageOffsetWord i)
      returnDest rest j).activeWords.toNat =
      words + 1 := by
  have hloadOffset := messageLoadOffset input hfit i j hi hj
  have hscheduleOffset := scheduleSlot_ofNat j (by omega)
  let loaded := Schedule.afterFirstLoad s (Driver.messageOffsetWord i)
    returnDest rest j
  have hloaded : loaded.activeWords.toNat = words + 1 := by
    apply activeWordsAfterUInt256_toNat_eq_succ s _ 32 words (by omega)
      hwords
    · simpa [loaded, Schedule.afterFirstLoad, hloadOffset] using hlower
    · simpa [loaded, Schedule.afterFirstLoad, hloadOffset] using hupper
    · exact hlt
  unfold Schedule.afterFirstIteration Schedule.afterFirstStore
  change (loaded.activeWordsAfterUInt256 (Schedule.scheduleSlot j) 32).toNat = _
  rw [activeWordsAfterUInt256_eq loaded _ _ (by
    rw [hscheduleOffset, hloaded]
    exact hschedule), hloaded]

private theorem firstLoopState_nonlast_activeWords
    (s : State) (input : ByteArray) (hfit : CalldataFits input)
    (i : Nat) (hi : i + 1 < Driver.blockCount input)
    (returnDest : UInt256) (rest : List UInt256)
    (hwords : s.activeWords.toNat = 89 + 2 * Driver.blockCount input) :
    (Schedule.firstLoopState s (Driver.messageOffsetWord i)
      returnDest rest 16).activeWords = s.activeWords := by
  have hiter : ∀ j, j ≤ 16 →
      (Schedule.firstLoopState s (Driver.messageOffsetWord i)
        returnDest rest j).activeWords = s.activeWords := by
    intro j hj
    have hpadBlocks := Driver.paddedLength_eq_blockCount input
    induction j with
    | zero => rfl
    | succ j ih =>
        rw [Schedule.firstLoopState]
        have hprev := ih (by omega)
        have hstep := afterFirstIteration_activeWords_eq
          (Schedule.firstLoopState s (Driver.messageOffsetWord i)
            returnDest rest j)
          input hfit i j (89 + 2 * Driver.blockCount input)
          returnDest rest (by omega) (by omega)
          (by rw [hprev, hwords])
          (by have hend := paddedEnd input; omega)
          (by have := blockCount_pos input; omega)
        exact hstep.trans hprev
  exact hiter 16 (by omega)

private theorem firstLoopState_last_activeWords
    (s : State) (input : ByteArray) (hfit : CalldataFits input)
    (returnDest : UInt256) (rest : List UInt256)
    (hwords : s.activeWords.toNat = 89 + 2 * Driver.blockCount input) :
    (Schedule.firstLoopState s
      (Driver.messageOffsetWord (Driver.blockCount input - 1))
      returnDest rest 16).activeWords.toNat =
        90 + 2 * Driver.blockCount input := by
  let blocks := Driver.blockCount input
  let words := 89 + 2 * blocks
  have hblocks : 0 < blocks := by exact blockCount_pos input
  have hi : blocks - 1 < Driver.blockCount input := by
    dsimp only [blocks]
    omega
  have hend : Padding.messageOffset + Padding.paddedLength input.size =
      words * 32 := by
    dsimp only [words, blocks]
    exact paddedEnd input
  have hpadBlocks := Driver.paddedLength_eq_blockCount input
  have hbefore : ∀ j, j ≤ 9 →
      (Schedule.firstLoopState s (Driver.messageOffsetWord (blocks - 1))
        returnDest rest j).activeWords = s.activeWords := by
    intro j hj
    induction j with
    | zero => rfl
    | succ j ih =>
        rw [Schedule.firstLoopState]
        have hprev := ih (by omega)
        have hstep := afterFirstIteration_activeWords_eq
          (Schedule.firstLoopState s (Driver.messageOffsetWord (blocks - 1))
            returnDest rest j)
          input hfit (blocks - 1) j words returnDest rest hi (by omega)
          (by rw [hprev, hwords])
          (by omega)
          (by have := blockCount_pos input; dsimp only [blocks, words]; omega)
        exact hstep.trans hprev
  have hstate9 := hbefore 9 (by omega)
  let q9 := Schedule.firstLoopState s
    (Driver.messageOffsetWord (blocks - 1)) returnDest rest 9
  have hq9 : q9.activeWords.toNat = words := by
    dsimp only [q9]
    rw [hstate9, hwords]
  have hlt : words + 1 < 2 ^ 256 := by
    have hbc : blocks ≤ Padding.paddedLength input.size := by
      dsimp only [blocks, Driver.blockCount]
      exact Nat.div_le_self _ _
    have hpadded := Padding.paddedLength_lt input.size
    unfold CalldataFits at hfit
    dsimp only [words]
    omega
  have hstate10 :
      (Schedule.firstLoopState s
        (Driver.messageOffsetWord (blocks - 1)) returnDest rest 10).activeWords.toNat =
        words + 1 := by
    rw [show 10 = 9 + 1 by omega, Schedule.firstLoopState]
    apply afterFirstIteration_activeWords_succ q9 input hfit
      (blocks - 1) 9 words returnDest rest hi (by omega) hq9
    · omega
    · omega
    · have := blockCount_pos input
      dsimp only [blocks, words]
      omega
    · exact hlt
  have hafter : ∀ k, k ≤ 6 →
      (Schedule.firstLoopState s
        (Driver.messageOffsetWord (blocks - 1)) returnDest rest (10 + k)).activeWords.toNat =
        words + 1 := by
    intro k hk
    induction k with
    | zero => simpa using hstate10
    | succ k ih =>
        rw [show 10 + (k + 1) = (10 + k) + 1 by omega,
          Schedule.firstLoopState]
        let q := Schedule.firstLoopState s
          (Driver.messageOffsetWord (blocks - 1)) returnDest rest (10 + k)
        have hq : q.activeWords.toNat = words + 1 := ih (by omega)
        have hstep := afterFirstIteration_activeWords_eq q input hfit
          (blocks - 1) (10 + k) (words + 1) returnDest rest hi (by omega)
          hq
          (by omega)
          (by have := blockCount_pos input; dsimp only [blocks, words]; omega)
        have := congrArg UInt256.toNat hstep
        simpa [q, hq] using this
  have hfinal := hafter 6 (by omega)
  dsimp only [blocks, words] at hfinal ⊢
  rw [show 10 + 6 = 16 by omega] at hfinal
  omega

private theorem scheduleAfterSecondIteration_activeWords_eq
    (s : State) (msgOff returnDest : UInt256) (rest : List UInt256)
    (j : Nat) (hj16 : 16 ≤ j) (hj64 : j < 64)
    (haw : 89 ≤ s.activeWords.toNat) :
    (Schedule.afterSecondIteration s msgOff returnDest rest j).activeWords =
      s.activeWords := by
  let q16 := Schedule.gotW16 s msgOff returnDest rest j
  have h16 : q16.activeWords = s.activeWords := by
    apply loadReturned_activeWords_eq s 800 (j - 16)
    · omega
    · omega
    · omega
  let q15 := Schedule.gotW15 s msgOff returnDest rest j
  have h15 : q15.activeWords = s.activeWords := by
    have h := loadReturned_activeWords_eq q16 800 (j - 15)
      (UInt256.ofNat 542)
      ([0, UInt256.ofNat 547, Schedule.wValue s (j - 16),
        UInt256.ofNat 0xffffffff, UInt256.ofNat 592, UInt256.ofNat j,
        msgOff, returnDest] ++ rest) (by omega) (by omega) (by rw [h16]; omega)
    simpa [q15, Schedule.gotW15, q16] using h.trans h16
  let q0 := Schedule.gotSsig0 s msgOff returnDest rest j
  have h0 : q0.activeWords = s.activeWords := by
    simpa [q0, Schedule.gotSsig0, q15, Schedule.gotW15,
      Functions.unaryReturned] using h15
  let q7 := Schedule.gotW7 s msgOff returnDest rest j
  have h7 : q7.activeWords = s.activeWords := by
    have h := loadReturned_activeWords_eq q0 800 (j - 7)
      (UInt256.ofNat 561)
      ([Schedule.firstSum s msgOff returnDest rest j,
        UInt256.ofNat 0xffffffff, UInt256.ofNat 592, UInt256.ofNat j,
        msgOff, returnDest] ++ rest) (by omega) (by omega) (by rw [h0]; omega)
    simpa [q7, Schedule.gotW7, q0] using h.trans h0
  let q2 := Schedule.gotW2 s msgOff returnDest rest j
  have h2 : q2.activeWords = s.activeWords := by
    have h := loadReturned_activeWords_eq q7 800 (j - 2)
      (UInt256.ofNat 578)
      ([0, UInt256.ofNat 583, Schedule.wValue q7 (j - 7),
        Schedule.firstSum s msgOff returnDest rest j,
        UInt256.ofNat 0xffffffff, UInt256.ofNat 592, UInt256.ofNat j,
        msgOff, returnDest] ++ rest) (by omega) (by omega) (by rw [h7]; omega)
    simpa [q2, Schedule.gotW2, q7] using h.trans h7
  let q1 := Schedule.gotSsig1 s msgOff returnDest rest j
  have h1 : q1.activeWords = s.activeWords := by
    simpa [q1, Schedule.gotSsig1, q2, Schedule.gotW2,
      Functions.unaryReturned] using h2
  have hset := storeReturned_activeWords_eq q1 800 j
    (Schedule.recurrenceWord s msgOff returnDest rest j) (UInt256.ofNat 592)
    ([UInt256.ofNat j, msgOff, returnDest] ++ rest) hj64 (by omega)
    (by rw [h1]; omega)
  simpa [Schedule.afterSecondIteration, Schedule.secondAt,
    Schedule.gotWSet, q1] using hset.trans h1

private theorem secondLoopState_activeWords_eq (s : State)
    (msgOff returnDest : UInt256) (rest : List UInt256)
    (haw : 89 ≤ s.activeWords.toNat) :
    (Schedule.secondLoopState s msgOff returnDest rest 48).activeWords =
      s.activeWords := by
  have hloop : ∀ n, n ≤ 48 →
      (Schedule.secondLoopState s msgOff returnDest rest n).activeWords =
        s.activeWords := by
    intro n hn
    induction n with
    | zero => rfl
    | succ n ih =>
        rw [Schedule.secondLoopState]
        have hprev := ih (by omega)
        have hstep := scheduleAfterSecondIteration_activeWords_eq
          (Schedule.secondLoopState s msgOff returnDest rest n)
          msgOff returnDest rest (16 + n) (by omega) (by omega)
          (by rw [hprev]; exact haw)
        exact hstep.trans hprev
  exact hloop 48 (by omega)

private theorem loadedE_activeWords_eq (s : State)
    (haw : 89 ≤ s.activeWords.toNat) :
    (Compression.loadedE s).activeWords = s.activeWords := by
  unfold Compression.loadedE
  rw [activeWordsAfterUInt256_eq s 416 32 (by omega)]

private theorem compressionAfterT1_activeWords_eq (s : State)
    (msgOff returnDest : UInt256) (rest : List UInt256) (j : Nat)
    (hj : j < 64) (haw : 89 ≤ s.activeWords.toNat) :
    (Compression.afterT1 s msgOff returnDest rest j).activeWords =
      s.activeWords := by
  have he : (Compression.loadedE s).activeWords = s.activeWords :=
    loadedE_activeWords_eq s haw
  have hw : (Compression.gotW s msgOff returnDest rest j).activeWords =
      s.activeWords := by
    unfold Compression.gotW
    exact (loadReturned_activeWords_eq (Compression.loadedE s) 800 j _ _ hj
      (by omega) (by rw [he]; omega)).trans he
  have hk : (Compression.gotK s msgOff returnDest rest j).activeWords =
      s.activeWords := by
    unfold Compression.gotK
    exact (kAtReturned_activeWords_eq (Compression.gotW s msgOff returnDest rest j)
      j _ _ hj (by rw [hw]; omega)).trans hw
  have hh6 : (Compression.gotH6 s msgOff returnDest rest j).activeWords =
      s.activeWords := by
    unfold Compression.gotH6
    exact (loadReturned_activeWords_eq (Compression.gotK s msgOff returnDest rest j)
      288 6 _ _ (by omega) (by omega) (by rw [hk]; omega)).trans hk
  have hh5 : (Compression.gotH5 s msgOff returnDest rest j).activeWords =
      s.activeWords := by
    unfold Compression.gotH5
    exact (loadReturned_activeWords_eq (Compression.gotH6 s msgOff returnDest rest j)
      288 5 _ _ (by omega) (by omega) (by rw [hh6]; omega)).trans hh6
  have hch : (Compression.gotCh s msgOff returnDest rest j).activeWords =
      s.activeWords := by
    simpa [Compression.gotCh, Functions.unaryReturned] using hh5
  have hs1 : (Compression.gotBigSigma1 s msgOff returnDest rest j).activeWords =
      s.activeWords := by
    simpa [Compression.gotBigSigma1, Functions.unaryReturned] using hch
  have hh7 : (Compression.gotH7 s msgOff returnDest rest j).activeWords =
      s.activeWords := by
    unfold Compression.gotH7
    exact (loadReturned_activeWords_eq
      (Compression.gotBigSigma1 s msgOff returnDest rest j) 288 7 _ _
      (by omega) (by omega) (by rw [hs1]; omega)).trans hs1
  simpa [Compression.afterT1] using hh7

private theorem compressionAfterT2_activeWords_eq (s : State)
    (msgOff returnDest : UInt256) (rest : List UInt256) (j : Nat)
    (hj : j < 64) (haw : 89 ≤ s.activeWords.toNat) :
    (Compression.afterT2 s msgOff returnDest rest j).activeWords =
      s.activeWords := by
  have ht1 := compressionAfterT1_activeWords_eq s msgOff returnDest rest j hj haw
  have ha : (Compression.loadedA s msgOff returnDest rest j).activeWords =
      s.activeWords := by
    unfold Compression.loadedA
    rw [activeWordsAfterUInt256_eq _ 288 32 (by rw [ht1]; omega), ht1]
  have hh2 : (Compression.gotT2H2 s msgOff returnDest rest j).activeWords =
      s.activeWords := by
    unfold Compression.gotT2H2
    exact (loadReturned_activeWords_eq
      (Compression.loadedA s msgOff returnDest rest j) 288 2 _ _
      (by omega) (by omega) (by rw [ha]; omega)).trans ha
  have hh1 : (Compression.gotT2H1 s msgOff returnDest rest j).activeWords =
      s.activeWords := by
    unfold Compression.gotT2H1
    exact (loadReturned_activeWords_eq
      (Compression.gotT2H2 s msgOff returnDest rest j) 288 1 _ _
      (by omega) (by omega) (by rw [hh2]; omega)).trans hh2
  have hmaj : (Compression.gotMaj s msgOff returnDest rest j).activeWords =
      s.activeWords := by
    simpa [Compression.gotMaj, Functions.unaryReturned] using hh1
  have hs0 : (Compression.gotBigSigma0 s msgOff returnDest rest j).activeWords =
      s.activeWords := by
    simpa [Compression.gotBigSigma0, Functions.unaryReturned] using hmaj
  simpa [Compression.afterT2] using hs0

private theorem directStored_activeWords_eq (s : State) (offset : Nat)
    (value : UInt256) (nextPC : Nat) (context : List UInt256)
    (hend : offset + 32 ≤ s.activeWords.toNat * 32) :
    (Compression.directStored s offset value nextPC context).activeWords =
      s.activeWords := by
  unfold Compression.directStored
  rw [activeWordsAfterUInt256_eq s offset 32 hend]

private theorem shiftReturned_activeWords_eq (s : State)
    (src dest loadReturn storeReturn : Nat) (context : List UInt256)
    (hsrc : src < 8) (hdest : dest < 8)
    (haw : 89 ≤ s.activeWords.toNat) :
    (Compression.shiftReturned s src dest loadReturn storeReturn context).activeWords =
      s.activeWords := by
  let loaded := Compression.shiftLoaded s src loadReturn storeReturn context
  have hl : loaded.activeWords = s.activeWords := by
    unfold loaded Compression.shiftLoaded
    apply loadReturned_activeWords_eq s 288 src
    · omega
    · omega
    · omega
  unfold Compression.shiftReturned
  exact (storeReturned_activeWords_eq loaded 288 dest _ _ _ (by omega)
    (by omega) (by rw [hl]; omega)).trans hl

private theorem compressionAfterRound_activeWords_eq (s : State)
    (msgOff returnDest : UInt256) (rest : List UInt256) (j : Nat)
    (hj : j < 64) (haw : 89 ≤ s.activeWords.toNat) :
    (Compression.afterSecondIteration s msgOff returnDest rest j).activeWords =
      s.activeWords := by
  have ht2 := compressionAfterT2_activeWords_eq s msgOff returnDest rest j hj haw
  have h7 : (Compression.afterShift7 s msgOff returnDest rest j).activeWords =
      s.activeWords := by
    unfold Compression.afterShift7
    exact (shiftReturned_activeWords_eq
      (Compression.afterT2 s msgOff returnDest rest j) 6 7 _ _ _
      (by omega) (by omega) (by rw [ht2]; exact haw)).trans ht2
  have h6 : (Compression.afterShift6 s msgOff returnDest rest j).activeWords =
      s.activeWords := by
    unfold Compression.afterShift6
    exact (shiftReturned_activeWords_eq
      (Compression.afterShift7 s msgOff returnDest rest j) 5 6 _ _ _
      (by omega) (by omega) (by rw [h7]; exact haw)).trans h7
  have he : (Compression.afterStoreE s msgOff returnDest rest j).activeWords =
      s.activeWords := by
    unfold Compression.afterStoreE
    exact (directStored_activeWords_eq
      (Compression.afterShift6 s msgOff returnDest rest j) 448 _ _ _
      (by rw [h6]; omega)).trans h6
  have hl4 : (Compression.h4Loaded s msgOff returnDest rest j).activeWords =
      s.activeWords := by
    unfold Compression.h4Loaded
    exact (loadReturned_activeWords_eq
      (Compression.afterStoreE s msgOff returnDest rest j) 288 3 _ _
      (by omega) (by omega) (by rw [he]; omega)).trans he
  have hs4 : (Compression.afterStoreH4 s msgOff returnDest rest j).activeWords =
      s.activeWords := by
    unfold Compression.afterStoreH4
    exact (storeReturned_activeWords_eq
      (Compression.h4Loaded s msgOff returnDest rest j) 288 4 _ _ _
      (by omega) (by omega) (by rw [hl4]; omega)).trans hl4
  have h3 : (Compression.afterShift3 s msgOff returnDest rest j).activeWords =
      s.activeWords := by
    unfold Compression.afterShift3
    exact (shiftReturned_activeWords_eq
      (Compression.afterStoreH4 s msgOff returnDest rest j) 2 3 _ _ _
      (by omega) (by omega) (by rw [hs4]; exact haw)).trans hs4
  have h2 : (Compression.afterShift2 s msgOff returnDest rest j).activeWords =
      s.activeWords := by
    unfold Compression.afterShift2
    exact (shiftReturned_activeWords_eq
      (Compression.afterShift3 s msgOff returnDest rest j) 1 2 _ _ _
      (by omega) (by omega) (by rw [h3]; exact haw)).trans h3
  have h1 : (Compression.afterStoreH1 s msgOff returnDest rest j).activeWords =
      s.activeWords := by
    unfold Compression.afterStoreH1
    exact (directStored_activeWords_eq
      (Compression.afterShift2 s msgOff returnDest rest j) 320 _ _ _
      (by rw [h2]; omega)).trans h2
  let q := Compression.afterStoreH1 s msgOff returnDest rest j
  unfold Compression.afterSecondIteration
  change (q.activeWordsAfterUInt256 288 32) = _
  rw [activeWordsAfterUInt256_eq q 288 32 (by rw [h1]; omega), h1]

private theorem roundLoopState_activeWords_eq (s : State)
    (msgOff returnDest : UInt256) (rest : List UInt256)
    (haw : 89 ≤ s.activeWords.toNat) :
    (Compression.roundLoopState s msgOff returnDest rest 64).activeWords =
      s.activeWords := by
  have hloop : ∀ n, n ≤ 64 →
      (Compression.roundLoopState s msgOff returnDest rest n).activeWords =
        s.activeWords := by
    intro n hn
    induction n with
    | zero => rfl
    | succ n ih =>
        rw [Compression.roundLoopState]
        have hprev := ih (by omega)
        exact (compressionAfterRound_activeWords_eq
          (Compression.roundLoopState s msgOff returnDest rest n)
          msgOff returnDest rest n (by omega)
          (by rw [hprev]; exact haw)).trans hprev
  exact hloop 64 (by omega)

private theorem compressionAfterFoldIteration_activeWords_eq
    (s : State) (msgOff returnDest : UInt256) (rest : List UInt256)
    (i : Nat) (hi : i < 8) (haw : 89 ≤ s.activeWords.toNat) :
    (Compression.afterFoldIteration s msgOff returnDest rest i).activeWords =
      s.activeWords := by
  have hsaved : (Compression.loadedSaved s i).activeWords = s.activeWords := by
    unfold Compression.loadedSaved Compression.savedOffset
    rw [Challenge.EvmProof.Word.shiftLeft_ofNat (by omega) (by decide)
      (by omega : i * 2 ^ 5 < 2 ^ 256)]
    rw [show i * 2 ^ 5 = 32 * i by omega]
    rw [Challenge.EvmProof.Word.ofNat_add_ofNat (by omega)]
    rw [Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : 32 * i + 544 < 2 ^ 256)]
    rw [activeWordsAfterUInt256_eq s _ 32 (by omega)]
  have hh : (Compression.foldGotH s msgOff returnDest rest i).activeWords =
      s.activeWords := by
    unfold Compression.foldGotH
    exact (loadReturned_activeWords_eq (Compression.loadedSaved s i) 288 i _ _
      (by omega) (by omega) (by rw [hsaved]; omega)).trans hsaved
  have hset : (Compression.foldGotSet s msgOff returnDest rest i).activeWords =
      s.activeWords := by
    unfold Compression.foldGotSet
    exact (storeReturned_activeWords_eq
      (Compression.foldGotH s msgOff returnDest rest i) 288 i _ _ _
      (by omega) (by omega) (by rw [hh]; omega)).trans hh
  simpa [Compression.afterFoldIteration] using hset

private theorem foldLoopState_activeWords_eq (s : State)
    (msgOff returnDest : UInt256) (rest : List UInt256)
    (haw : 89 ≤ s.activeWords.toNat) :
    (Compression.foldLoopState s msgOff returnDest rest 8).activeWords =
      s.activeWords := by
  have hloop : ∀ n, n ≤ 8 →
      (Compression.foldLoopState s msgOff returnDest rest n).activeWords =
        s.activeWords := by
    intro n hn
    induction n with
    | zero => rfl
    | succ n ih =>
        rw [Compression.foldLoopState]
        have hprev := ih (by omega)
        exact (compressionAfterFoldIteration_activeWords_eq
          (Compression.foldLoopState s msgOff returnDest rest n)
          msgOff returnDest rest n (by omega)
          (by rw [hprev]; exact haw)).trans hprev
  exact hloop 8 (by omega)

private theorem copyHashState_activeWords_eq (s : State)
    (haw : 89 ≤ s.activeWords.toNat) :
    (Compression.copyHashState s).activeWords = s.activeWords := by
  unfold Compression.copyHashState State.activeWordsAfterUInt256_2
  have hfirst : MachineState.activeWordsAfter s.activeWords.toNat 544 256 =
      s.activeWords.toNat := activeWordsAfter_eq_of_end_le _ _ _ (by omega)
  rw [hfirst, activeWordsAfter_eq_of_end_le _ 288 256 (by omega), ofNat_toNat]

private theorem afterSchedule_activeWords_eq_firstLoop
    (s : State) (msgOff returnDest : UInt256) (rest : List UInt256)
    (haw : 89 ≤ (Schedule.firstLoopState s msgOff (UInt256.ofNat 621)
      (msgOff :: returnDest :: rest) 16).activeWords.toNat) :
    (Compression.afterSchedule s msgOff returnDest rest).activeWords =
      (Schedule.firstLoopState s msgOff (UInt256.ofNat 621)
        (msgOff :: returnDest :: rest) 16).activeWords := by
  let q1 := Schedule.firstLoopState s msgOff (UInt256.ofNat 621)
    (msgOff :: returnDest :: rest) 16
  have hsecond := secondLoopState_activeWords_eq q1 msgOff
    (UInt256.ofNat 621) (msgOff :: returnDest :: rest) haw
  simpa [Compression.afterSchedule, Schedule.scheduleResult,
    Schedule.scheduleReturned, q1] using hsecond

private theorem compressResult_activeWords_eq_firstLoop
    (s : State) (msgOff returnDest : UInt256) (rest : List UInt256)
    (haw : 89 ≤ (Schedule.firstLoopState s msgOff (UInt256.ofNat 621)
      (msgOff :: returnDest :: rest) 16).activeWords.toNat) :
    (Compression.compressResult s msgOff returnDest rest).activeWords =
      (Schedule.firstLoopState s msgOff (UInt256.ofNat 621)
        (msgOff :: returnDest :: rest) 16).activeWords := by
  let first := Schedule.firstLoopState s msgOff (UInt256.ofNat 621)
    (msgOff :: returnDest :: rest) 16
  let scheduled := Compression.afterSchedule s msgOff returnDest rest
  have hs : scheduled.activeWords = first.activeWords := by
    exact afterSchedule_activeWords_eq_firstLoop s msgOff returnDest rest haw
  let prepared := Compression.copyHashState scheduled
  have hp : prepared.activeWords = first.activeWords := by
    exact (copyHashState_activeWords_eq scheduled (by rw [hs]; exact haw)).trans hs
  let rounded := Compression.roundLoopState prepared msgOff returnDest rest 64
  have hr : rounded.activeWords = first.activeWords := by
    exact (roundLoopState_activeWords_eq prepared msgOff returnDest rest
      (by rw [hp]; exact haw)).trans hp
  let folded := Compression.foldLoopState rounded msgOff returnDest rest 8
  have hf : folded.activeWords = first.activeWords := by
    exact (foldLoopState_activeWords_eq rounded msgOff returnDest rest
      (by rw [hr]; exact haw)).trans hr
  simpa [Compression.compressResult, Compression.compressReturned,
    first, scheduled, prepared, rounded, folded] using hf

private theorem afterCompression_nonlast_activeWords (s : State)
    (input : ByteArray) (hfit : CalldataFits input) (i : Nat)
    (hi : i + 1 < Driver.blockCount input)
    (hwords : s.activeWords.toNat = 89 + 2 * Driver.blockCount input) :
    (Driver.afterCompression s input i).activeWords = s.activeWords := by
  let q := Driver.loopAt s input i
  have hq : q.activeWords = s.activeWords := rfl
  have hfirst := firstLoopState_nonlast_activeWords q input hfit i hi
    (UInt256.ofNat 621)
    (Driver.messageOffsetWord i :: UInt256.ofNat 1390 ::
      [Driver.blockOffsetWord i, Padding.paddedWord input])
    (by simpa [q, Driver.loopAt] using hwords)
  have hremain := compressResult_activeWords_eq_firstLoop q
    (Driver.messageOffsetWord i) (UInt256.ofNat 1390)
    [Driver.blockOffsetWord i, Padding.paddedWord input]
    (by rw [hfirst, hq, hwords]; have := blockCount_pos input; omega)
  unfold Driver.afterCompression
  exact hremain.trans (hfirst.trans hq)

private theorem afterCompression_last_activeWords (s : State)
    (input : ByteArray) (hfit : CalldataFits input)
    (hwords : s.activeWords.toNat = 89 + 2 * Driver.blockCount input) :
    (Driver.afterCompression s input (Driver.blockCount input - 1)).activeWords.toNat =
      90 + 2 * Driver.blockCount input := by
  let i := Driver.blockCount input - 1
  let q := Driver.loopAt s input i
  have hfirst := firstLoopState_last_activeWords q input hfit
    (UInt256.ofNat 621)
    (Driver.messageOffsetWord i :: UInt256.ofNat 1390 ::
      [Driver.blockOffsetWord i, Padding.paddedWord input])
    (by simpa [q, Driver.loopAt] using hwords)
  have hremain := compressResult_activeWords_eq_firstLoop q
    (Driver.messageOffsetWord i) (UInt256.ofNat 1390)
    [Driver.blockOffsetWord i, Padding.paddedWord input]
    (by rw [hfirst]; omega)
  have h := congrArg UInt256.toNat hremain
  unfold Driver.afterCompression
  dsimp only [i] at h ⊢
  rw [h, hfirst]

private theorem blockLoopState_beforeLast_activeWords (input : ByteArray)
    (hfit : CalldataFits input) (i : Nat) (hi : i < Driver.blockCount input) :
    (Driver.blockLoopState input i).activeWords.toNat =
      89 + 2 * Driver.blockCount input := by
  induction i with
  | zero => exact blockLoopState_zero_activeWords input hfit
  | succ i ih =>
      rw [Driver.blockLoopState]
      have hprev := ih (by omega)
      have hcompress := afterCompression_nonlast_activeWords
        (Driver.blockLoopState input i) input hfit i hi hprev
      change (Driver.afterCompression
        (Driver.blockLoopState input i) input i).activeWords.toNat = _
      rw [hcompress, hprev]

theorem blockLoopState_final_activeWords (input : ByteArray)
    (hfit : CalldataFits input) :
    (Driver.blockLoopState input (Driver.blockCount input)).activeWords.toNat =
      90 + 2 * Driver.blockCount input := by
  have hpos := blockCount_pos input
  rw [show Driver.blockCount input = (Driver.blockCount input - 1) + 1 by omega,
    Driver.blockLoopState]
  have hprev := blockLoopState_beforeLast_activeWords input hfit
    (Driver.blockCount input - 1) (by omega)
  change (Driver.afterCompression
    (Driver.blockLoopState input (Driver.blockCount input - 1)) input
    (Driver.blockCount input - 1)).activeWords.toNat = _
  convert afterCompression_last_activeWords
    (Driver.blockLoopState input (Driver.blockCount input - 1)) input hfit hprev using 1
  all_goals omega

theorem blockLoopState_final_activeWords_ge_seventeen (input : ByteArray)
    (hfit : CalldataFits input) :
    17 ≤ (Driver.blockLoopState input (Driver.blockCount input)).activeWords.toNat := by
  rw [blockLoopState_final_activeWords input hfit]
  omega

end Challenge.Sha256.Reference.Proofs.Bytecode.DriverMemory
