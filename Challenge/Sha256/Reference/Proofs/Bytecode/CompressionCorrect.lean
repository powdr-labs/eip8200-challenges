import Challenge.Sha256.Reference.Proofs.Bytecode.Compression
import Challenge.Sha256.Reference.Proofs.Bytecode.ScheduleCorrect
import Challenge.Sha256.Reference.Proofs.Bytecode.InitializationCorrect
import Challenge.Sha256.Reference.Proofs.Bytecode.HashSpecBridge

set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

/-!
# Functional correctness of direct SHA-256 compression

This file is deliberately separate from symbolic execution.  It states the
round invariant using eight `UInt32` values, so another bytecode proof can
reuse the same functional target without adopting the reference program's
basic blocks or calling convention.
-/

namespace Challenge.Sha256.Reference.Proofs.Bytecode.CompressionCorrect

open EvmSemantics
open EvmSemantics.Crypto
open EvmSemantics.EVM

/-- The eight SHA-256 working variables, in `a` through `h` order. -/
structure Working where
  a : UInt32
  b : UInt32
  c : UInt32
  d : UInt32
  e : UInt32
  f : UInt32
  g : UInt32
  h : UInt32
deriving DecidableEq

/-- One mathematical SHA-256 compression round. -/
def round (x : Working) (k w : UInt32) : Working :=
  let t1 := x.h + Sha256.bigSigma1 x.e + Sha256.Ch x.e x.f x.g + k + w
  let t2 := Sha256.bigSigma0 x.a + Sha256.Maj x.a x.b x.c
  { a := t1 + t2, b := x.a, c := x.b, d := x.c
    e := x.d + t1, f := x.e, g := x.f, h := x.g }

/-- The bytecode's working-memory region represents `x`. -/
def Represents (s : State) (x : Working) : Prop :=
  Compression.hValue s 0 = Challenge.EvmProof.Word.ofUInt32 x.a ∧
  Compression.hValue s 1 = Challenge.EvmProof.Word.ofUInt32 x.b ∧
  Compression.hValue s 2 = Challenge.EvmProof.Word.ofUInt32 x.c ∧
  Compression.hValue s 3 = Challenge.EvmProof.Word.ofUInt32 x.d ∧
  Compression.hValue s 4 = Challenge.EvmProof.Word.ofUInt32 x.e ∧
  Compression.hValue s 5 = Challenge.EvmProof.Word.ofUInt32 x.f ∧
  Compression.hValue s 6 = Challenge.EvmProof.Word.ofUInt32 x.g ∧
  Compression.hValue s 7 = Challenge.EvmProof.Word.ofUInt32 x.h

private theorem mask32_add_distrib (x y : UInt256) :
    Challenge.EvmProof.Word.mask32 (x + y) =
      Challenge.EvmProof.Word.mask32
        (Challenge.EvmProof.Word.mask32 x + Challenge.EvmProof.Word.mask32 y) := by
  rw [Challenge.EvmProof.Word.mask32_eq_ofUInt32,
    Challenge.EvmProof.Word.mask32_eq_ofUInt32 x,
    Challenge.EvmProof.Word.mask32_eq_ofUInt32 y,
    Challenge.EvmProof.Word.mask32_add]
  congr 1
  apply UInt32.toNat_inj.mp
  simp only [Challenge.EvmProof.Word.toUInt32_toNat, UInt32.toNat_add]
  change ((x.val + y.val).val % 2 ^ 32) =
    (x.toNat % 2 ^ 32 + y.toNat % 2 ^ 32) % 2 ^ 32
  rw [Fin.val_add]
  change ((x.toNat + y.toNat) % UInt256.size) % 2 ^ 32 = _
  rw [show UInt256.size = 2 ^ 256 by rfl,
    Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega)), Nat.add_mod]

private theorem toUInt32_add (x y : UInt256) :
    Challenge.EvmProof.Word.toUInt32 (x + y) =
      Challenge.EvmProof.Word.toUInt32 x + Challenge.EvmProof.Word.toUInt32 y := by
  apply UInt32.toNat_inj.mp
  simp only [Challenge.EvmProof.Word.toUInt32_toNat, UInt32.toNat_add]
  change ((x.val + y.val).val % 2 ^ 32) =
    (x.toNat % 2 ^ 32 + y.toNat % 2 ^ 32) % 2 ^ 32
  rw [Fin.val_add]
  change ((x.toNat + y.toNat) % UInt256.size) % 2 ^ 32 = _
  rw [show UInt256.size = 2 ^ 256 by rfl,
    Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega)), Nat.add_mod]

theorem t1_eq (s : State) (j : Nat) (x : Working) (k w : UInt32)
    (hx : Represents s x)
    (hk : Compression.kValue s j = Challenge.EvmProof.Word.ofUInt32 k)
    (hw : Compression.wValue s j = Challenge.EvmProof.Word.ofUInt32 w) :
    Compression.t1 s j = Challenge.EvmProof.Word.ofUInt32
      (x.h + Sha256.bigSigma1 x.e + Sha256.Ch x.e x.f x.g + k + w) := by
  rcases hx with ⟨ha, hb, hc, hd, he, hf, hg, hh⟩
  unfold Compression.t1 Compression.chPlusK
  rw [he, hf, hg, hh, hk, hw, Word.evmBigSigma1_ofUInt32,
    Word.evmCh_ofUInt32]
  rw [Challenge.EvmProof.Word.mask32_eq_ofUInt32]
  congr 1
  simp only [toUInt32_add, Challenge.EvmProof.Word.toUInt32_ofUInt32]
  ac_rfl

theorem t2_eq (s : State) (x : Working) (hx : Represents s x) :
    Compression.t2 s = Challenge.EvmProof.Word.ofUInt32
      (Sha256.bigSigma0 x.a + Sha256.Maj x.a x.b x.c) := by
  rcases hx with ⟨ha, hb, hc, hd, he, hf, hg, hh⟩
  unfold Compression.t2
  rw [ha, hb, hc, Word.evmBigSigma0_ofUInt32, Word.evmMaj_ofUInt32,
    Challenge.EvmProof.Word.mask32_add]

private theorem hSlot_eq (i : Nat) (hi : i < 8) :
    Accessors.slotOffset 288 (UInt256.ofNat i) = 288 + i * 32 := by
  unfold Accessors.slotOffset
  rw [Challenge.EvmProof.Word.shiftLeft_ofNat (by omega) (by decide) (by omega)]
  rw [Challenge.EvmProof.Word.ofNat_add_ofNat (by omega),
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  omega

private def writeH (memory : ByteArray) (i : Nat) (value : UInt256) : ByteArray :=
  MachineState.writeBytes memory
    (Data.Bytes.natToBytesPadded value.toNat 32) (288 + i * 32)

private theorem readH_writeH_same (memory : ByteArray) (i : Nat)
    (value : UInt256) :
    MachineState.readWord (writeH memory i value) (288 + i * 32) = value := by
  exact Challenge.EvmProof.Memory.readWord_writeWord memory (288 + i * 32) value

private theorem readH_writeH_ne (memory : ByteArray) (read write : Nat)
    (value : UInt256) (hne : read ≠ write) :
    MachineState.readWord (writeH memory write value) (288 + read * 32) =
      MachineState.readWord memory (288 + read * 32) := by
  apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
  have hsize : (Data.Bytes.natToBytesPadded value.toNat 32).size = 32 := by
    simp [Data.Bytes.natToBytesPadded, ByteArray.size]
  rw [hsize]
  by_cases hlt : read < write
  · left
    omega
  · right
    omega

private theorem hValue_eq_readH (s : State) (i : Nat) (hi : i < 8) :
    Compression.hValue s i = MachineState.readWord s.memory (288 + i * 32) := by
  unfold Compression.hValue
  rw [hSlot_eq i hi]

private theorem hValue_of_write_same (before after : State) (i : Nat)
    (hi : i < 8) (value : UInt256)
    (hmemory : after.memory = writeH before.memory i value) :
    Compression.hValue after i = value := by
  rw [hValue_eq_readH after i hi, hmemory, readH_writeH_same]

private theorem hValue_of_write_ne (before after : State) (read write : Nat)
    (hread : read < 8) (hne : read ≠ write) (value : UInt256)
    (hmemory : after.memory = writeH before.memory write value) :
    Compression.hValue after read = Compression.hValue before read := by
  rw [hValue_eq_readH after read hread, hmemory,
    readH_writeH_ne _ _ _ _ hne, ← hValue_eq_readH before read hread]

private theorem shiftReturned_memory (q : State) (src dest loadReturn storeReturn : Nat)
    (context : List UInt256) (hdest : dest < 8) :
    (Compression.shiftReturned q src dest loadReturn storeReturn context).memory =
      writeH q.memory dest (Compression.hValue q src) := by
  unfold Compression.shiftReturned Compression.shiftLoaded
  unfold Accessors.storeReturned Accessors.loadReturned writeH
  rw [hSlot_eq dest hdest]

private theorem directStored_memory (q : State) (dest : Nat) (value : UInt256)
    (nextPC : Nat) (context : List UInt256) :
    (Compression.directStored q (288 + dest * 32) value nextPC context).memory =
      writeH q.memory dest value := by
  rfl

private theorem afterShift7_memory (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) :
    (Compression.afterShift7 s msgOff returnDest rest j).memory =
      writeH (Compression.afterT2 s msgOff returnDest rest j).memory 7
        (Compression.hValue (Compression.afterT2 s msgOff returnDest rest j) 6) := by
  exact shiftReturned_memory _ _ _ _ _ _ (by decide)

private theorem afterShift6_memory (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) :
    (Compression.afterShift6 s msgOff returnDest rest j).memory =
      writeH (Compression.afterShift7 s msgOff returnDest rest j).memory 6
        (Compression.hValue (Compression.afterShift7 s msgOff returnDest rest j) 5) := by
  exact shiftReturned_memory _ _ _ _ _ _ (by decide)

private theorem afterStoreE_memory (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) :
    (Compression.afterStoreE s msgOff returnDest rest j).memory =
      writeH (Compression.afterShift6 s msgOff returnDest rest j).memory 5
        (Compression.hValue s 4) := by
  exact directStored_memory _ 5 _ _ _

private theorem afterStoreH4_memory (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) :
    (Compression.afterStoreH4 s msgOff returnDest rest j).memory =
      writeH (Compression.afterStoreE s msgOff returnDest rest j).memory 4
        (Compression.newH4 s msgOff returnDest rest j) := by
  unfold Compression.afterStoreH4 Compression.h4Loaded
  unfold Accessors.storeReturned Accessors.loadReturned writeH
  rw [hSlot_eq 4 (by decide)]

private theorem afterShift3_memory (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) :
    (Compression.afterShift3 s msgOff returnDest rest j).memory =
      writeH (Compression.afterStoreH4 s msgOff returnDest rest j).memory 3
        (Compression.hValue
          (Compression.afterStoreH4 s msgOff returnDest rest j) 2) := by
  exact shiftReturned_memory _ _ _ _ _ _ (by decide)

private theorem afterShift2_memory (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) :
    (Compression.afterShift2 s msgOff returnDest rest j).memory =
      writeH (Compression.afterShift3 s msgOff returnDest rest j).memory 2
        (Compression.hValue (Compression.afterShift3 s msgOff returnDest rest j) 1) := by
  exact shiftReturned_memory _ _ _ _ _ _ (by decide)

private theorem afterStoreH1_memory (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) :
    (Compression.afterStoreH1 s msgOff returnDest rest j).memory =
      writeH (Compression.afterShift2 s msgOff returnDest rest j).memory 1
        (Compression.hValue s 0) := by
  exact directStored_memory _ 1 _ _ _

private theorem afterSecondIteration_memory (s : State)
    (msgOff returnDest : UInt256) (rest : List UInt256) (j : Nat) :
    (Compression.afterSecondIteration s msgOff returnDest rest j).memory =
      writeH (Compression.afterStoreH1 s msgOff returnDest rest j).memory 0
        (Challenge.EvmProof.Word.mask32
          (Compression.t1 s j + Compression.t2 s)) := by
  rfl

/-- One complete bytecode round implements the mathematical SHA-256 round.
The schedule word and packed round constant are explicit reusable seams. -/
theorem afterSecondIteration_represents (s : State)
    (msgOff returnDest : UInt256) (rest : List UInt256) (j : Nat)
    (x : Working) (k w : UInt32)
    (hx : Represents s x)
    (hk : Compression.kValue s j = Challenge.EvmProof.Word.ofUInt32 k)
    (hw : Compression.wValue s j = Challenge.EvmProof.Word.ofUInt32 w) :
    Represents (Compression.afterSecondIteration s msgOff returnDest rest j)
      (round x k w) := by
  let qt := Compression.afterT2 s msgOff returnDest rest j
  let q7 := Compression.afterShift7 s msgOff returnDest rest j
  let q6 := Compression.afterShift6 s msgOff returnDest rest j
  let q5 := Compression.afterStoreE s msgOff returnDest rest j
  let q4 := Compression.afterStoreH4 s msgOff returnDest rest j
  let q3 := Compression.afterShift3 s msgOff returnDest rest j
  let q2 := Compression.afterShift2 s msgOff returnDest rest j
  let q1 := Compression.afterStoreH1 s msgOff returnDest rest j
  let q0 := Compression.afterSecondIteration s msgOff returnDest rest j
  have htmem : qt.memory = s.memory := by rfl
  have ht (i : Nat) (hi : i < 8) : Compression.hValue qt i =
      Compression.hValue s i := by
    unfold Compression.hValue
    rw [htmem]
  have hm7 : q7.memory = writeH qt.memory 7 (Compression.hValue qt 6) := by
    simpa [q7, qt] using afterShift7_memory s msgOff returnDest rest j
  have hm6 : q6.memory = writeH q7.memory 6 (Compression.hValue q7 5) := by
    simpa [q6, q7] using afterShift6_memory s msgOff returnDest rest j
  have hm5 : q5.memory = writeH q6.memory 5 (Compression.hValue s 4) := by
    simpa [q5, q6] using afterStoreE_memory s msgOff returnDest rest j
  have hm4 : q4.memory = writeH q5.memory 4
      (Compression.newH4 s msgOff returnDest rest j) := by
    simpa [q4, q5] using afterStoreH4_memory s msgOff returnDest rest j
  have hm3 : q3.memory = writeH q4.memory 3 (Compression.hValue q4 2) := by
    simpa [q3, q4] using afterShift3_memory s msgOff returnDest rest j
  have hm2 : q2.memory = writeH q3.memory 2 (Compression.hValue q3 1) := by
    simpa [q2, q3] using afterShift2_memory s msgOff returnDest rest j
  have hm1 : q1.memory = writeH q2.memory 1 (Compression.hValue s 0) := by
    simpa [q1, q2] using afterStoreH1_memory s msgOff returnDest rest j
  have hm0 : q0.memory = writeH q1.memory 0
      (Challenge.EvmProof.Word.mask32
        (Compression.t1 s j + Compression.t2 s)) := by
    simpa [q0, q1] using afterSecondIteration_memory s msgOff returnDest rest j
  have p7 (i : Nat) (hi : i < 8) (hne : i ≠ 7) :
      Compression.hValue q7 i = Compression.hValue qt i :=
    hValue_of_write_ne qt q7 i 7 hi hne _ hm7
  have p6 (i : Nat) (hi : i < 8) (hne : i ≠ 6) :
      Compression.hValue q6 i = Compression.hValue q7 i :=
    hValue_of_write_ne q7 q6 i 6 hi hne _ hm6
  have p5 (i : Nat) (hi : i < 8) (hne : i ≠ 5) :
      Compression.hValue q5 i = Compression.hValue q6 i :=
    hValue_of_write_ne q6 q5 i 5 hi hne _ hm5
  have p4 (i : Nat) (hi : i < 8) (hne : i ≠ 4) :
      Compression.hValue q4 i = Compression.hValue q5 i :=
    hValue_of_write_ne q5 q4 i 4 hi hne _ hm4
  have p3 (i : Nat) (hi : i < 8) (hne : i ≠ 3) :
      Compression.hValue q3 i = Compression.hValue q4 i :=
    hValue_of_write_ne q4 q3 i 3 hi hne _ hm3
  have p2 (i : Nat) (hi : i < 8) (hne : i ≠ 2) :
      Compression.hValue q2 i = Compression.hValue q3 i :=
    hValue_of_write_ne q3 q2 i 2 hi hne _ hm2
  have p1 (i : Nat) (hi : i < 8) (hne : i ≠ 1) :
      Compression.hValue q1 i = Compression.hValue q2 i :=
    hValue_of_write_ne q2 q1 i 1 hi hne _ hm1
  have p0 (i : Nat) (hi : i < 8) (hne : i ≠ 0) :
      Compression.hValue q0 i = Compression.hValue q1 i :=
    hValue_of_write_ne q1 q0 i 0 hi hne _ hm0
  have hs7 : Compression.hValue q7 7 = Compression.hValue s 6 := by
    rw [hValue_of_write_same qt q7 7 (by decide) _ hm7, ht 6 (by decide)]
  have hs6 : Compression.hValue q6 6 = Compression.hValue s 5 := by
    rw [hValue_of_write_same q7 q6 6 (by decide) _ hm6,
      p7 5 (by decide) (by decide), ht 5 (by decide)]
  have hs5 : Compression.hValue q5 5 = Compression.hValue s 4 := by
    exact hValue_of_write_same q6 q5 5 (by decide) _ hm5
  have hs3 : Compression.hValue q3 3 = Compression.hValue s 2 := by
    rw [hValue_of_write_same q4 q3 3 (by decide) _ hm3,
      p4 2 (by decide) (by decide), p5 2 (by decide) (by decide),
      p6 2 (by decide) (by decide), p7 2 (by decide) (by decide),
      ht 2 (by decide)]
  have hs2 : Compression.hValue q2 2 = Compression.hValue s 1 := by
    rw [hValue_of_write_same q3 q2 2 (by decide) _ hm2,
      p3 1 (by decide) (by decide), p4 1 (by decide) (by decide),
      p5 1 (by decide) (by decide), p6 1 (by decide) (by decide),
      p7 1 (by decide) (by decide), ht 1 (by decide)]
  have hs1 : Compression.hValue q1 1 = Compression.hValue s 0 := by
    exact hValue_of_write_same q2 q1 1 (by decide) _ hm1
  have hq5d : Compression.hValue q5 3 = Compression.hValue s 3 := by
    rw [p5 3 (by decide) (by decide), p6 3 (by decide) (by decide),
      p7 3 (by decide) (by decide), ht 3 (by decide)]
  have ht1 := t1_eq s j x k w hx hk hw
  have ht2 := t2_eq s x hx
  let T1 := x.h + Sha256.bigSigma1 x.e + Sha256.Ch x.e x.f x.g + k + w
  let T2 := Sha256.bigSigma0 x.a + Sha256.Maj x.a x.b x.c
  have hnewA : Challenge.EvmProof.Word.mask32
      (Compression.t1 s j + Compression.t2 s) =
      Challenge.EvmProof.Word.ofUInt32 (T1 + T2) := by
    rw [ht1, ht2, Challenge.EvmProof.Word.mask32_add]
  have hnewE : Compression.newH4 s msgOff returnDest rest j =
      Challenge.EvmProof.Word.ofUInt32 (x.d + T1) := by
    unfold Compression.newH4
    change Challenge.EvmProof.Word.mask32
      (Compression.hValue q5 3 + Compression.t1 s j) = _
    rw [hq5d]
    rcases hx with ⟨ha, hb, hc, hd, he, hf, hg, hh⟩
    rw [hd, ht1, Challenge.EvmProof.Word.mask32_add]
  have hs4 : Compression.hValue q4 4 =
      Challenge.EvmProof.Word.ofUInt32 (x.d + T1) := by
    rw [hValue_of_write_same q5 q4 4 (by decide) _ hm4, hnewE]
  rcases hx with ⟨ha, hb, hc, hd, he, hf, hg, hh⟩
  unfold Represents round
  dsimp only [T1, T2]
  constructor
  · rw [show Compression.afterSecondIteration s msgOff returnDest rest j = q0 by rfl]
    rw [hValue_of_write_same q1 q0 0 (by decide) _ hm0, hnewA]
  constructor
  · rw [show Compression.afterSecondIteration s msgOff returnDest rest j = q0 by rfl,
      p0 1 (by decide) (by decide), hs1, ha]
  constructor
  · rw [show Compression.afterSecondIteration s msgOff returnDest rest j = q0 by rfl,
      p0 2 (by decide) (by decide), p1 2 (by decide) (by decide), hs2, hb]
  constructor
  · rw [show Compression.afterSecondIteration s msgOff returnDest rest j = q0 by rfl,
      p0 3 (by decide) (by decide), p1 3 (by decide) (by decide),
      p2 3 (by decide) (by decide), hs3, hc]
  constructor
  · rw [show Compression.afterSecondIteration s msgOff returnDest rest j = q0 by rfl,
      p0 4 (by decide) (by decide), p1 4 (by decide) (by decide),
      p2 4 (by decide) (by decide), p3 4 (by decide) (by decide), hs4]
  constructor
  · rw [show Compression.afterSecondIteration s msgOff returnDest rest j = q0 by rfl,
      p0 5 (by decide) (by decide), p1 5 (by decide) (by decide),
      p2 5 (by decide) (by decide), p3 5 (by decide) (by decide),
      p4 5 (by decide) (by decide), hs5, he]
  constructor
  · rw [show Compression.afterSecondIteration s msgOff returnDest rest j = q0 by rfl,
      p0 6 (by decide) (by decide), p1 6 (by decide) (by decide),
      p2 6 (by decide) (by decide), p3 6 (by decide) (by decide),
      p4 6 (by decide) (by decide), p5 6 (by decide) (by decide), hs6, hf]
  · rw [show Compression.afterSecondIteration s msgOff returnDest rest j = q0 by rfl,
      p0 7 (by decide) (by decide), p1 7 (by decide) (by decide),
      p2 7 (by decide) (by decide), p3 7 (by decide) (by decide),
      p4 7 (by decide) (by decide), p5 7 (by decide) (by decide),
      p6 7 (by decide) (by decide), hs7, hg]

/-- Functional working state after `n` SHA-256 rounds. -/
def rounds (initial : Working) (padded : ByteArray) (blockOff : Nat) :
    Nat → Working
  | 0 => initial
  | n + 1 => round (rounds initial padded blockOff n) Sha256.K[n]!
      (ScheduleCorrect.scheduleWord padded blockOff n)

/-- All round-local memory inputs required by the reusable loop theorem. -/
def RoundInputsCorrect (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (padded : ByteArray) (blockOff : Nat) : Prop :=
  ∀ n, n < 64 →
    Compression.kValue
        (Compression.roundLoopState s msgOff returnDest rest n) n =
      Challenge.EvmProof.Word.ofUInt32 Sha256.K[n]! ∧
    Compression.wValue
        (Compression.roundLoopState s msgOff returnDest rest n) n =
      Challenge.EvmProof.Word.ofUInt32
        (ScheduleCorrect.scheduleWord padded blockOff n)

theorem roundLoopState_represents (s : State)
    (msgOff returnDest : UInt256) (rest : List UInt256)
    (padded : ByteArray) (blockOff : Nat) (initial : Working)
    (hinitial : Represents s initial)
    (hinputs : RoundInputsCorrect s msgOff returnDest rest padded blockOff) :
    ∀ n, n ≤ 64 →
      Represents (Compression.roundLoopState s msgOff returnDest rest n)
        (rounds initial padded blockOff n) := by
  intro n hn
  induction n with
  | zero =>
      change Represents s initial
      exact hinitial
  | succ n ih =>
      rw [Compression.roundLoopState, rounds]
      apply afterSecondIteration_represents
      · exact ih (by omega)
      · exact (hinputs n (by omega)).1
      · exact (hinputs n (by omega)).2

private theorem wValue_of_writeH (before after : State) (read write : Nat)
    (hread : read < 64) (hwrite : write < 8) (value : UInt256)
    (hmemory : after.memory = writeH before.memory write value) :
    Compression.wValue after read = Compression.wValue before read := by
  unfold Compression.wValue
  have hoff : Accessors.slotOffset 800 (UInt256.ofNat read) =
      800 + read * 32 := by
    unfold Accessors.slotOffset
    rw [Challenge.EvmProof.Word.shiftLeft_ofNat (by omega) (by decide) (by omega)]
    rw [Challenge.EvmProof.Word.ofNat_add_ofNat (by omega),
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega
  rw [hmemory, hoff]
  apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
  right
  simp [Data.Bytes.natToBytesPadded, ByteArray.size]
  omega

private theorem kOffset_eq (j : Nat) (hj : j < 64) :
    (UInt256.shiftLeft (UInt256.ofNat j) (UInt256.ofNat 2) +
      UInt256.ofNat 32).toNat = 32 + 4 * j := by
  rw [Challenge.EvmProof.Word.shiftLeft_ofNat (by omega) (by decide) (by omega)]
  rw [Challenge.EvmProof.Word.ofNat_add_ofNat (by omega),
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  omega

private theorem readBE32_writeH (memory : ByteArray) (j write : Nat)
    (value : UInt256) (hj : j < 64) :
    Sha256.readBE32 (writeH memory write value) (32 + 4 * j) =
      Sha256.readBE32 memory (32 + 4 * j) := by
  apply HashSpecBridge.readBE32_eq_of_byte
  intro i hi
  let idx := 32 + 4 * j + i
  have hidx : idx < 288 + write * 32 := by
    dsimp only [idx]
    omega
  have hbytes : (Data.Bytes.natToBytesPadded value.toNat 32).size = 32 := by
    simp [Data.Bytes.natToBytesPadded, ByteArray.size]
  by_cases hm : idx < memory.size
  · have hw : idx < (writeH memory write value).size := by
      unfold writeH
      rw [MachineState.writeBytes_size, if_neg (by simp [hbytes]), hbytes]
      omega
    rw [dif_pos hw, dif_pos hm]
    apply congrArg UInt8.toUInt32
    have hg := MachineState.writeBytes_getElem?_getD memory
      (Data.Bytes.natToBytesPadded value.toNat 32) (288 + write * 32) idx
    rw [if_neg (by simp only [hbytes]; omega)] at hg
    change (writeH memory write value)[idx]?.getD 0 = memory[idx]?.getD 0 at hg
    rw [Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hw,
      Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hm] at hg
    exact hg
  · by_cases hw : idx < (writeH memory write value).size
    · rw [dif_pos hw, dif_neg hm]
      have hg := MachineState.writeBytes_getElem?_getD memory
        (Data.Bytes.natToBytesPadded value.toNat 32) (288 + write * 32) idx
      rw [if_neg (by simp only [hbytes]; omega)] at hg
      change (writeH memory write value)[idx]?.getD 0 = memory[idx]?.getD 0 at hg
      rw [Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hw,
        Challenge.EvmProof.Memory.getElem?_getD_eq_zero_of_size_le _ _
          (by omega)] at hg
      simpa using congrArg UInt8.toUInt32 hg
    · rw [dif_neg hw, dif_neg hm]

private theorem kValue_of_writeH (before after : State) (read write : Nat)
    (hread : read < 64) (value : UInt256)
    (hmemory : after.memory = writeH before.memory write value) :
    Compression.kValue after read = Compression.kValue before read := by
  unfold Compression.kValue
  rw [kOffset_eq read hread]
  dsimp only
  rw [hmemory,
    PaddedBlockBridge.shiftRight_readWord_224,
    PaddedBlockBridge.shiftRight_readWord_224,
    readBE32_writeH before.memory read write value hread]

/-- A round mutates only the eight working-state slots; the packed constants
and the 64-word schedule are preserved. -/
theorem afterSecondIteration_preserves_inputs (s : State)
    (msgOff returnDest : UInt256) (rest : List UInt256) (j read : Nat)
    (hread : read < 64) :
    Compression.kValue
        (Compression.afterSecondIteration s msgOff returnDest rest j) read =
        Compression.kValue s read ∧
      Compression.wValue
        (Compression.afterSecondIteration s msgOff returnDest rest j) read =
        Compression.wValue s read := by
  let qt := Compression.afterT2 s msgOff returnDest rest j
  let q7 := Compression.afterShift7 s msgOff returnDest rest j
  let q6 := Compression.afterShift6 s msgOff returnDest rest j
  let q5 := Compression.afterStoreE s msgOff returnDest rest j
  let q4 := Compression.afterStoreH4 s msgOff returnDest rest j
  let q3 := Compression.afterShift3 s msgOff returnDest rest j
  let q2 := Compression.afterShift2 s msgOff returnDest rest j
  let q1 := Compression.afterStoreH1 s msgOff returnDest rest j
  let q0 := Compression.afterSecondIteration s msgOff returnDest rest j
  have htmem : qt.memory = s.memory := by rfl
  have hm7 : q7.memory = writeH qt.memory 7 (Compression.hValue qt 6) := by
    simpa [q7, qt] using afterShift7_memory s msgOff returnDest rest j
  have hm6 : q6.memory = writeH q7.memory 6 (Compression.hValue q7 5) := by
    simpa [q6, q7] using afterShift6_memory s msgOff returnDest rest j
  have hm5 : q5.memory = writeH q6.memory 5 (Compression.hValue s 4) := by
    simpa [q5, q6] using afterStoreE_memory s msgOff returnDest rest j
  have hm4 : q4.memory = writeH q5.memory 4
      (Compression.newH4 s msgOff returnDest rest j) := by
    simpa [q4, q5] using afterStoreH4_memory s msgOff returnDest rest j
  have hm3 : q3.memory = writeH q4.memory 3 (Compression.hValue q4 2) := by
    simpa [q3, q4] using afterShift3_memory s msgOff returnDest rest j
  have hm2 : q2.memory = writeH q3.memory 2 (Compression.hValue q3 1) := by
    simpa [q2, q3] using afterShift2_memory s msgOff returnDest rest j
  have hm1 : q1.memory = writeH q2.memory 1 (Compression.hValue s 0) := by
    simpa [q1, q2] using afterStoreH1_memory s msgOff returnDest rest j
  have hm0 : q0.memory = writeH q1.memory 0
      (Challenge.EvmProof.Word.mask32
        (Compression.t1 s j + Compression.t2 s)) := by
    simpa [q0, q1] using afterSecondIteration_memory s msgOff returnDest rest j
  constructor
  · rw [show Compression.afterSecondIteration s msgOff returnDest rest j = q0 by rfl]
    rw [kValue_of_writeH q1 q0 read 0 hread _ hm0,
      kValue_of_writeH q2 q1 read 1 hread _ hm1,
      kValue_of_writeH q3 q2 read 2 hread _ hm2,
      kValue_of_writeH q4 q3 read 3 hread _ hm3,
      kValue_of_writeH q5 q4 read 4 hread _ hm4,
      kValue_of_writeH q6 q5 read 5 hread _ hm5,
      kValue_of_writeH q7 q6 read 6 hread _ hm6,
      kValue_of_writeH qt q7 read 7 hread _ hm7]
    unfold Compression.kValue
    rw [htmem]
  · rw [show Compression.afterSecondIteration s msgOff returnDest rest j = q0 by rfl]
    rw [wValue_of_writeH q1 q0 read 0 hread (by decide) _ hm0,
      wValue_of_writeH q2 q1 read 1 hread (by decide) _ hm1,
      wValue_of_writeH q3 q2 read 2 hread (by decide) _ hm2,
      wValue_of_writeH q4 q3 read 3 hread (by decide) _ hm3,
      wValue_of_writeH q5 q4 read 4 hread (by decide) _ hm4,
      wValue_of_writeH q6 q5 read 5 hread (by decide) _ hm5,
      wValue_of_writeH q7 q6 read 6 hread (by decide) _ hm6,
      wValue_of_writeH qt q7 read 7 hread (by decide) _ hm7]
    unfold Compression.wValue
    rw [htmem]

theorem roundLoopState_inputs (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (n read : Nat) (hread : read < 64) :
    Compression.kValue
        (Compression.roundLoopState s msgOff returnDest rest n) read =
        Compression.kValue s read ∧
      Compression.wValue
        (Compression.roundLoopState s msgOff returnDest rest n) read =
        Compression.wValue s read := by
  induction n with
  | zero =>
      constructor <;> rfl
  | succ n ih =>
      rw [Compression.roundLoopState]
      have hp := afterSecondIteration_preserves_inputs
        (Compression.roundLoopState s msgOff returnDest rest n)
        msgOff returnDest rest n read hread
      exact ⟨hp.1.trans ih.1, hp.2.trans ih.2⟩

/-- Construct the loop's input invariant from one constant-table invariant and
one completed schedule invariant at loop entry. -/
theorem roundInputsCorrect_of_entry (s : State)
    (msgOff returnDest : UInt256) (rest : List UInt256)
    (padded : ByteArray) (blockOff : Nat)
    (hk : ∀ n, n < 64 → Compression.kValue s n =
      Challenge.EvmProof.Word.ofUInt32 Sha256.K[n]!)
    (hw : ∀ n, n < 64 → Compression.wValue s n =
      Challenge.EvmProof.Word.ofUInt32
        (ScheduleCorrect.scheduleWord padded blockOff n)) :
    RoundInputsCorrect s msgOff returnDest rest padded blockOff := by
  intro n hn
  have hp := roundLoopState_inputs s msgOff returnDest rest n n hn
  exact ⟨hp.1.trans (hk n hn), hp.2.trans (hw n hn)⟩

def Working.get (x : Working) : Nat → UInt32
  | 0 => x.a
  | 1 => x.b
  | 2 => x.c
  | 3 => x.d
  | 4 => x.e
  | 5 => x.f
  | 6 => x.g
  | _ => x.h

theorem represents_get (s : State) (x : Working) (hx : Represents s x)
    (i : Nat) (hi : i < 8) :
    Compression.hValue s i = Challenge.EvmProof.Word.ofUInt32 (x.get i) := by
  rcases hx with ⟨ha, hb, hc, hd, he, hf, hg, hh⟩
  interval_cases i
  · exact ha
  · exact hb
  · exact hc
  · exact hd
  · exact he
  · exact hf
  · exact hg
  · exact hh

/-- Saved pre-round hash words used by the feed-forward loop. -/
def SavedRepresents (s : State) (H : Array UInt32) : Prop :=
  ∀ i, i < 8 → Compression.savedValue s i =
    Challenge.EvmProof.Word.ofUInt32 H[i]!

private theorem savedOffset_eq (i : Nat) (hi : i < 8) :
    Compression.savedOffset i = 544 + i * 32 := by
  unfold Compression.savedOffset
  rw [Challenge.EvmProof.Word.shiftLeft_ofNat (by omega) (by decide) (by omega)]
  rw [Challenge.EvmProof.Word.ofNat_add_ofNat (by omega),
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  omega

private theorem savedValue_of_writeH (before after : State) (read write : Nat)
    (hread : read < 8) (hwrite : write < 8) (value : UInt256)
    (hmemory : after.memory = writeH before.memory write value) :
    Compression.savedValue after read = Compression.savedValue before read := by
  unfold Compression.savedValue
  rw [hmemory, savedOffset_eq read hread]
  apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
  right
  simp [Data.Bytes.natToBytesPadded, ByteArray.size]
  omega

private theorem afterFoldIteration_memory (s : State)
    (msgOff returnDest : UInt256) (rest : List UInt256) (i : Nat)
    (hi : i < 8) :
    (Compression.afterFoldIteration s msgOff returnDest rest i).memory =
      writeH s.memory i
        (Compression.foldedValue s msgOff returnDest rest i) := by
  unfold Compression.afterFoldIteration Compression.foldGotSet
  unfold Compression.foldGotH Compression.loadedSaved
  unfold Accessors.storeReturned Accessors.loadReturned writeH
  rw [hSlot_eq i hi]

theorem foldedValue_eq (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (H : Array UInt32) (x : Working) (i : Nat)
    (hx : Compression.hValue s i =
      Challenge.EvmProof.Word.ofUInt32 (x.get i))
    (hH : Compression.savedValue s i =
      Challenge.EvmProof.Word.ofUInt32 H[i]!) :
    Compression.foldedValue s msgOff returnDest rest i =
      Challenge.EvmProof.Word.ofUInt32 (H[i]! + x.get i) := by
  unfold Compression.foldedValue Compression.loadedSaved
  change Challenge.EvmProof.Word.mask32
    (Compression.hValue s i + Compression.savedValue s i) = _
  rw [hx, hH, Challenge.EvmProof.Word.mask32_add]
  congr 1
  exact UInt32.add_comm _ _

/-- Pointwise invariant after `n` feed-forward stores. -/
def FoldCorrect (s : State) (H : Array UInt32) (x : Working) (n : Nat) : Prop :=
  (∀ i, i < 8 → Compression.hValue s i =
    Challenge.EvmProof.Word.ofUInt32
      (if i < n then H[i]! + x.get i else x.get i)) ∧
  SavedRepresents s H

theorem foldLoopState_correct (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (H : Array UInt32) (x : Working)
    (hx : Represents s x) (hH : SavedRepresents s H) :
    ∀ n, n ≤ 8 →
      FoldCorrect (Compression.foldLoopState s msgOff returnDest rest n) H x n := by
  intro n hn
  induction n with
  | zero =>
      constructor
      · intro i hi
        simp only [Nat.not_lt_zero, if_false]
        change Compression.hValue s i = _
        exact represents_get s x hx i hi
      · intro i hi
        change Compression.savedValue s i = _
        exact hH i hi
  | succ n ih =>
      let q := Compression.foldLoopState s msgOff returnDest rest n
      let q' := Compression.afterFoldIteration q msgOff returnDest rest n
      have hprev := ih (by omega)
      have hm : q'.memory = writeH q.memory n
          (Compression.foldedValue q msgOff returnDest rest n) := by
        simpa [q, q'] using afterFoldIteration_memory q msgOff returnDest rest n
          (by omega)
      have hv : Compression.foldedValue q msgOff returnDest rest n =
          Challenge.EvmProof.Word.ofUInt32 (H[n]! + x.get n) := by
        apply foldedValue_eq q msgOff returnDest rest H x n
        · simpa using hprev.1 n (by omega)
        · exact hprev.2 n (by omega)
      constructor
      · intro i hi
        rw [Compression.foldLoopState]
        change Compression.hValue q' i = _
        by_cases hin : i = n
        · subst i
          rw [hValue_of_write_same q q' n (by omega) _ hm, hv]
          simp
        · rw [hValue_of_write_ne q q' i n hi hin _ hm]
          rw [hprev.1 i hi]
          by_cases hlt : i < n
          · have hlt' : i < n + 1 := by omega
            simp [hlt, hlt']
          · have hlt' : ¬i < n + 1 := by omega
            simp [hlt, hlt']
      · intro i hi
        rw [Compression.foldLoopState]
        change Compression.savedValue q' i = _
        rw [savedValue_of_writeH q q' i n hi (by omega) _ hm]
        exact hprev.2 i hi

theorem afterSecondIteration_preserves_saved (s : State)
    (msgOff returnDest : UInt256) (rest : List UInt256) (j read : Nat)
    (hread : read < 8) :
    Compression.savedValue
        (Compression.afterSecondIteration s msgOff returnDest rest j) read =
      Compression.savedValue s read := by
  let qt := Compression.afterT2 s msgOff returnDest rest j
  let q7 := Compression.afterShift7 s msgOff returnDest rest j
  let q6 := Compression.afterShift6 s msgOff returnDest rest j
  let q5 := Compression.afterStoreE s msgOff returnDest rest j
  let q4 := Compression.afterStoreH4 s msgOff returnDest rest j
  let q3 := Compression.afterShift3 s msgOff returnDest rest j
  let q2 := Compression.afterShift2 s msgOff returnDest rest j
  let q1 := Compression.afterStoreH1 s msgOff returnDest rest j
  let q0 := Compression.afterSecondIteration s msgOff returnDest rest j
  have htmem : qt.memory = s.memory := by rfl
  have hm7 : q7.memory = writeH qt.memory 7 (Compression.hValue qt 6) := by
    simpa [q7, qt] using afterShift7_memory s msgOff returnDest rest j
  have hm6 : q6.memory = writeH q7.memory 6 (Compression.hValue q7 5) := by
    simpa [q6, q7] using afterShift6_memory s msgOff returnDest rest j
  have hm5 : q5.memory = writeH q6.memory 5 (Compression.hValue s 4) := by
    simpa [q5, q6] using afterStoreE_memory s msgOff returnDest rest j
  have hm4 : q4.memory = writeH q5.memory 4
      (Compression.newH4 s msgOff returnDest rest j) := by
    simpa [q4, q5] using afterStoreH4_memory s msgOff returnDest rest j
  have hm3 : q3.memory = writeH q4.memory 3 (Compression.hValue q4 2) := by
    simpa [q3, q4] using afterShift3_memory s msgOff returnDest rest j
  have hm2 : q2.memory = writeH q3.memory 2 (Compression.hValue q3 1) := by
    simpa [q2, q3] using afterShift2_memory s msgOff returnDest rest j
  have hm1 : q1.memory = writeH q2.memory 1 (Compression.hValue s 0) := by
    simpa [q1, q2] using afterStoreH1_memory s msgOff returnDest rest j
  have hm0 : q0.memory = writeH q1.memory 0
      (Challenge.EvmProof.Word.mask32
        (Compression.t1 s j + Compression.t2 s)) := by
    simpa [q0, q1] using afterSecondIteration_memory s msgOff returnDest rest j
  rw [show Compression.afterSecondIteration s msgOff returnDest rest j = q0 by rfl]
  rw [savedValue_of_writeH q1 q0 read 0 hread (by decide) _ hm0,
    savedValue_of_writeH q2 q1 read 1 hread (by decide) _ hm1,
    savedValue_of_writeH q3 q2 read 2 hread (by decide) _ hm2,
    savedValue_of_writeH q4 q3 read 3 hread (by decide) _ hm3,
    savedValue_of_writeH q5 q4 read 4 hread (by decide) _ hm4,
    savedValue_of_writeH q6 q5 read 5 hread (by decide) _ hm5,
    savedValue_of_writeH q7 q6 read 6 hread (by decide) _ hm6,
    savedValue_of_writeH qt q7 read 7 hread (by decide) _ hm7]
  unfold Compression.savedValue
  rw [htmem]

theorem roundLoopState_saved (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (n read : Nat) (hread : read < 8) :
    Compression.savedValue
        (Compression.roundLoopState s msgOff returnDest rest n) read =
      Compression.savedValue s read := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Compression.roundLoopState]
      exact (afterSecondIteration_preserves_saved
        (Compression.roundLoopState s msgOff returnDest rest n)
        msgOff returnDest rest n read hread).trans ih

/-- The normalized eight-word feed-forward result. -/
def feedForward (H : Array UInt32) (x : Working) : Array UInt32 := #[
  H[0]! + x.a, H[1]! + x.b, H[2]! + x.c, H[3]! + x.d,
  H[4]! + x.e, H[5]! + x.f, H[6]! + x.g, H[7]! + x.h]

/-- Complete bytecode-local compression core: 64 rounds followed by all eight
feed-forward stores.  The thin `compressResult` wrapper changes only pc and
stack after this state. -/
theorem compressionCore_words (prepared : State)
    (msgOff returnDest : UInt256) (rest : List UInt256)
    (padded : ByteArray) (blockOff : Nat) (H : Array UInt32)
    (initial : Working)
    (hinitial : Represents prepared initial)
    (hsaved : SavedRepresents prepared H)
    (hinputs : RoundInputsCorrect prepared msgOff returnDest rest
      padded blockOff) :
    ∀ i, i < 8 →
      Compression.hValue
          (Compression.foldLoopState
            (Compression.roundLoopState prepared msgOff returnDest rest 64)
            msgOff returnDest rest 8) i =
        Challenge.EvmProof.Word.ofUInt32
          (H[i]! + (rounds initial padded blockOff 64).get i) := by
  intro i hi
  let afterRounds := Compression.roundLoopState prepared msgOff returnDest rest 64
  have hrounds := roundLoopState_represents prepared msgOff returnDest rest
    padded blockOff initial hinitial hinputs 64 (by omega)
  have hsavedRounds : SavedRepresents afterRounds H := by
    intro k hk
    rw [roundLoopState_saved prepared msgOff returnDest rest 64 k hk]
    exact hsaved k hk
  have hfold := foldLoopState_correct afterRounds msgOff returnDest rest H
    (rounds initial padded blockOff 64) hrounds hsavedRounds 8 (by omega)
  change Compression.hValue
    (Compression.foldLoopState afterRounds msgOff returnDest rest 8) i = _
  rw [hfold.1 i hi, if_pos hi]

private def firstW (padded : ByteArray) (blockOff count : Nat) : Array UInt32 :=
  (List.range' 0 count).foldl
    (fun W i => W.set! i (Sha256.readBE32 padded (blockOff + i * 4)))
    (Array.replicate 64 0)

@[simp] private theorem firstW_size (padded : ByteArray) (blockOff count : Nat) :
    (firstW padded blockOff count).size = 64 := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [firstW, List.range'_concat, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil, Array.set!_eq_setIfInBounds,
        Array.size_setIfInBounds]
      simpa [firstW] using ih

private theorem firstW_get (padded : ByteArray) (blockOff count k : Nat)
    (hcount : count ≤ 16) (hk : k < 64) :
    (firstW padded blockOff count)[k]! =
      if k < count then Sha256.readBE32 padded (blockOff + k * 4) else 0 := by
  induction count with
  | zero =>
      rw [firstW]
      simp only [List.range'_zero, List.foldl_nil]
      rw [getElem!_pos _ k (by simp; exact hk)]
      simp
  | succ count ih =>
      rw [firstW, List.range'_concat, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [show 0 + 1 * count = count by omega]
      change ((firstW padded blockOff count).set! count
        (Sha256.readBE32 padded (blockOff + count * 4)))[k]! = _
      rw [Array.set!_eq_setIfInBounds]
      rw [getElem!_pos _ k (by simpa using hk),
        Array.getElem_setIfInBounds (by simpa using hk)]
      rw [← getElem!_pos (firstW padded blockOff count) k
        (by simpa using hk), ih (by omega)]
      by_cases heq : count = k
      · subst k
        simp
      · by_cases hlt : k < count <;> simp [heq, hlt] <;> omega

private def expandW (padded : ByteArray) (blockOff count : Nat) : Array UInt32 :=
  (List.range' 16 count).foldl
    (fun W t => W.set! t
      (Sha256.smallSigma1 W[t - 2]! + W[t - 7]! +
        Sha256.smallSigma0 W[t - 15]! + W[t - 16]!))
    (firstW padded blockOff 16)

@[simp] private theorem expandW_size (padded : ByteArray) (blockOff count : Nat) :
    (expandW padded blockOff count).size = 64 := by
  induction count with
  | zero => simp [expandW]
  | succ count ih =>
      rw [expandW, List.range'_concat, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil, Array.set!_eq_setIfInBounds,
        Array.size_setIfInBounds]
      simpa [expandW] using ih

private theorem expandW_get (padded : ByteArray) (blockOff count k : Nat)
    (hcount : count ≤ 48) (hk : k < 64) :
    (expandW padded blockOff count)[k]! =
      if k < 16 + count then ScheduleCorrect.scheduleWord padded blockOff k
      else 0 := by
  induction count generalizing k with
  | zero =>
      rw [expandW]
      simp only [List.range'_zero, List.foldl_nil, Nat.add_zero]
      rw [firstW_get padded blockOff 16 k (by omega) hk]
      by_cases hlt : k < 16 <;> simp [hlt]
  | succ count ih =>
      rw [expandW, List.range'_concat, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [show 16 + 1 * count = 16 + count by omega]
      let t := 16 + count
      change ((expandW padded blockOff count).set! t
        (Sha256.smallSigma1 (expandW padded blockOff count)[t - 2]! +
          (expandW padded blockOff count)[t - 7]! +
          Sha256.smallSigma0 (expandW padded blockOff count)[t - 15]! +
          (expandW padded blockOff count)[t - 16]!))[k]! = _
      rw [Array.set!_eq_setIfInBounds]
      rw [getElem!_pos _ k (by simpa using hk),
        Array.getElem_setIfInBounds (by simpa using hk)]
      by_cases heq : t = k
      · rw [if_pos heq]
        subst k
        rw [ih (t - 2) (by omega) (by omega), if_pos (by omega),
          ih (t - 7) (by omega) (by omega), if_pos (by omega),
          ih (t - 15) (by omega) (by omega), if_pos (by omega),
          ih (t - 16) (by omega) (by omega), if_pos (by omega)]
        rw [if_pos (show t < 16 + (count + 1) by dsimp only [t]; omega)]
        rw [ScheduleCorrect.scheduleWord_of_ge_compressBlock padded blockOff t
          (by dsimp only [t]; omega)]
      · rw [if_neg heq]
        rw [← getElem!_pos (expandW padded blockOff count) k
          (by simpa using hk), ih k (by omega) hk]
        by_cases hlt : k < 16 + count
        · have hlt' : k < 16 + (count + 1) := by omega
          simp [hlt, hlt']
        · have hlt' : ¬k < 16 + (count + 1) := by
            dsimp only [t] at heq
            omega
          simp [hlt, hlt']

abbrev RoundTuple := MProd UInt32 (MProd UInt32 (MProd UInt32
  (MProd UInt32 (MProd UInt32 (MProd UInt32 (MProd UInt32 UInt32))))))

private abbrev ProdRoundTuple := UInt32 × UInt32 × UInt32 × UInt32 ×
  UInt32 × UInt32 × UInt32 × UInt32

private def ProdRoundTuple.toRoundTuple (x : ProdRoundTuple) : RoundTuple :=
  ⟨x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
    x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2⟩

private def prodRound (x : ProdRoundTuple) (k w : UInt32) : ProdRoundTuple :=
  let t1 := x.2.2.2.2.2.2.2 + Sha256.bigSigma1 x.2.2.2.2.1 +
    Sha256.Ch x.2.2.2.2.1 x.2.2.2.2.2.1 x.2.2.2.2.2.2.1 + k + w
  let t2 := Sha256.bigSigma0 x.1 + Sha256.Maj x.1 x.2.1 x.2.2.1
  (t1 + t2, x.1, x.2.1, x.2.2.1, x.2.2.2.1 + t1,
    x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1)

def Working.toTuple (x : Working) : RoundTuple :=
  ⟨x.a, x.b, x.c, x.d, x.e, x.f, x.g, x.h⟩

def tupleRound (x : RoundTuple) (k w : UInt32) : RoundTuple :=
  let ⟨a, b, c, d, e, f, g, h⟩ := x
  let t1 := h + Sha256.bigSigma1 e + Sha256.Ch e f g + k + w
  let t2 := Sha256.bigSigma0 a + Sha256.Maj a b c
  ⟨t1 + t2, a, b, c, d + t1, e, f, g⟩

@[simp] private theorem prodRound_toRoundTuple (x : ProdRoundTuple)
    (k w : UInt32) :
    (prodRound x k w).toRoundTuple = tupleRound x.toRoundTuple k w := by
  rfl

private theorem fold_prodRound_toRoundTuple (W : Array UInt32)
    (xs : List Nat) (initial : ProdRoundTuple) :
    (xs.foldl (fun x n => prodRound x Sha256.K[n]! W[n]!) initial).toRoundTuple =
      xs.foldl (fun x n => tupleRound x Sha256.K[n]! W[n]!)
        initial.toRoundTuple := by
  induction xs generalizing initial with
  | nil => rfl
  | cons n ns ih =>
      simp only [List.foldl_cons]
      rw [ih]
      rfl

@[simp] theorem tupleRound_toTuple (x : Working) (k w : UInt32) :
    tupleRound x.toTuple k w = (round x k w).toTuple := by
  rfl

private def tupleRounds (W : Array UInt32) (initial : Working)
    (count : Nat) : RoundTuple :=
  (List.range' 0 count).foldl
    (fun x n => tupleRound x Sha256.K[n]! W[n]!) initial.toTuple

private theorem tupleRounds_eq (padded : ByteArray) (blockOff count : Nat)
    (initial : Working) (hcount : count ≤ 64) :
    tupleRounds (expandW padded blockOff 48) initial count =
      (rounds initial padded blockOff count).toTuple := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [tupleRounds, List.range'_concat, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [show 0 + 1 * count = count by omega]
      change tupleRound
        (tupleRounds (expandW padded blockOff 48) initial count)
        Sha256.K[count]! (expandW padded blockOff 48)[count]! = _
      rw [ih (by omega)]
      rw [expandW_get padded blockOff 48 count (by omega) (by omega),
        if_pos (by omega)]
      rfl

/-- Interpret the eight input hash words as working variables. -/
def workingOfArray (H : Array UInt32) : Working :=
  ⟨H[0]!, H[1]!, H[2]!, H[3]!, H[4]!, H[5]!, H[6]!, H[7]!⟩

private theorem rawSchedule_eq (padded : ByteArray) (blockOff : Nat) :
    (List.range' 16 (64 - 16)).foldl
        (fun W t => W.set! t
          (Sha256.smallSigma1 W[t - 2]! + W[t - 7]! +
            Sha256.smallSigma0 W[t - 15]! + W[t - 16]!))
        ((List.range' 0 16).foldl
          (fun W t => W.set! t
            (Sha256.readBE32 padded (blockOff + t * 4)))
          (Array.replicate 64 0)) =
      expandW padded blockOff 48 := by
  rfl

private theorem rawRounds_eq (W : Array UInt32) (H : Array UInt32) :
    (List.range' 0 64).foldl
        (fun b a =>
          ⟨b.2.2.2.2.2.2.2 + Sha256.bigSigma1 b.2.2.2.2.1 +
                  Sha256.Ch b.2.2.2.2.1 b.2.2.2.2.2.1 b.2.2.2.2.2.2.1 +
                Sha256.K[a]! + W[a]! +
              (Sha256.bigSigma0 b.1 + Sha256.Maj b.1 b.2.1 b.2.2.1),
            b.1, b.2.1, b.2.2.1,
            b.2.2.2.1 +
              (b.2.2.2.2.2.2.2 + Sha256.bigSigma1 b.2.2.2.2.1 +
                  Sha256.Ch b.2.2.2.2.1 b.2.2.2.2.2.1 b.2.2.2.2.2.2.1 +
                Sha256.K[a]! + W[a]!),
            b.2.2.2.2.1, b.2.2.2.2.2.1, b.2.2.2.2.2.2.1⟩)
        ⟨H[0]!, H[1]!, H[2]!, H[3]!, H[4]!, H[5]!, H[6]!, H[7]!⟩ =
      tupleRounds W (workingOfArray H) 64 := by
  rfl

private def tupleFeedForward (H : Array UInt32) (x : RoundTuple) :
    Array UInt32 :=
  let ⟨a, b, c, d, e, f, g, h⟩ := x
  #[H[0]! + a, H[1]! + b, H[2]! + c, H[3]! + d,
    H[4]! + e, H[5]! + f, H[6]! + g, H[7]! + h]

private theorem feedForward_eq_tuple (H : Array UInt32) (x : Working) :
    feedForward H x = tupleFeedForward H x.toTuple := by
  rfl

private theorem tupleFeedForward_eq_projections (H : Array UInt32)
    (x : RoundTuple) :
    tupleFeedForward H x = #[
      H[0]! + x.1, H[1]! + x.2.1, H[2]! + x.2.2.1,
      H[3]! + x.2.2.2.1, H[4]! + x.2.2.2.2.1,
      H[5]! + x.2.2.2.2.2.1, H[6]! + x.2.2.2.2.2.2.1,
      H[7]! + x.2.2.2.2.2.2.2] := by
  rcases x with ⟨a, b, c, d, e, f, g, h⟩
  rfl

private theorem prodFeedForward_eq (H : Array UInt32) (x : ProdRoundTuple) :
    #[H[0]! + x.1, H[1]! + x.2.1, H[2]! + x.2.2.1,
      H[3]! + x.2.2.2.1, H[4]! + x.2.2.2.2.1,
      H[5]! + x.2.2.2.2.2.1, H[6]! + x.2.2.2.2.2.2.1,
      H[7]! + x.2.2.2.2.2.2.2] =
      tupleFeedForward H x.toRoundTuple := by
  rfl

/-- Pure normalization of the pinned SHA-256 compression specification into
the reusable schedule/round/feed-forward model used above. -/
theorem compressBlock_eq_feedForward (H : Array UInt32) (padded : ByteArray)
    (blockOff : Nat) :
    Sha256.compressBlock H padded blockOff =
      feedForward H (rounds (workingOfArray H) padded blockOff 64) := by
  rw [feedForward_eq_tuple]
  rw [← tupleRounds_eq padded blockOff 64 (workingOfArray H) (by omega)]
  have hprod := fold_prodRound_toRoundTuple (expandW padded blockOff 48)
    (List.range' 0 64)
    (H[0]!, H[1]!, H[2]!, H[3]!, H[4]!, H[5]!, H[6]!, H[7]!)
  change ProdRoundTuple.toRoundTuple
      ((List.range' 0 64).foldl
        (fun x n => prodRound x Sha256.K[n]! (expandW padded blockOff 48)[n]!)
        (H[0]!, H[1]!, H[2]!, H[3]!, H[4]!, H[5]!, H[6]!, H[7]!)) =
    tupleRounds (expandW padded blockOff 48) (workingOfArray H) 64 at hprod
  unfold Sha256.compressBlock
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure]
  rw [rawSchedule_eq padded blockOff]
  generalize hfold : (List.range' 0 64).foldl
    (fun b a =>
      (b.2.2.2.2.2.2.2 + Sha256.bigSigma1 b.2.2.2.2.1 +
              Sha256.Ch b.2.2.2.2.1 b.2.2.2.2.2.1 b.2.2.2.2.2.2.1 +
            Sha256.K[a]! + (expandW padded blockOff 48)[a]! +
          (Sha256.bigSigma0 b.1 + Sha256.Maj b.1 b.2.1 b.2.2.1),
        b.1, b.2.1, b.2.2.1,
        b.2.2.2.1 +
          (b.2.2.2.2.2.2.2 + Sha256.bigSigma1 b.2.2.2.2.1 +
              Sha256.Ch b.2.2.2.2.1 b.2.2.2.2.2.1 b.2.2.2.2.2.2.1 +
            Sha256.K[a]! + (expandW padded blockOff 48)[a]!),
        b.2.2.2.2.1, b.2.2.2.2.2.1, b.2.2.2.2.2.2.1))
    (H[0]!, H[1]!, H[2]!, H[3]!, H[4]!, H[5]!, H[6]!, H[7]!) = x
  have hx : ProdRoundTuple.toRoundTuple x =
      tupleRounds (expandW padded blockOff 48)
      (workingOfArray H) 64 := by
    rw [← hfold]
    simpa only [prodRound] using hprod
  calc
    _ = tupleFeedForward H (ProdRoundTuple.toRoundTuple x) :=
      prodFeedForward_eq H x
    _ = tupleFeedForward H (tupleRounds (expandW padded blockOff 48)
        (workingOfArray H) 64) := congrArg (tupleFeedForward H) hx

private theorem hValue_after_first (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j i : Nat) (hj : j < 16) (hi : i < 8) :
    Compression.hValue (Schedule.afterFirstIteration s msgOff returnDest rest j) i =
      Compression.hValue s i := by
  unfold Compression.hValue
  rw [ScheduleCorrect.afterFirstIteration_memory]
  apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
  left
  rw [hSlot_eq i hi, ScheduleCorrect.scheduleSlot_eq j (by omega)]
  omega

private theorem hValue_firstLoop (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (n i : Nat) (hn : n ≤ 16) (hi : i < 8) :
    Compression.hValue (Schedule.firstLoopState s msgOff returnDest rest n) i =
      Compression.hValue s i := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Schedule.firstLoopState, hValue_after_first _ _ _ _ n i (by omega) hi,
        ih (by omega)]

private theorem hValue_after_second (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j i : Nat) (hj : j < 64) (hi : i < 8) :
    Compression.hValue (Schedule.afterSecondIteration s msgOff returnDest rest j) i =
      Compression.hValue s i := by
  unfold Compression.hValue
  rw [ScheduleCorrect.afterSecondIteration_memory]
  apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
  left
  rw [hSlot_eq i hi, ScheduleCorrect.scheduleSlot_eq j hj]
  omega

private theorem hValue_secondLoop (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (n i : Nat) (hn : n ≤ 48) (hi : i < 8) :
    Compression.hValue (Schedule.secondLoopState s msgOff returnDest rest n) i =
      Compression.hValue s i := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Schedule.secondLoopState,
        hValue_after_second _ _ _ _ (16 + n) i (by omega) hi,
        ih (by omega)]

theorem afterSchedule_hValue (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (i : Nat) (hi : i < 8) :
    Compression.hValue (Compression.afterSchedule s msgOff returnDest rest) i =
      Compression.hValue s i := by
  unfold Compression.afterSchedule Schedule.scheduleResult
  dsimp only
  unfold Schedule.scheduleReturned
  change Compression.hValue
    (Schedule.secondLoopState
      (Schedule.firstLoopState s msgOff (UInt256.ofNat 621)
        (msgOff :: returnDest :: rest) 16)
      msgOff (UInt256.ofNat 621) (msgOff :: returnDest :: rest) 48) i = _
  rw [hValue_secondLoop _ _ _ _ 48 i (by omega) hi,
    hValue_firstLoop _ _ _ _ 16 i (by omega) hi]

private theorem readPadded_write_inside (memory bytes : ByteArray)
    (writeStart off n : Nat) (hinside : off + n ≤ bytes.size) :
    MachineState.readPadded (MachineState.writeBytes memory bytes writeStart)
        (writeStart + off) n =
      MachineState.readPadded bytes off n := by
  apply ByteArray.ext_getElem
  · simp
  · intro i hleft hright
    have hi : i < n := by simpa using hleft
    rw [← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hleft,
      ← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hright,
      Challenge.EvmProof.Memory.readPadded_getElem?_getD,
      Challenge.EvmProof.Memory.readPadded_getElem?_getD,
      if_pos hi, if_pos hi]
    rw [MachineState.writeBytes_getElem?_getD, if_pos]
    · congr 2
      omega
    · constructor <;> omega

private theorem readPadded_readPadded (memory : ByteArray)
    (start total off n : Nat) (hinside : off + n ≤ total) :
    MachineState.readPadded (MachineState.readPadded memory start total) off n =
      MachineState.readPadded memory (start + off) n := by
  apply ByteArray.ext_getElem
  · simp
  · intro i hleft hright
    have hi : i < n := by simpa using hleft
    rw [← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hleft,
      ← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hright,
      Challenge.EvmProof.Memory.readPadded_getElem?_getD,
      Challenge.EvmProof.Memory.readPadded_getElem?_getD,
      if_pos hi]
    rw [if_pos (by omega)]
    rw [Challenge.EvmProof.Memory.readPadded_getElem?_getD]
    rw [if_pos hi]
    congr 2
    omega

theorem copyHashState_hValue (s : State) (i : Nat) (hi : i < 8) :
    Compression.hValue (Compression.copyHashState s) i =
      Compression.hValue s i := by
  unfold Compression.hValue Compression.copyHashState
  apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
  left
  rw [hSlot_eq i hi]
  omega

theorem copyHashState_savedValue (s : State) (i : Nat) (hi : i < 8) :
    Compression.savedValue (Compression.copyHashState s) i =
      Compression.hValue s i := by
  unfold Compression.savedValue Compression.copyHashState Compression.hValue
  rw [savedOffset_eq i hi, hSlot_eq i hi]
  unfold MachineState.readWord
  rw [readPadded_write_inside _ _ 544 (i * 32) 32 (by simp; omega),
    readPadded_readPadded _ 288 256 (i * 32) 32 (by omega)]

private theorem kValue_after_scheduleWrite (before after : State)
    (j write : Nat) (hj : j < 64) (hwrite : write < 64)
    (value : UInt256)
    (hmemory : after.memory = writeH before.memory write value ∨
      after.memory = MachineState.writeBytes before.memory
        (Data.Bytes.natToBytesPadded value.toNat 32) (800 + write * 32)) :
    Compression.kValue after j = Compression.kValue before j := by
  unfold Compression.kValue
  rw [kOffset_eq j hj]
  dsimp only
  rcases hmemory with hm | hm
  · rw [hm, PaddedBlockBridge.shiftRight_readWord_224,
      PaddedBlockBridge.shiftRight_readWord_224,
      readBE32_writeH before.memory j write value hj]
  · rw [hm]
    congr 1
    apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
    left
    omega

private theorem kValue_after_first (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j k : Nat) (hj : j < 16) (hk : k < 64) :
    Compression.kValue (Schedule.afterFirstIteration s msgOff returnDest rest j) k =
      Compression.kValue s k := by
  apply kValue_after_scheduleWrite s _ k j hk (by omega)
    (Schedule.initialWord s.memory msgOff j)
  right
  rw [ScheduleCorrect.afterFirstIteration_memory,
    ScheduleCorrect.scheduleSlot_eq j (by omega)]

private theorem kValue_firstLoop (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (n k : Nat) (hn : n ≤ 16) (hk : k < 64) :
    Compression.kValue (Schedule.firstLoopState s msgOff returnDest rest n) k =
      Compression.kValue s k := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Schedule.firstLoopState, kValue_after_first _ _ _ _ n k (by omega) hk,
        ih (by omega)]

private theorem kValue_after_second (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j k : Nat) (hj : j < 64) (hk : k < 64) :
    Compression.kValue (Schedule.afterSecondIteration s msgOff returnDest rest j) k =
      Compression.kValue s k := by
  apply kValue_after_scheduleWrite s _ k j hk hj
    (Schedule.recurrenceWord s msgOff returnDest rest j)
  right
  rw [ScheduleCorrect.afterSecondIteration_memory,
    ScheduleCorrect.scheduleSlot_eq j hj]

private theorem kValue_secondLoop (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (n k : Nat) (hn : n ≤ 48) (hk : k < 64) :
    Compression.kValue (Schedule.secondLoopState s msgOff returnDest rest n) k =
      Compression.kValue s k := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Schedule.secondLoopState,
        kValue_after_second _ _ _ _ (16 + n) k (by omega) hk,
        ih (by omega)]

theorem afterSchedule_kValue (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (k : Nat) (hk : k < 64) :
    Compression.kValue (Compression.afterSchedule s msgOff returnDest rest) k =
      Compression.kValue s k := by
  unfold Compression.afterSchedule Schedule.scheduleResult
  dsimp only
  unfold Schedule.scheduleReturned
  change Compression.kValue
    (Schedule.secondLoopState
      (Schedule.firstLoopState s msgOff (UInt256.ofNat 621)
        (msgOff :: returnDest :: rest) 16)
      msgOff (UInt256.ofNat 621) (msgOff :: returnDest :: rest) 48) k = _
  rw [kValue_secondLoop _ _ _ _ 48 k (by omega) hk,
    kValue_firstLoop _ _ _ _ 16 k (by omega) hk]

theorem copyHashState_kValue (s : State) (k : Nat) (hk : k < 64) :
    Compression.kValue (Compression.copyHashState s) k =
      Compression.kValue s k := by
  unfold Compression.kValue
  rw [kOffset_eq k hk]
  dsimp only
  rw [show (Compression.copyHashState s).memory =
      MachineState.writeBytes s.memory
        (MachineState.readPadded s.memory 288 256) 544 from rfl]
  rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint]
  left
  omega

theorem copyHashState_wValue (s : State) (j : Nat) (hj : j < 64) :
    Compression.wValue (Compression.copyHashState s) j =
      Compression.wValue s j := by
  unfold Compression.wValue Compression.copyHashState
  apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
  right
  change 544 + (MachineState.readPadded s.memory 288 256).size ≤
    Schedule.scheduleSlot j
  rw [ScheduleCorrect.scheduleSlot_eq j hj,
    Challenge.EvmProof.Memory.readPadded_size]
  simp

private theorem afterFoldIteration_kValue (s : State)
    (msgOff returnDest : UInt256) (rest : List UInt256) (i k : Nat)
    (hi : i < 8) (hk : k < 64) :
    Compression.kValue
        (Compression.afterFoldIteration s msgOff returnDest rest i) k =
      Compression.kValue s k := by
  apply kValue_of_writeH s _ k i hk
    (Compression.foldedValue s msgOff returnDest rest i)
  exact afterFoldIteration_memory s msgOff returnDest rest i hi

theorem foldLoopState_kValue (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (n k : Nat) (hn : n ≤ 8) (hk : k < 64) :
    Compression.kValue
        (Compression.foldLoopState s msgOff returnDest rest n) k =
      Compression.kValue s k := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Compression.foldLoopState,
        afterFoldIteration_kValue _ _ _ _ n k (by omega) hk,
        ih (by omega)]

/-- The complete compression preserves the packed SHA-256 constant table. -/
theorem compressResult_kValue (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (k : Nat) (hk : k < 64) :
    Compression.kValue (Compression.compressResult s msgOff returnDest rest) k =
      Compression.kValue s k := by
  unfold Compression.compressResult
  dsimp only
  unfold Compression.compressReturned
  change Compression.kValue
    (Compression.foldLoopState
      (Compression.roundLoopState
        (Compression.copyHashState
          (Compression.afterSchedule s msgOff returnDest rest))
        msgOff returnDest rest 64)
      msgOff returnDest rest 8) k = _
  rw [foldLoopState_kValue _ _ _ _ 8 k (by omega) hk,
    (roundLoopState_inputs _ _ _ _ 64 k hk).1,
    copyHashState_kValue _ k hk,
    afterSchedule_kValue _ _ _ _ k hk]

theorem compressResult_hValue_core (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (i : Nat) :
    Compression.hValue (Compression.compressResult s msgOff returnDest rest) i =
      Compression.hValue
        (Compression.foldLoopState
          (Compression.roundLoopState
            (Compression.copyHashState
              (Compression.afterSchedule s msgOff returnDest rest))
            msgOff returnDest rest 64)
          msgOff returnDest rest 8) i := by
  rfl

/-- Natural reusable one-block seam for the outer SHA driver. -/
theorem compressResult_eq_compressBlock (s : State)
    (msgOff returnDest : UInt256) (rest : List UInt256)
    (padded : ByteArray) (blockOff : Nat) (H : Array UInt32)
    (hH : ∀ i, i < 8 → Compression.hValue s i =
      Challenge.EvmProof.Word.ofUInt32 H[i]!)
    (hK : ∀ j, j < 64 → Compression.kValue s j =
      Challenge.EvmProof.Word.ofUInt32 Sha256.K[j]!)
    (hW : ScheduleCorrect.SlotsCorrect
      (Compression.afterSchedule s msgOff returnDest rest)
      padded blockOff 64) :
    ∀ i, i < 8 →
      Compression.hValue (Compression.compressResult s msgOff returnDest rest) i =
        Challenge.EvmProof.Word.ofUInt32
          (Sha256.compressBlock H padded blockOff)[i]! := by
  intro i hi
  let q := Compression.afterSchedule s msgOff returnDest rest
  let prepared := Compression.copyHashState q
  have hpH : Represents prepared (workingOfArray H) := by
    unfold Represents workingOfArray
    repeat' apply And.intro
    all_goals
      rw [copyHashState_hValue _ _ (by omega)]
      change Compression.hValue
        (Compression.afterSchedule s msgOff returnDest rest) _ = _
      rw [afterSchedule_hValue (s := s) (msgOff := msgOff)
        (returnDest := returnDest) (rest := rest) (hi := by omega)]
      exact hH _ (by omega)
  have hpSaved : SavedRepresents prepared H := by
    intro k hk
    rw [copyHashState_savedValue _ k hk]
    change Compression.hValue
      (Compression.afterSchedule s msgOff returnDest rest) k = _
    rw [afterSchedule_hValue (s := s) (msgOff := msgOff)
      (returnDest := returnDest) (rest := rest) (i := k) (hi := hk)]
    exact hH k hk
  have hpK : ∀ j, j < 64 → Compression.kValue prepared j =
      Challenge.EvmProof.Word.ofUInt32 Sha256.K[j]! := by
    intro j hj
    rw [copyHashState_kValue _ j hj]
    change Compression.kValue
      (Compression.afterSchedule s msgOff returnDest rest) j = _
    rw [afterSchedule_kValue (s := s) (msgOff := msgOff)
      (returnDest := returnDest) (rest := rest) (k := j) (hk := hj)]
    exact hK j hj
  have hpW : ∀ j, j < 64 → Compression.wValue prepared j =
      Challenge.EvmProof.Word.ofUInt32
        (ScheduleCorrect.scheduleWord padded blockOff j) := by
    intro j hj
    rw [copyHashState_wValue _ j hj]
    exact hW j hj
  have hinputs := roundInputsCorrect_of_entry prepared msgOff returnDest rest
    padded blockOff hpK hpW
  have hcore := compressionCore_words prepared msgOff returnDest rest
    padded blockOff H (workingOfArray H) hpH hpSaved hinputs i hi
  rw [compressResult_hValue_core]
  rw [hcore]
  have hspec := congrArg (fun a : Array UInt32 => a[i]!)
    (compressBlock_eq_feedForward H padded blockOff)
  rw [hspec]
  interval_cases i <;> norm_num <;> rfl

end Challenge.Sha256.Reference.Proofs.Bytecode.CompressionCorrect
