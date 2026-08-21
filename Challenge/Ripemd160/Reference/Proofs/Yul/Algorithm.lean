import Challenge.Ripemd160.Reference.Proofs.Yul.Procedures
import Challenge.Ripemd160.Reference.Proofs.Bytecode.CompressionCorrect
import YulEvmCompiler.Optimizer.Implementation.MemorySpillStateSound

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

/-!
# RIPEMD algorithm bridge for the source-level Yul proof

This file relates the `BitVec 256` expressions executed by the Yul semantics to the existing pure
`UInt32` RIPEMD model.  It contains no EVM execution judgment.
-/

namespace Challenge.Ripemd160.Reference.Proofs.Yul.Algorithm

open YulSemantics.EVM
open YulEvmCompiler
open EvmSemantics
open Challenge.EvmProof.Word
open StateModel
open Challenge.YulProof.EvmState
open Challenge.Ripemd160.Reference.Proofs.Bytecode
open YulEvmCompiler.Optimizer.MemorySpillStateSound

def convWorking (x : SourceWorking) : Compression.EvmWorking where
  a := conv x.a
  b := conv x.b
  c := conv x.c
  d := conv x.d
  e := conv x.e

def sourceWorkingOf (x : Compression.Working) : SourceWorking where
  a := BitVec.ofNat 256 x.a.toNat
  b := BitVec.ofNat 256 x.b.toNat
  c := BitVec.ofNat 256 x.c.toNat
  d := BitVec.ofNat 256 x.d.toNat
  e := BitVec.ofNat 256 x.e.toNat

theorem sourceWorking_ext {x y : SourceWorking}
    (ha : x.a = y.a) (hb : x.b = y.b) (hc : x.c = y.c)
    (hd : x.d = y.d) (he : x.e = y.e) : x = y := by
  cases x
  cases y
  simp_all

@[simp] theorem convWorking_sourceWorkingOf (x : Compression.Working) :
    convWorking (sourceWorkingOf x) = Compression.embed x := by
  rfl

@[simp] theorem embedded_mask (x : UInt32) :
    BitVec.ofNat 256 x.toNat &&& (0xffffffff : U256) =
      BitVec.ofNat 256 x.toNat := by
  apply BitVec.eq_of_toNat_eq
  change (x.toNat % 2 ^ 256 &&& 4294967295) = x.toNat % 2 ^ 256
  rw [Nat.mod_eq_of_lt (Nat.lt_trans x.toNat_lt (by norm_num))]
  simpa using (Nat.and_two_pow_sub_one_of_lt_two_pow x.toNat_lt)

@[simp] theorem mask_sourceWorkingOf (x : Compression.Working) :
    let sx := sourceWorkingOf x
    { a := sx.a &&& 0xffffffff, b := sx.b &&& 0xffffffff,
      c := sx.c &&& 0xffffffff, d := sx.d &&& 0xffffffff,
      e := sx.e &&& 0xffffffff } = sx := by
  cases x
  simp only [sourceWorkingOf]
  congr <;> apply embedded_mask

theorem conv_mask32 (x : U256) :
    conv (x &&& 0xffffffff) = mask32 (conv x) := by
  rw [conv_and]
  unfold mask32
  congr 1

theorem conv_sourceF (j : Nat) (x y z : U256) :
    conv (sourceF j x y z) = Word.evmF j (conv x) (conv y) (conv z) := by
  by_cases hj : j < 5
  · interval_cases j
    · simp only [sourceF, Word.evmF]
      rw [conv_xor, conv_xor]
      rfl
    · simp only [sourceF, Word.evmF]
      rw [conv_or, conv_and, conv_and, conv_not]
      rfl
    · simp only [sourceF, Word.evmF]
      rw [conv_mask32, conv_xor, conv_or, conv_not]
      rfl
    · simp only [sourceF, Word.evmF]
      rw [conv_or, conv_and, conv_and, conv_not]
      rfl
    · simp only [sourceF, Word.evmF]
      rw [conv_mask32, conv_xor, conv_or, conv_not]
      rfl
  · obtain ⟨k, rfl⟩ : ∃ k, j = k + 5 := by
      use j - 5
      omega
    simp only [sourceF, Word.evmF]
    rw [conv_mask32, conv_xor, conv_or, conv_not]
    rfl

theorem conv_ofNat (n : Nat) :
    conv (BitVec.ofNat 256 n) = EvmSemantics.UInt256.ofNat n := by
  apply u256ext
  change n % 2 ^ 256 = n % 2 ^ 256
  rfl

theorem sourceRotl_ofNat (x : U256) (n : Nat) (hn : n ≤ 32) :
    conv (sourceRotl x (BitVec.ofNat 256 n)) = Word.evmRotl32 (conv x) n := by
  have hn256 : n < 2 ^ 256 := by omega
  have hsub256 : 32 - n < 2 ^ 256 := by omega
  have hnword : (BitVec.ofNat 256 n).toNat = n := by
    change n % 2 ^ 256 = n
    rw [Nat.mod_eq_of_lt hn256]
  have hsubword : ((32 : U256) - BitVec.ofNat 256 n).toNat = 32 - n := by
    have hle : BitVec.ofNat 256 n ≤ (32 : U256) := by
      rw [BitVec.le_def, hnword]
      change n ≤ 32
      exact hn
    rw [BitVec.toNat_sub_of_le hle, hnword]
    rfl
  unfold sourceRotl Word.evmRotl32
  rw [conv_mask32]
  congr 1
  rw [conv_or]
  change conv (x <<< (BitVec.ofNat 256 n).toNat) |||
      conv (x >>> ((32 : U256) - BitVec.ofNat 256 n).toNat) = _
  rw [hnword, hsubword]
  have hshl := conv_shl (BitVec.ofNat 256 n) x
  rw [hnword] at hshl
  rw [hshl]
  have hmword : (BitVec.ofNat 256 (32 - n)).toNat = 32 - n := by
    change (32 - n) % 2 ^ 256 = 32 - n
    rw [Nat.mod_eq_of_lt hsub256]
  have hshr := conv_shr (BitVec.ofNat 256 (32 - n)) x
  rw [hmword] at hshr
  rw [hshr]
  rw [conv_ofNat n, conv_ofNat (32 - n)]

theorem conv_sourceRound (x : SourceWorking) (j : Nat) (_hj : j < 5)
    (word constant : U256) (rotation : Nat) (hrotation : rotation ≤ 32) :
    convWorking
        (sourceRound x j word (BitVec.ofNat 256 rotation) constant) =
      Compression.evmRound (convWorking x) j (conv word) rotation (conv constant) := by
  simp only [sourceRound, Compression.evmRound, convWorking]
  congr 1
  · simp only [conv_mask32, conv_add, conv_sourceF,
      sourceRotl_ofNat _ rotation hrotation]
  · exact sourceRotl_ofNat _ 10 (by omega)

/-- A single source-level Yul round refines the mathematical RIPEMD transition. -/
theorem sourceRound_embed (x : Compression.Working) (j : Nat) (word constant : UInt32)
    (rotation : Nat) (hj : j < 5) (hr0 : 0 < rotation) (hr : rotation < 32) :
    convWorking
        (sourceRound
          { a := BitVec.ofNat 256 x.a.toNat, b := BitVec.ofNat 256 x.b.toNat,
            c := BitVec.ofNat 256 x.c.toNat, d := BitVec.ofNat 256 x.d.toNat,
            e := BitVec.ofNat 256 x.e.toNat }
          j (BitVec.ofNat 256 word.toNat) (BitVec.ofNat 256 rotation)
          (BitVec.ofNat 256 constant.toNat)) =
      Compression.embed (Compression.round x j word rotation constant) := by
  rw [conv_sourceRound _ j hj _ _ rotation (by omega)]
  have hx : convWorking
      { a := BitVec.ofNat 256 x.a.toNat, b := BitVec.ofNat 256 x.b.toNat,
        c := BitVec.ofNat 256 x.c.toNat, d := BitVec.ofNat 256 x.d.toNat,
        e := BitVec.ofNat 256 x.e.toNat } = Compression.embed x := by
    congr 1
  rw [hx]
  have hw : conv (BitVec.ofNat 256 word.toNat) = ofUInt32 word := by
    exact conv_ofNat word.toNat
  have hk : conv (BitVec.ofNat 256 constant.toNat) = ofUInt32 constant := by
    exact conv_ofNat constant.toNat
  rw [hw, hk]
  exact Compression.evmRound_embed x j word constant rotation hj hr0 hr

theorem sourceRound_exact (x : Compression.Working) (j : Nat) (word constant : UInt32)
    (rotation : Nat) (hj : j < 5) (hr0 : 0 < rotation) (hr : rotation < 32) :
    sourceRound (sourceWorkingOf x) j (BitVec.ofNat 256 word.toNat)
        (BitVec.ofNat 256 rotation) (BitVec.ofNat 256 constant.toNat) =
      sourceWorkingOf (Compression.round x j word rotation constant) := by
  have h := sourceRound_embed x j word constant rotation hj hr0 hr
  change convWorking
      (sourceRound (sourceWorkingOf x) j (BitVec.ofNat 256 word.toNat)
        (BitVec.ofNat 256 rotation) (BitVec.ofNat 256 constant.toNat)) =
    convWorking (sourceWorkingOf (Compression.round x j word rotation constant)) at h
  generalize sourceRound (sourceWorkingOf x) j (BitVec.ofNat 256 word.toNat)
      (BitVec.ofNat 256 rotation) (BitVec.ofNat 256 constant.toNat) = lhs at h ⊢
  generalize sourceWorkingOf (Compression.round x j word rotation constant) = rhs at h ⊢
  cases lhs
  cases rhs
  simp only [convWorking] at h
  injection h with ha hb hc hd he
  congr
  · exact conv_injective ha
  · exact conv_injective hb
  · exact conv_injective hc
  · exact conv_injective hd
  · exact conv_injective he

private theorem workingAt_storeWorking_0c0 (st : EvmState) (x : SourceWorking) :
    workingAt (storeWorking st 0x0c0 x).memory 0x0c0 =
      { a := x.a &&& 0xffffffff, b := x.b &&& 0xffffffff,
        c := x.c &&& 0xffffffff, d := x.d &&& 0xffffffff,
        e := x.e &&& 0xffffffff } := by
  unfold workingAt storeWorking storeWordAt
  dsimp only
  norm_num [BitVec.toNat_add, BitVec.toNat_mul]
  have h192 : (192 : U256).toNat = 192 := by decide
  have h224 : (224 : U256).toNat = 224 := by decide
  have h256 : (256 : U256).toNat = 256 := by decide
  have h288 : (288 : U256).toNat = 288 := by decide
  have h320 : (320 : U256).toNat = 320 := by decide
  simp only [h192, h224, h256, h288, h320]
  constructor
  · rw [loadWord_storeWord_other _ 224 192 _ (by omega),
      loadWord_storeWord_other _ 256 192 _ (by omega),
      loadWord_storeWord_other _ 288 192 _ (by omega),
      loadWord_storeWord_other _ 320 192 _ (by omega), loadWord_storeWord]
  constructor
  · rw [loadWord_storeWord]
  constructor
  · rw [loadWord_storeWord_other _ 224 256 _ (by omega), loadWord_storeWord]
  constructor
  · rw [loadWord_storeWord_other _ 224 288 _ (by omega),
      loadWord_storeWord_other _ 256 288 _ (by omega), loadWord_storeWord]
  · rw [loadWord_storeWord_other _ 224 320 _ (by omega),
      loadWord_storeWord_other _ 256 320 _ (by omega),
      loadWord_storeWord_other _ 288 320 _ (by omega), loadWord_storeWord]

private theorem workingAt_storeWorking_0160 (st : EvmState) (x : SourceWorking) :
    workingAt (storeWorking st 0x160 x).memory 0x160 =
      { a := x.a &&& 0xffffffff, b := x.b &&& 0xffffffff,
        c := x.c &&& 0xffffffff, d := x.d &&& 0xffffffff,
        e := x.e &&& 0xffffffff } := by
  unfold workingAt storeWorking storeWordAt
  dsimp only
  norm_num [BitVec.toNat_add, BitVec.toNat_mul]
  have h352 : (352 : U256).toNat = 352 := by decide
  have h384 : (384 : U256).toNat = 384 := by decide
  have h416 : (416 : U256).toNat = 416 := by decide
  have h448 : (448 : U256).toNat = 448 := by decide
  have h480 : (480 : U256).toNat = 480 := by decide
  simp only [h352, h384, h416, h448, h480]
  constructor
  · rw [loadWord_storeWord_other _ 384 352 _ (by omega),
      loadWord_storeWord_other _ 416 352 _ (by omega),
      loadWord_storeWord_other _ 448 352 _ (by omega),
      loadWord_storeWord_other _ 480 352 _ (by omega), loadWord_storeWord]
  constructor
  · rw [loadWord_storeWord]
  constructor
  · rw [loadWord_storeWord_other _ 384 416 _ (by omega), loadWord_storeWord]
  constructor
  · rw [loadWord_storeWord_other _ 384 448 _ (by omega),
      loadWord_storeWord_other _ 416 448 _ (by omega), loadWord_storeWord]
  · rw [loadWord_storeWord_other _ 384 480 _ (by omega),
      loadWord_storeWord_other _ 416 480 _ (by omega),
      loadWord_storeWord_other _ 448 480 _ (by omega), loadWord_storeWord]

/-- The generic frame relation specialized to the scratch working region. -/
abbrev HighMemoryEq : EvmState → EvmState → Prop := MemoryEqFrom 0x200

theorem HighMemoryEq.tableValue {before after : EvmState}
    (h : HighMemoryEq before after) (base i : U256)
    (hp : 0x200 ≤ (base + (i / 32) * 32).toNat) :
    StateModel.tableValue after.memory base i =
      StateModel.tableValue before.memory base i := by
  unfold StateModel.tableValue
  rw [MemoryEqFrom.loadWord h _ hp]

private theorem highMemoryEq_storeWorking_0c0 (st : EvmState) (x : SourceWorking) :
    HighMemoryEq st (storeWorking st 0x0c0 x) := by
  unfold storeWorking
  apply MemoryEqFrom.storeWordAt
  · apply MemoryEqFrom.storeWordAt
    · apply MemoryEqFrom.storeWordAt
      · apply MemoryEqFrom.storeWordAt
        · apply MemoryEqFrom.storeWordAt (MemoryEqFrom.refl 0x200 st)
          decide
        · decide
      · decide
    · decide
  · decide

private theorem highMemoryEq_storeWorking_0160 (st : EvmState) (x : SourceWorking) :
    HighMemoryEq st (storeWorking st 0x160 x) := by
  unfold storeWorking
  apply MemoryEqFrom.storeWordAt
  · apply MemoryEqFrom.storeWordAt
    · apply MemoryEqFrom.storeWordAt
      · apply MemoryEqFrom.storeWordAt
        · apply MemoryEqFrom.storeWordAt (MemoryEqFrom.refl 0x200 st)
          decide
        · decide
      · decide
    · decide
  · decide

private theorem highMemoryEq_roundState_0c0 (st : EvmState) (j : Nat)
    (wordIndex rotation constant : U256) :
    HighMemoryEq st (roundState st 0x0c0 j wordIndex rotation constant) := by
  unfold roundState touchWorking
  exact highMemoryEq_storeWorking_0c0 _ _

private theorem highMemoryEq_roundState_0160 (st : EvmState) (j : Nat)
    (wordIndex rotation constant : U256) :
    HighMemoryEq st (roundState st 0x160 j wordIndex rotation constant) := by
  unfold roundState touchWorking
  exact highMemoryEq_storeWorking_0160 _ _

private theorem highMemoryEq_leftRoundStep (st : EvmState) (i : Nat) :
    HighMemoryEq st (leftRoundStepState st i) := by
  let iw := BitVec.ofNat 256 i
  let j := i / 16
  let jw := BitVec.ofNat 256 j
  let constantAddress := 0x620 + jw * 32
  let constantState := touchMemory st constantAddress.toNat 32
  let rotationAddress := (0x560 + (iw / 32) * 32).toNat
  let rotationState := touchMemory constantState rotationAddress 32
  let wordAddress := (0x4a0 + (iw / 32) * 32).toNat
  let wordState := touchMemory rotationState wordAddress 32
  change HighMemoryEq st
    (roundState wordState 0x0c0 j (tableValue st.memory 0x4a0 iw)
      (tableValue st.memory 0x560 iw) (loadWord st.memory constantAddress.toNat))
  exact (MemoryEqFrom.touch 0x200 st constantAddress.toNat 32).trans
    ((MemoryEqFrom.touch 0x200 constantState rotationAddress 32).trans
      ((MemoryEqFrom.touch 0x200 rotationState wordAddress 32).trans
        (highMemoryEq_roundState_0c0 wordState _ _ _ _)))

private theorem highMemoryEq_rightRoundStep (st : EvmState) (i : Nat) :
    HighMemoryEq st (rightRoundStepState st i) := by
  let iw := BitVec.ofNat 256 i
  let group := i / 16
  let groupWord := BitVec.ofNat 256 group
  let j := 4 - group
  let constantAddress := 0x6c0 + groupWord * 32
  let constantState := touchMemory st constantAddress.toNat 32
  let rotationAddress := (0x5c0 + (iw / 32) * 32).toNat
  let rotationState := touchMemory constantState rotationAddress 32
  let wordAddress := (0x500 + (iw / 32) * 32).toNat
  let wordState := touchMemory rotationState wordAddress 32
  change HighMemoryEq st
    (roundState wordState 0x160 j (tableValue st.memory 0x500 iw)
      (tableValue st.memory 0x5c0 iw) (loadWord st.memory constantAddress.toNat))
  exact (MemoryEqFrom.touch 0x200 st constantAddress.toNat 32).trans
    ((MemoryEqFrom.touch 0x200 constantState rotationAddress 32).trans
      ((MemoryEqFrom.touch 0x200 rotationState wordAddress 32).trans
        (highMemoryEq_roundState_0160 wordState _ _ _ _)))

theorem highMemoryEq_leftRoundPrefix (st : EvmState) (count : Nat) :
    HighMemoryEq st (leftRoundPrefix count st) := by
  induction count with
  | zero => exact MemoryEqFrom.refl 0x200 st
  | succ i ih =>
      exact ih.trans (highMemoryEq_leftRoundStep _ i)

theorem highMemoryEq_rightRoundPrefix (st : EvmState) (count : Nat) :
    HighMemoryEq st (rightRoundPrefix count st) := by
  induction count with
  | zero => exact MemoryEqFrom.refl 0x200 st
  | succ i ih =>
      exact ih.trans (highMemoryEq_rightRoundStep _ i)

private theorem leftRotation_pos (i : Nat) (hi : i < 80) :
    0 < Crypto.Ripemd160.s[i]! := by
  interval_cases i <;> decide

private theorem leftRotation_lt (i : Nat) (hi : i < 80) :
    Crypto.Ripemd160.s[i]! < 32 := by
  interval_cases i <;> decide

/-- One concrete left-line memory transition implements `leftStep`; all lookup facts are stated
on the source state and can therefore be transported by `HighMemoryEq`. -/
theorem workingAt_leftRoundStep (st : EvmState) (word : Nat → UInt32)
    (i : Nat) (x : Compression.Working) (hi : i < 80)
    (hworking : workingAt st.memory 0x0c0 = sourceWorkingOf x)
    (hindex : tableValue st.memory 0x4a0 (BitVec.ofNat 256 i) =
      BitVec.ofNat 256 (Crypto.Ripemd160.r[i]!))
    (hrotation : tableValue st.memory 0x560 (BitVec.ofNat 256 i) =
      BitVec.ofNat 256 (Crypto.Ripemd160.s[i]!))
    (hconstant : loadWord st.memory
      (0x620 + BitVec.ofNat 256 (i / 16) * 32).toNat =
        BitVec.ofNat 256 (Crypto.Ripemd160.K[i / 16]!).toNat)
    (hword : loadWord st.memory
      (0x2a0 + BitVec.ofNat 256 (Crypto.Ripemd160.r[i]!) * 32).toNat =
        BitVec.ofNat 256 (word (Crypto.Ripemd160.r[i]!)).toNat) :
    workingAt (leftRoundStepState st i).memory 0x0c0 =
      sourceWorkingOf (CompressionCorrect.leftStep word i x) := by
  unfold leftRoundStepState roundState touchWorking
  simp only [touchMemory]
  rw [workingAt_storeWorking_0c0]
  rw [hworking, hindex, hrotation, hconstant, hword]
  rw [sourceRound_exact x (i / 16) _ _ _ (by omega)
    (leftRotation_pos i hi) (leftRotation_lt i hi)]
  simpa [CompressionCorrect.leftStep] using
    (mask_sourceWorkingOf (CompressionCorrect.leftStep word i x))

private theorem rightRotation_pos (i : Nat) (hi : i < 80) :
    0 < Crypto.Ripemd160.sP[i]! := by
  interval_cases i <;> decide

private theorem rightRotation_lt (i : Nat) (hi : i < 80) :
    Crypto.Ripemd160.sP[i]! < 32 := by
  interval_cases i <;> decide

/-- One concrete right-line memory transition implements `rightStep`. -/
theorem workingAt_rightRoundStep (st : EvmState) (word : Nat → UInt32)
    (i : Nat) (x : Compression.Working) (hi : i < 80)
    (hworking : workingAt st.memory 0x160 = sourceWorkingOf x)
    (hindex : tableValue st.memory 0x500 (BitVec.ofNat 256 i) =
      BitVec.ofNat 256 (Crypto.Ripemd160.rP[i]!))
    (hrotation : tableValue st.memory 0x5c0 (BitVec.ofNat 256 i) =
      BitVec.ofNat 256 (Crypto.Ripemd160.sP[i]!))
    (hconstant : loadWord st.memory
      (0x6c0 + BitVec.ofNat 256 (i / 16) * 32).toNat =
        BitVec.ofNat 256 (Crypto.Ripemd160.KP[i / 16]!).toNat)
    (hword : loadWord st.memory
      (0x2a0 + BitVec.ofNat 256 (Crypto.Ripemd160.rP[i]!) * 32).toNat =
        BitVec.ofNat 256 (word (Crypto.Ripemd160.rP[i]!)).toNat) :
    workingAt (rightRoundStepState st i).memory 0x160 =
      sourceWorkingOf (CompressionCorrect.rightStep word i x) := by
  unfold rightRoundStepState roundState touchWorking
  simp only [touchMemory]
  rw [workingAt_storeWorking_0160]
  rw [hworking, hindex, hrotation, hconstant, hword]
  rw [sourceRound_exact x (4 - i / 16) _ _ _ (by omega)
    (rightRotation_pos i hi) (rightRotation_lt i hi)]
  simpa [CompressionCorrect.rightStep] using
    (mask_sourceWorkingOf (CompressionCorrect.rightStep word i x))

private theorem scheduleAddress_high (i : Nat) (hi : i < 16) :
    0x2a0 ≤ (0x2a0 + BitVec.ofNat 256 i * 32).toNat := by
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : i < 2 ^ 256)]
  have h672 : (672 : U256).toNat = 672 := by decide
  have h32 : (32 : U256).toNat = 32 := by decide
  simp only [h672, h32]
  rw [Nat.mod_eq_of_lt (by omega : i * 32 < 2 ^ 256)]
  rw [Nat.mod_eq_of_lt (by omega : 672 + i * 32 < 2 ^ 256)]
  omega

private theorem tableAddress_high (base : U256) (i : Nat) (hi : i < 80)
    (hbase : 0x2a0 ≤ base.toNat) (hroom : base.toNat + 96 < 2 ^ 256) :
    0x2a0 ≤ (base + (BitVec.ofNat 256 i / 32) * 32).toNat := by
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_udiv,
    BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : i < 2 ^ 256)]
  have h32 : (32 : U256).toNat = 32 := by decide
  simp only [h32]
  have hmul : (i / 32) * 32 < 96 := by omega
  rw [Nat.mod_eq_of_lt (by omega : i / 32 * 32 < 2 ^ 256)]
  rw [Nat.mod_eq_of_lt (by omega : base.toNat + i / 32 * 32 < 2 ^ 256)]
  omega

private theorem constantAddress_high (base : U256) (i : Nat) (hi : i < 80)
    (hbase : 0x2a0 ≤ base.toNat) (hroom : base.toNat + 160 < 2 ^ 256) :
    0x2a0 ≤ (base + BitVec.ofNat 256 (i / 16) * 32).toNat := by
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : i / 16 < 2 ^ 256)]
  have h32 : (32 : U256).toNat = 32 := by decide
  simp only [h32]
  rw [Nat.mod_eq_of_lt (by omega : i / 16 * 32 < 2 ^ 256)]
  rw [Nat.mod_eq_of_lt (by omega : base.toNat + i / 16 * 32 < 2 ^ 256)]
  omega

/-- All message-schedule, permutation, rotation, and constant loads needed by compression. -/
structure LookupCorrect (memory : Nat → UInt8) (word : Nat → UInt32) : Prop where
  schedule : ∀ i, i < 16 →
    loadWord memory (0x2a0 + BitVec.ofNat 256 i * 32).toNat =
      BitVec.ofNat 256 (word i).toNat
  leftIndex : ∀ i, i < 80 →
    tableValue memory 0x4a0 (BitVec.ofNat 256 i) =
      BitVec.ofNat 256 (Crypto.Ripemd160.r[i]!)
  rightIndex : ∀ i, i < 80 →
    tableValue memory 0x500 (BitVec.ofNat 256 i) =
      BitVec.ofNat 256 (Crypto.Ripemd160.rP[i]!)
  leftRotation : ∀ i, i < 80 →
    tableValue memory 0x560 (BitVec.ofNat 256 i) =
      BitVec.ofNat 256 (Crypto.Ripemd160.s[i]!)
  rightRotation : ∀ i, i < 80 →
    tableValue memory 0x5c0 (BitVec.ofNat 256 i) =
      BitVec.ofNat 256 (Crypto.Ripemd160.sP[i]!)
  leftConstant : ∀ i, i < 80 →
    loadWord memory (0x620 + BitVec.ofNat 256 (i / 16) * 32).toNat =
      BitVec.ofNat 256 (Crypto.Ripemd160.K[i / 16]!).toNat
  rightConstant : ∀ i, i < 80 →
    loadWord memory (0x6c0 + BitVec.ofNat 256 (i / 16) * 32).toNat =
      BitVec.ofNat 256 (Crypto.Ripemd160.KP[i / 16]!).toNat

theorem LookupCorrect.transport {before after : EvmState} {word : Nat → UInt32}
    (lookup : LookupCorrect before.memory word) (h : HighMemoryEq before after) :
    LookupCorrect after.memory word where
  schedule i hi := by
    rw [h.loadWord _ (by have := scheduleAddress_high i hi; omega)]
    exact lookup.schedule i hi
  leftIndex i hi := by
    rw [h.tableValue 0x4a0 _ (by
      have := tableAddress_high 0x4a0 i hi (by decide) (by decide); omega)]
    exact lookup.leftIndex i hi
  rightIndex i hi := by
    rw [h.tableValue 0x500 _ (by
      have := tableAddress_high 0x500 i hi (by decide) (by decide); omega)]
    exact lookup.rightIndex i hi
  leftRotation i hi := by
    rw [h.tableValue 0x560 _ (by
      have := tableAddress_high 0x560 i hi (by decide) (by decide); omega)]
    exact lookup.leftRotation i hi
  rightRotation i hi := by
    rw [h.tableValue 0x5c0 _ (by
      have := tableAddress_high 0x5c0 i hi (by decide) (by decide); omega)]
    exact lookup.rightRotation i hi
  leftConstant i hi := by
    rw [h.loadWord _ (by
      have := constantAddress_high 0x620 i hi (by decide) (by decide); omega)]
    exact lookup.leftConstant i hi
  rightConstant i hi := by
    rw [h.loadWord _ (by
      have := constantAddress_high 0x6c0 i hi (by decide) (by decide); omega)]
    exact lookup.rightConstant i hi

private theorem leftIndex_lt (i : Nat) (hi : i < 80) :
    Crypto.Ripemd160.r[i]! < 16 := by
  interval_cases i <;> decide

private theorem rightIndex_lt (i : Nat) (hi : i < 80) :
    Crypto.Ripemd160.rP[i]! < 16 := by
  interval_cases i <;> decide

/-- The entire source-level left loop refines the pure left-round fold. -/
theorem workingAt_leftRoundPrefix (st : EvmState) (word : Nat → UInt32)
    (lookup : LookupCorrect st.memory word) (x : Compression.Working)
    (hworking : workingAt st.memory 0x0c0 = sourceWorkingOf x)
    (count : Nat) (hcount : count ≤ 80) :
    workingAt (leftRoundPrefix count st).memory 0x0c0 =
      sourceWorkingOf (CompressionCorrect.leftRounds word count x) := by
  induction count with
  | zero => simpa [leftRoundPrefix, CompressionCorrect.leftRounds] using hworking
  | succ i ih =>
      rw [leftRoundPrefix, CompressionCorrect.leftRounds]
      let current := leftRoundPrefix i st
      have currentLookup : LookupCorrect current.memory word :=
        lookup.transport (highMemoryEq_leftRoundPrefix st i)
      exact workingAt_leftRoundStep current word i
        (CompressionCorrect.leftRounds word i x) (by omega) (ih (by omega))
        (currentLookup.leftIndex i (by omega))
        (currentLookup.leftRotation i (by omega))
        (currentLookup.leftConstant i (by omega))
        (currentLookup.schedule _ (leftIndex_lt i (by omega)))

/-- The entire source-level right loop refines the pure right-round fold. -/
theorem workingAt_rightRoundPrefix (st : EvmState) (word : Nat → UInt32)
    (lookup : LookupCorrect st.memory word) (x : Compression.Working)
    (hworking : workingAt st.memory 0x160 = sourceWorkingOf x)
    (count : Nat) (hcount : count ≤ 80) :
    workingAt (rightRoundPrefix count st).memory 0x160 =
      sourceWorkingOf (CompressionCorrect.rightRounds word count x) := by
  induction count with
  | zero => simpa [rightRoundPrefix, CompressionCorrect.rightRounds] using hworking
  | succ i ih =>
      rw [rightRoundPrefix, CompressionCorrect.rightRounds]
      let current := rightRoundPrefix i st
      have currentLookup : LookupCorrect current.memory word :=
        lookup.transport (highMemoryEq_rightRoundPrefix st i)
      exact workingAt_rightRoundStep current word i
        (CompressionCorrect.rightRounds word i x) (by omega) (ih (by omega))
        (currentLookup.rightIndex i (by omega))
        (currentLookup.rightRotation i (by omega))
        (currentLookup.rightConstant i (by omega))
        (currentLookup.schedule _ (rightIndex_lt i (by omega)))

private theorem workingAt_mcopy_0c0_020 (st : EvmState) :
    workingAt (mcopyState st 0x0c0 0x020 0x0a0).memory 0x0c0 =
      workingAt st.memory 0x020 := by
  unfold workingAt mcopyState
  dsimp only
  norm_num [BitVec.toNat_add, BitVec.toNat_mul]
  have h32 : (32 : U256).toNat = 32 := by decide
  have h64 : (64 : U256).toNat = 64 := by decide
  have h96 : (96 : U256).toNat = 96 := by decide
  have h128 : (128 : U256).toNat = 128 := by decide
  have h160 : (160 : U256).toNat = 160 := by decide
  have h192 : (192 : U256).toNat = 192 := by decide
  have h224 : (224 : U256).toNat = 224 := by decide
  have h256 : (256 : U256).toNat = 256 := by decide
  have h288 : (288 : U256).toNat = 288 := by decide
  have h320 : (320 : U256).toNat = 320 := by decide
  simp only [h32, h64, h96, h128, h160, h192, h224, h256, h288, h320]
  constructor
  · exact loadWord_copyWithin_window st.memory 192 32 160 0 (by omega)
  constructor
  · exact loadWord_copyWithin_window st.memory 192 32 160 32 (by omega)
  constructor
  · exact loadWord_copyWithin_window st.memory 192 32 160 64 (by omega)
  constructor
  · exact loadWord_copyWithin_window st.memory 192 32 160 96 (by omega)
  · exact loadWord_copyWithin_window st.memory 192 32 160 128 (by omega)

private theorem workingAt_mcopy_hash (st : EvmState) (dst src n : U256)
    (hdst : 0x0c0 ≤ dst.toNat) :
    workingAt (mcopyState st dst src n).memory 0x020 = workingAt st.memory 0x020 := by
  unfold workingAt mcopyState
  dsimp only
  norm_num [BitVec.toNat_add, BitVec.toNat_mul]
  have h32 : (32 : U256).toNat = 32 := by decide
  have h64 : (64 : U256).toNat = 64 := by decide
  have h96 : (96 : U256).toNat = 96 := by decide
  have h128 : (128 : U256).toNat = 128 := by decide
  have h160 : (160 : U256).toNat = 160 := by decide
  simp only [h32, h64, h96, h128, h160]
  constructor
  · exact loadWord_copyWithin_other st.memory dst.toNat src.toNat n.toNat 32
      (Or.inl (by omega))
  constructor
  · exact loadWord_copyWithin_other st.memory dst.toNat src.toNat n.toNat 64
      (Or.inl (by omega))
  constructor
  · exact loadWord_copyWithin_other st.memory dst.toNat src.toNat n.toNat 96
      (Or.inl (by omega))
  constructor
  · exact loadWord_copyWithin_other st.memory dst.toNat src.toNat n.toNat 128
      (Or.inl (by omega))
  · exact loadWord_copyWithin_other st.memory dst.toNat src.toNat n.toNat 160
      (Or.inl (by omega))

private theorem workingAt_mcopy_0160_020 (st : EvmState) :
    workingAt (mcopyState st 0x160 0x020 0x0a0).memory 0x160 =
      workingAt st.memory 0x020 := by
  unfold workingAt mcopyState
  dsimp only
  norm_num [BitVec.toNat_add, BitVec.toNat_mul]
  have h32 : (32 : U256).toNat = 32 := by decide
  have h64 : (64 : U256).toNat = 64 := by decide
  have h96 : (96 : U256).toNat = 96 := by decide
  have h128 : (128 : U256).toNat = 128 := by decide
  have h160 : (160 : U256).toNat = 160 := by decide
  have h352 : (352 : U256).toNat = 352 := by decide
  have h384 : (384 : U256).toNat = 384 := by decide
  have h416 : (416 : U256).toNat = 416 := by decide
  have h448 : (448 : U256).toNat = 448 := by decide
  have h480 : (480 : U256).toNat = 480 := by decide
  simp only [h32, h64, h96, h128, h160, h352, h384, h416, h448, h480]
  constructor
  · exact loadWord_copyWithin_window st.memory 352 32 160 0 (by omega)
  constructor
  · exact loadWord_copyWithin_window st.memory 352 32 160 32 (by omega)
  constructor
  · exact loadWord_copyWithin_window st.memory 352 32 160 64 (by omega)
  constructor
  · exact loadWord_copyWithin_window st.memory 352 32 160 96 (by omega)
  · exact loadWord_copyWithin_window st.memory 352 32 160 128 (by omega)

private theorem workingAt_mcopy_0200_020 (st : EvmState) :
    workingAt (mcopyState st 0x200 0x020 0x0a0).memory 0x200 =
      workingAt st.memory 0x020 := by
  unfold workingAt mcopyState
  dsimp only
  norm_num [BitVec.toNat_add, BitVec.toNat_mul]
  have h32 : (32 : U256).toNat = 32 := by decide
  have h64 : (64 : U256).toNat = 64 := by decide
  have h96 : (96 : U256).toNat = 96 := by decide
  have h128 : (128 : U256).toNat = 128 := by decide
  have h160 : (160 : U256).toNat = 160 := by decide
  have h512 : (512 : U256).toNat = 512 := by decide
  have h544 : (544 : U256).toNat = 544 := by decide
  have h576 : (576 : U256).toNat = 576 := by decide
  have h608 : (608 : U256).toNat = 608 := by decide
  have h640 : (640 : U256).toNat = 640 := by decide
  simp only [h32, h64, h96, h128, h160, h512, h544, h576, h608, h640]
  constructor
  · exact loadWord_copyWithin_window st.memory 512 32 160 0 (by omega)
  constructor
  · exact loadWord_copyWithin_window st.memory 512 32 160 32 (by omega)
  constructor
  · exact loadWord_copyWithin_window st.memory 512 32 160 64 (by omega)
  constructor
  · exact loadWord_copyWithin_window st.memory 512 32 160 96 (by omega)
  · exact loadWord_copyWithin_window st.memory 512 32 160 128 (by omega)

theorem LookupCorrect.mcopy {word : Nat → UInt32} (st : EvmState)
    (lookup : LookupCorrect st.memory word) (dst src n : U256)
    (hbelow : dst.toNat + n.toNat ≤ 0x2a0) :
    LookupCorrect (mcopyState st dst src n).memory word where
  schedule i hi := by
    rw [loadWord_mcopyState_other st dst src n _
      (Or.inr (le_trans hbelow (scheduleAddress_high i hi)))]
    exact lookup.schedule i hi
  leftIndex i hi := by
    unfold tableValue
    rw [loadWord_mcopyState_other st dst src n _
      (Or.inr (le_trans hbelow
        (tableAddress_high 0x4a0 i hi (by decide) (by decide))))]
    exact lookup.leftIndex i hi
  rightIndex i hi := by
    unfold tableValue
    rw [loadWord_mcopyState_other st dst src n _
      (Or.inr (le_trans hbelow
        (tableAddress_high 0x500 i hi (by decide) (by decide))))]
    exact lookup.rightIndex i hi
  leftRotation i hi := by
    unfold tableValue
    rw [loadWord_mcopyState_other st dst src n _
      (Or.inr (le_trans hbelow
        (tableAddress_high 0x560 i hi (by decide) (by decide))))]
    exact lookup.leftRotation i hi
  rightRotation i hi := by
    unfold tableValue
    rw [loadWord_mcopyState_other st dst src n _
      (Or.inr (le_trans hbelow
        (tableAddress_high 0x5c0 i hi (by decide) (by decide))))]
    exact lookup.rightRotation i hi
  leftConstant i hi := by
    rw [loadWord_mcopyState_other st dst src n _
      (Or.inr (le_trans hbelow
        (constantAddress_high 0x620 i hi (by decide) (by decide))))]
    exact lookup.leftConstant i hi
  rightConstant i hi := by
    rw [loadWord_mcopyState_other st dst src n _
      (Or.inr (le_trans hbelow
        (constantAddress_high 0x6c0 i hi (by decide) (by decide))))]
    exact lookup.rightConstant i hi

private theorem loadWord_storeWorking_0c0_high (st : EvmState) (x : SourceWorking)
    (p : Nat) (hp : 0x160 ≤ p) :
    loadWord (storeWorking st 0x0c0 x).memory p = loadWord st.memory p := by
  unfold storeWorking storeWordAt
  dsimp only
  norm_num [BitVec.toNat_add, BitVec.toNat_mul]
  have h192 : (192 : U256).toNat = 192 := by decide
  have h224 : (224 : U256).toNat = 224 := by decide
  have h256 : (256 : U256).toNat = 256 := by decide
  have h288 : (288 : U256).toNat = 288 := by decide
  have h320 : (320 : U256).toNat = 320 := by decide
  simp only [h192, h224, h256, h288, h320]
  rw [loadWord_storeWord_other _ 224 p _ (by omega),
    loadWord_storeWord_other _ 256 p _ (by omega),
    loadWord_storeWord_other _ 288 p _ (by omega),
    loadWord_storeWord_other _ 320 p _ (by omega),
    loadWord_storeWord_other _ 192 p _ (by omega)]

private theorem loadWord_storeWorking_0160_low (st : EvmState) (x : SourceWorking)
    (p : Nat) (hp : p + 32 ≤ 0x160) :
    loadWord (storeWorking st 0x160 x).memory p = loadWord st.memory p := by
  unfold storeWorking storeWordAt
  dsimp only
  norm_num [BitVec.toNat_add, BitVec.toNat_mul]
  have h352 : (352 : U256).toNat = 352 := by decide
  have h384 : (384 : U256).toNat = 384 := by decide
  have h416 : (416 : U256).toNat = 416 := by decide
  have h448 : (448 : U256).toNat = 448 := by decide
  have h480 : (480 : U256).toNat = 480 := by decide
  simp only [h352, h384, h416, h448, h480]
  rw [loadWord_storeWord_other _ 384 p _ (by omega),
    loadWord_storeWord_other _ 416 p _ (by omega),
    loadWord_storeWord_other _ 448 p _ (by omega),
    loadWord_storeWord_other _ 480 p _ (by omega),
    loadWord_storeWord_other _ 352 p _ (by omega)]

private theorem workingAt_leftRoundStep_right (st : EvmState) (i : Nat) :
    workingAt (leftRoundStepState st i).memory 0x160 = workingAt st.memory 0x160 := by
  unfold leftRoundStepState roundState touchWorking workingAt
  simp only [touchMemory]
  norm_num [BitVec.toNat_add, BitVec.toNat_mul]
  have h352 : (352 : U256).toNat = 352 := by decide
  have h384 : (384 : U256).toNat = 384 := by decide
  have h416 : (416 : U256).toNat = 416 := by decide
  have h448 : (448 : U256).toNat = 448 := by decide
  have h480 : (480 : U256).toNat = 480 := by decide
  simp only [h352, h384, h416, h448, h480]
  constructor
  · exact loadWord_storeWorking_0c0_high _ _ 352 (by omega)
  constructor
  · exact loadWord_storeWorking_0c0_high _ _ 384 (by omega)
  constructor
  · exact loadWord_storeWorking_0c0_high _ _ 416 (by omega)
  constructor
  · exact loadWord_storeWorking_0c0_high _ _ 448 (by omega)
  · exact loadWord_storeWorking_0c0_high _ _ 480 (by omega)

private theorem workingAt_rightRoundStep_left (st : EvmState) (i : Nat) :
    workingAt (rightRoundStepState st i).memory 0x0c0 = workingAt st.memory 0x0c0 := by
  unfold rightRoundStepState roundState touchWorking workingAt
  simp only [touchMemory]
  norm_num [BitVec.toNat_add, BitVec.toNat_mul]
  have h192 : (192 : U256).toNat = 192 := by decide
  have h224 : (224 : U256).toNat = 224 := by decide
  have h256 : (256 : U256).toNat = 256 := by decide
  have h288 : (288 : U256).toNat = 288 := by decide
  have h320 : (320 : U256).toNat = 320 := by decide
  simp only [h192, h224, h256, h288, h320]
  constructor
  · exact loadWord_storeWorking_0160_low _ _ 192 (by omega)
  constructor
  · exact loadWord_storeWorking_0160_low _ _ 224 (by omega)
  constructor
  · exact loadWord_storeWorking_0160_low _ _ 256 (by omega)
  constructor
  · exact loadWord_storeWorking_0160_low _ _ 288 (by omega)
  · exact loadWord_storeWorking_0160_low _ _ 320 (by omega)

theorem workingAt_leftRoundPrefix_right (st : EvmState) (count : Nat) :
    workingAt (leftRoundPrefix count st).memory 0x160 = workingAt st.memory 0x160 := by
  induction count with
  | zero => rfl
  | succ i ih => rw [leftRoundPrefix, workingAt_leftRoundStep_right, ih]

theorem workingAt_rightRoundPrefix_left (st : EvmState) (count : Nat) :
    workingAt (rightRoundPrefix count st).memory 0x0c0 = workingAt st.memory 0x0c0 := by
  induction count with
  | zero => rfl
  | succ i ih => rw [rightRoundPrefix, workingAt_rightRoundStep_left, ih]

private theorem workingAt_mcopy_0c0_preserved (st : EvmState) (dst src n : U256)
    (hdst : 0x160 ≤ dst.toNat) :
    workingAt (mcopyState st dst src n).memory 0x0c0 = workingAt st.memory 0x0c0 := by
  unfold workingAt
  norm_num [BitVec.toNat_add, BitVec.toNat_mul]
  have h192 : (192 : U256).toNat = 192 := by decide
  have h224 : (224 : U256).toNat = 224 := by decide
  have h256 : (256 : U256).toNat = 256 := by decide
  have h288 : (288 : U256).toNat = 288 := by decide
  have h320 : (320 : U256).toNat = 320 := by decide
  simp only [h192, h224, h256, h288, h320]
  constructor
  · exact loadWord_mcopyState_other st dst src n 192 (Or.inl (by omega))
  constructor
  · exact loadWord_mcopyState_other st dst src n 224 (Or.inl (by omega))
  constructor
  · exact loadWord_mcopyState_other st dst src n 256 (Or.inl (by omega))
  constructor
  · exact loadWord_mcopyState_other st dst src n 288 (Or.inl (by omega))
  · exact loadWord_mcopyState_other st dst src n 320 (Or.inl (by omega))

private theorem workingAt_mcopy_0160_preserved (st : EvmState) (dst src n : U256)
    (hdst : 0x200 ≤ dst.toNat) :
    workingAt (mcopyState st dst src n).memory 0x160 = workingAt st.memory 0x160 := by
  unfold workingAt
  norm_num [BitVec.toNat_add, BitVec.toNat_mul]
  have h352 : (352 : U256).toNat = 352 := by decide
  have h384 : (384 : U256).toNat = 384 := by decide
  have h416 : (416 : U256).toNat = 416 := by decide
  have h448 : (448 : U256).toNat = 448 := by decide
  have h480 : (480 : U256).toNat = 480 := by decide
  simp only [h352, h384, h416, h448, h480]
  constructor
  · exact loadWord_mcopyState_other st dst src n 352 (Or.inl (by omega))
  constructor
  · exact loadWord_mcopyState_other st dst src n 384 (Or.inl (by omega))
  constructor
  · exact loadWord_mcopyState_other st dst src n 416 (Or.inl (by omega))
  constructor
  · exact loadWord_mcopyState_other st dst src n 448 (Or.inl (by omega))
  · exact loadWord_mcopyState_other st dst src n 480 (Or.inl (by omega))

private theorem workingAt_0200_of_highMemoryEq {before after : EvmState}
    (h : HighMemoryEq before after) :
    workingAt after.memory 0x200 = workingAt before.memory 0x200 := by
  unfold workingAt
  norm_num [BitVec.toNat_add, BitVec.toNat_mul]
  have h512 : (512 : U256).toNat = 512 := by decide
  have h544 : (544 : U256).toNat = 544 := by decide
  have h576 : (576 : U256).toNat = 576 := by decide
  have h608 : (608 : U256).toNat = 608 := by decide
  have h640 : (640 : U256).toNat = 640 := by decide
  simp only [h512, h544, h576, h608, h640]
  constructor
  · exact h.loadWord 512 (by omega)
  constructor
  · exact h.loadWord 544 (by omega)
  constructor
  · exact h.loadWord 576 (by omega)
  constructor
  · exact h.loadWord 608 (by omega)
  · exact h.loadWord 640 (by omega)

structure CompressionWorkCorrect (st : EvmState) (word : Nat → UInt32)
    (h : Compression.HashState) : Prop where
  left : workingAt st.memory 0x0c0 = sourceWorkingOf
    (CompressionCorrect.leftRounds word 80 (CompressionCorrect.workingOfHash h))
  right : workingAt st.memory 0x160 = sourceWorkingOf
    (CompressionCorrect.rightRounds word 80 (CompressionCorrect.workingOfHash h))
  saved : workingAt st.memory 0x200 = sourceWorkingOf (CompressionCorrect.workingOfHash h)

/-- Copying the incoming hash and running both source loops produces exactly the two pure
80-round states while retaining the incoming state for the final cross-combination. -/
theorem compressionWorkState_correct (st : EvmState) (msgOff : U256)
    (word : Nat → UInt32) (h : Compression.HashState)
    (lookup : LookupCorrect (scheduleState msgOff st).memory word)
    (hhash : workingAt (scheduleState msgOff st).memory 0x020 =
      sourceWorkingOf (CompressionCorrect.workingOfHash h)) :
    CompressionWorkCorrect (compressionWorkState st msgOff) word h := by
  let s0 := scheduleState msgOff st
  let s1 := mcopyState s0 0x0c0 0x020 0x0a0
  let s2 := mcopyState s1 0x160 0x020 0x0a0
  let s3 := mcopyState s2 0x200 0x020 0x0a0
  let s4 := leftRoundPrefix 80 s3
  let s5 := rightRoundPrefix 80 s4
  have lookup1 := lookup.mcopy s0 0x0c0 0x020 0x0a0 (by decide)
  have lookup2 := lookup1.mcopy s1 0x160 0x020 0x0a0 (by decide)
  have lookup3 := lookup2.mcopy s2 0x200 0x020 0x0a0 (by decide)
  have hhash1 : workingAt s1.memory 0x020 =
      sourceWorkingOf (CompressionCorrect.workingOfHash h) := by
    rw [workingAt_mcopy_hash s0 0x0c0 0x020 0x0a0 (by decide)]
    exact hhash
  have hhash2 : workingAt s2.memory 0x020 =
      sourceWorkingOf (CompressionCorrect.workingOfHash h) := by
    rw [workingAt_mcopy_hash s1 0x160 0x020 0x0a0 (by decide)]
    exact hhash1
  have hleft3 : workingAt s3.memory 0x0c0 =
      sourceWorkingOf (CompressionCorrect.workingOfHash h) := by
    rw [workingAt_mcopy_0c0_preserved s2 0x200 0x020 0x0a0 (by decide),
      workingAt_mcopy_0c0_preserved s1 0x160 0x020 0x0a0 (by decide),
      workingAt_mcopy_0c0_020]
    exact hhash
  have hright3 : workingAt s3.memory 0x160 =
      sourceWorkingOf (CompressionCorrect.workingOfHash h) := by
    rw [workingAt_mcopy_0160_preserved s2 0x200 0x020 0x0a0 (by decide),
      workingAt_mcopy_0160_020]
    exact hhash1
  have hsaved3 : workingAt s3.memory 0x200 =
      sourceWorkingOf (CompressionCorrect.workingOfHash h) := by
    rw [workingAt_mcopy_0200_020]
    exact hhash2
  have hleft4 := workingAt_leftRoundPrefix s3 word lookup3
    (CompressionCorrect.workingOfHash h) hleft3 80 (by omega)
  have hright4 : workingAt s4.memory 0x160 =
      sourceWorkingOf (CompressionCorrect.workingOfHash h) := by
    rw [workingAt_leftRoundPrefix_right]
    exact hright3
  have lookup4 := lookup3.transport (highMemoryEq_leftRoundPrefix s3 80)
  have hright5 := workingAt_rightRoundPrefix s4 word lookup4
    (CompressionCorrect.workingOfHash h) hright4 80 (by omega)
  have hleft5 : workingAt s5.memory 0x0c0 = sourceWorkingOf
      (CompressionCorrect.leftRounds word 80 (CompressionCorrect.workingOfHash h)) := by
    rw [workingAt_rightRoundPrefix_left]
    exact hleft4
  have hsaved5 : workingAt s5.memory 0x200 =
      sourceWorkingOf (CompressionCorrect.workingOfHash h) := by
    rw [workingAt_0200_of_highMemoryEq (highMemoryEq_rightRoundPrefix s4 80),
      workingAt_0200_of_highMemoryEq (highMemoryEq_leftRoundPrefix s3 80)]
    exact hsaved3
  exact ⟨hleft5, hright5, hsaved5⟩

def setSourceWorking (x : SourceWorking) (i : Nat) (v : U256) : SourceWorking :=
  { a := if 0 = i then v &&& 0xffffffff else x.a
    b := if 1 = i then v &&& 0xffffffff else x.b
    c := if 2 = i then v &&& 0xffffffff else x.c
    d := if 3 = i then v &&& 0xffffffff else x.d
    e := if 4 = i then v &&& 0xffffffff else x.e }

@[simp] private theorem hashAddress0 : (0x20 + 0 * 32 : U256).toNat = 32 := by decide
@[simp] private theorem hashAddress1 : (0x20 + 1 * 32 : U256).toNat = 64 := by decide
@[simp] private theorem hashAddress2 : (0x20 + 2 * 32 : U256).toNat = 96 := by decide
@[simp] private theorem hashAddress3 : (0x20 + 3 * 32 : U256).toNat = 128 := by decide
@[simp] private theorem hashAddress4 : (0x20 + 4 * 32 : U256).toNat = 160 := by decide

private theorem loadWord_hSetState_nat (st : EvmState) (i j : Nat) (v : U256)
    (hi : i < 5) (hj : j < 5) :
    loadWord (hSetState st (BitVec.ofNat 256 i) v).memory (0x20 + j * 32) =
      if j = i then v &&& 0xffffffff else loadWord st.memory (0x20 + j * 32) := by
  unfold hSetState storeWordAt
  norm_num [BitVec.toNat_add, BitVec.toNat_mul]
  have h32 : (32 : U256).toNat = 32 := by decide
  simp only [h32]
  have haddr := Nat.mod_eq_of_lt (show 32 + i * 32 < 2 ^ 256 by omega)
  norm_num only [Nat.reducePow] at haddr
  rw [haddr]
  by_cases hji : j = i
  · subst j
    rw [if_pos rfl, loadWord_storeWord]
  · rw [if_neg hji, loadWord_storeWord_other]
    omega

private theorem loadWord_hSetState_same (st : EvmState) (i j : Nat) (v : U256)
    (hi : i < 5) (hj : j < 5) (hji : j = i) :
    loadWord (hSetState st (BitVec.ofNat 256 i) v).memory (0x20 + j * 32) =
      v &&& 0xffffffff := by
  simpa [hji] using loadWord_hSetState_nat st i j v hi hj

private theorem loadWord_hSetState_other (st : EvmState) (i j : Nat) (v : U256)
    (hi : i < 5) (hj : j < 5) (hji : j ≠ i) :
    loadWord (hSetState st (BitVec.ofNat 256 i) v).memory (0x20 + j * 32) =
      loadWord st.memory (0x20 + j * 32) := by
  simpa [hji] using loadWord_hSetState_nat st i j v hi hj

private theorem workingAt_hSetState_nat (st : EvmState) (i : Nat) (v : U256)
    (hi : i < 5) :
    workingAt (hSetState st (BitVec.ofNat 256 i) v).memory 0x020 =
      setSourceWorking (workingAt st.memory 0x020) i v := by
  apply sourceWorking_ext
  · simpa [workingAt, setSourceWorking] using
      (loadWord_hSetState_nat st i 0 v hi (by omega))
  · simpa [workingAt, setSourceWorking] using
      (loadWord_hSetState_nat st i 1 v hi (by omega))
  · simpa [workingAt, setSourceWorking] using
      (loadWord_hSetState_nat st i 2 v hi (by omega))
  · simpa [workingAt, setSourceWorking] using
      (loadWord_hSetState_nat st i 3 v hi (by omega))
  · simpa [workingAt, setSourceWorking] using
      (loadWord_hSetState_nat st i 4 v hi (by omega))

private theorem workingAt_addThreeMasked_state (st : EvmState) (p q r base : U256) :
    workingAt (addThreeMasked st p q r).2.memory base = workingAt st.memory base := by
  rfl

private theorem workingAt_compressionTailState_shape (st : EvmState) :
    let t := addThreeMasked st 0x220 0x100 0x1c0
    let p1 := addThreeMasked t.2 0x240 0x120 0x1e0
    let s1 := hSetState p1.2 1 p1.1
    let p2 := addThreeMasked s1 0x260 0x140 0x160
    let s2 := hSetState p2.2 2 p2.1
    let p3 := addThreeMasked s2 0x280 0x0c0 0x180
    let s3 := hSetState p3.2 3 p3.1
    let p4 := addThreeMasked s3 0x200 0x0e0 0x1a0
    workingAt (compressionTailState st).memory 0x020 =
      { a := t.1 &&& 0xffffffff, b := p1.1 &&& 0xffffffff,
        c := p2.1 &&& 0xffffffff, d := p3.1 &&& 0xffffffff,
        e := p4.1 &&& 0xffffffff } := by
  let t := addThreeMasked st 0x220 0x100 0x1c0
  let p1 := addThreeMasked t.2 0x240 0x120 0x1e0
  let s1 := hSetState p1.2 1 p1.1
  let p2 := addThreeMasked s1 0x260 0x140 0x160
  let s2 := hSetState p2.2 2 p2.1
  let p3 := addThreeMasked s2 0x280 0x0c0 0x180
  let s3 := hSetState p3.2 3 p3.1
  let p4 := addThreeMasked s3 0x200 0x0e0 0x1a0
  let s4 := hSetState p4.2 4 p4.1
  change workingAt (hSetState s4 (BitVec.ofNat 256 0) t.1).memory 0x020 =
    { a := t.1 &&& 0xffffffff, b := p1.1 &&& 0xffffffff,
      c := p2.1 &&& 0xffffffff, d := p3.1 &&& 0xffffffff,
      e := p4.1 &&& 0xffffffff }
  rw [workingAt_hSetState_nat s4 0 t.1 (by omega)]
  dsimp only [s4]
  rw [show (4 : U256) = BitVec.ofNat 256 4 by decide]
  rw [workingAt_hSetState_nat p4.2 4 p4.1 (by omega)]
  dsimp only [p4]
  rw [workingAt_addThreeMasked_state]
  dsimp only [s3]
  rw [show (3 : U256) = BitVec.ofNat 256 3 by decide]
  rw [workingAt_hSetState_nat p3.2 3 p3.1 (by omega)]
  dsimp only [p3]
  rw [workingAt_addThreeMasked_state]
  dsimp only [s2]
  rw [show (2 : U256) = BitVec.ofNat 256 2 by decide]
  rw [workingAt_hSetState_nat p2.2 2 p2.1 (by omega)]
  dsimp only [p2]
  rw [workingAt_addThreeMasked_state]
  dsimp only [s1]
  rw [show (1 : U256) = BitVec.ofNat 256 1 by decide]
  rw [workingAt_hSetState_nat p1.2 1 p1.1 (by omega)]
  dsimp only [p1]
  rw [workingAt_addThreeMasked_state]
  rfl

/-- The generic frame relation specialized to the combination data region. -/
abbrev DataMemoryEq : EvmState → EvmState → Prop := MemoryEqFrom 0x0c0

private theorem dataMemoryEq_addThreeMasked (st : EvmState) (p q r : U256) :
    DataMemoryEq st (addThreeMasked st p q r).2 := by
  intro _ _
  rfl

private theorem dataMemoryEq_hSetState {before after : EvmState}
    (h : DataMemoryEq before after) (i : Nat) (v : U256) (hi : i < 5) :
    DataMemoryEq before (hSetState after (BitVec.ofNat 256 i) v) := by
  intro p hp
  unfold hSetState storeWordAt
  simp only [storeWord]
  split
  · rename_i hwindow
    simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat] at hwindow
    have h32 : (32 : U256).toNat = 32 := by decide
    simp only [h32] at hwindow
    have hi256 : i < 2 ^ 256 := by omega
    rw [Nat.mod_eq_of_lt hi256] at hwindow
    rw [Nat.mod_eq_of_lt (by omega : i * 32 < 2 ^ 256)] at hwindow
    rw [Nat.mod_eq_of_lt (by omega : 32 + i * 32 < 2 ^ 256)] at hwindow
    omega
  · exact h p hp

private theorem addThreeMasked_value_of_dataMemoryEq {before after : EvmState}
    (h : DataMemoryEq before after) (p q r : U256)
    (hp : 0x0c0 ≤ p.toNat) (hq : 0x0c0 ≤ q.toNat) (hr : 0x0c0 ≤ r.toNat) :
    (addThreeMasked after p q r).1 = (addThreeMasked before p q r).1 := by
  unfold addThreeMasked
  rw [MemoryEqFrom.loadWord h p.toNat hp, MemoryEqFrom.loadWord h q.toNat hq,
    MemoryEqFrom.loadWord h r.toNat hr]

def sourceCombine (saved left right : SourceWorking) : SourceWorking where
  a := (saved.b + left.c + right.d) &&& 0xffffffff
  b := (saved.c + left.d + right.e) &&& 0xffffffff
  c := (saved.d + left.e + right.a) &&& 0xffffffff
  d := (saved.e + left.a + right.b) &&& 0xffffffff
  e := (saved.a + left.b + right.c) &&& 0xffffffff

def sourceHashOf (h : Compression.HashState) : SourceWorking where
  a := BitVec.ofNat 256 h.h0.toNat
  b := BitVec.ofNat 256 h.h1.toNat
  c := BitVec.ofNat 256 h.h2.toNat
  d := BitVec.ofNat 256 h.h3.toNat
  e := BitVec.ofNat 256 h.h4.toNat

theorem sourceCombine_exact (h : Compression.HashState)
    (left right : Compression.Working) :
    sourceCombine (sourceWorkingOf (CompressionCorrect.workingOfHash h))
      (sourceWorkingOf left) (sourceWorkingOf right) =
      sourceHashOf (Compression.combine h left right) := by
  have hc := Compression.evmCombine_embed h left right
  change Compression.evmCombine (Compression.embedHash h)
      (Compression.embed left) (Compression.embed right) =
    Compression.embedHash (Compression.combine h left right) at hc
  apply sourceWorking_ext
  all_goals apply conv_injective
  · have hh := congrArg Compression.EvmHashState.h0 hc
    simp only [Compression.evmCombine, Compression.embedHash, Compression.embed] at hh
    simpa only [sourceCombine, sourceWorkingOf, sourceHashOf,
      CompressionCorrect.workingOfHash, conv_mask32, conv_add, conv_ofNat, ofUInt32] using hh

  · have hh := congrArg Compression.EvmHashState.h1 hc
    simp only [Compression.evmCombine, Compression.embedHash, Compression.embed] at hh
    simpa only [sourceCombine, sourceWorkingOf, sourceHashOf,
      CompressionCorrect.workingOfHash, conv_mask32, conv_add, conv_ofNat, ofUInt32] using hh
  · have hh := congrArg Compression.EvmHashState.h2 hc
    simp only [Compression.evmCombine, Compression.embedHash, Compression.embed] at hh
    simpa only [sourceCombine, sourceWorkingOf, sourceHashOf,
      CompressionCorrect.workingOfHash, conv_mask32, conv_add, conv_ofNat, ofUInt32] using hh
  · have hh := congrArg Compression.EvmHashState.h3 hc
    simp only [Compression.evmCombine, Compression.embedHash, Compression.embed] at hh
    simpa only [sourceCombine, sourceWorkingOf, sourceHashOf,
      CompressionCorrect.workingOfHash, conv_mask32, conv_add, conv_ofNat, ofUInt32] using hh
  · have hh := congrArg Compression.EvmHashState.h4 hc
    simp only [Compression.evmCombine, Compression.embedHash, Compression.embed] at hh
    simpa only [sourceCombine, sourceWorkingOf, sourceHashOf,
      CompressionCorrect.workingOfHash, conv_mask32, conv_add, conv_ofNat, ofUInt32] using hh

@[simp] private theorem addThreeMasked_value_mask (st : EvmState) (p q r : U256) :
    (addThreeMasked st p q r).1 &&& 0xffffffff = (addThreeMasked st p q r).1 := by
  unfold addThreeMasked
  simp only
  rw [BitVec.and_assoc, BitVec.and_self]

/-- The source `compress` tail is the mathematical RIPEMD cross-combination. -/
theorem compressionTailState_correct (st : EvmState) (word : Nat → UInt32)
    (h : Compression.HashState) (work : CompressionWorkCorrect st word h) :
    workingAt (compressionTailState st).memory 0x020 =
      sourceHashOf (CompressionCorrect.compressModel word h) := by
  let t := addThreeMasked st 0x220 0x100 0x1c0
  let p1 := addThreeMasked t.2 0x240 0x120 0x1e0
  let s1 := hSetState p1.2 1 p1.1
  let p2 := addThreeMasked s1 0x260 0x140 0x160
  let s2 := hSetState p2.2 2 p2.1
  let p3 := addThreeMasked s2 0x280 0x0c0 0x180
  let s3 := hSetState p3.2 3 p3.1
  let p4 := addThreeMasked s3 0x200 0x0e0 0x1a0
  have htMem : DataMemoryEq st t.2 := dataMemoryEq_addThreeMasked st _ _ _
  have hp1Mem : DataMemoryEq st p1.2 :=
    htMem.trans (dataMemoryEq_addThreeMasked t.2 _ _ _)
  have hs1Mem : DataMemoryEq st s1 :=
    dataMemoryEq_hSetState hp1Mem 1 p1.1 (by omega)
  have hp2Mem : DataMemoryEq st p2.2 :=
    hs1Mem.trans (dataMemoryEq_addThreeMasked s1 _ _ _)
  have hs2Mem : DataMemoryEq st s2 :=
    dataMemoryEq_hSetState hp2Mem 2 p2.1 (by omega)
  have hp3Mem : DataMemoryEq st p3.2 :=
    hs2Mem.trans (dataMemoryEq_addThreeMasked s2 _ _ _)
  have hs3Mem : DataMemoryEq st s3 :=
    dataMemoryEq_hSetState hp3Mem 3 p3.1 (by omega)
  have hp1Val : p1.1 = (addThreeMasked st 0x240 0x120 0x1e0).1 :=
    addThreeMasked_value_of_dataMemoryEq htMem _ _ _ (by decide) (by decide) (by decide)
  have hp2Val : p2.1 = (addThreeMasked st 0x260 0x140 0x160).1 :=
    addThreeMasked_value_of_dataMemoryEq hs1Mem _ _ _ (by decide) (by decide) (by decide)
  have hp3Val : p3.1 = (addThreeMasked st 0x280 0x0c0 0x180).1 :=
    addThreeMasked_value_of_dataMemoryEq hs2Mem _ _ _ (by decide) (by decide) (by decide)
  have hp4Val : p4.1 = (addThreeMasked st 0x200 0x0e0 0x1a0).1 :=
    addThreeMasked_value_of_dataMemoryEq hs3Mem _ _ _ (by decide) (by decide) (by decide)
  rw [workingAt_compressionTailState_shape]
  rw [hp4Val, hp3Val, hp2Val, hp1Val]
  simp only [addThreeMasked_value_mask]
  change sourceCombine (workingAt st.memory 0x200) (workingAt st.memory 0x0c0)
      (workingAt st.memory 0x160) =
    sourceHashOf (CompressionCorrect.compressModel word h)
  rw [work.saved, work.left, work.right, sourceCombine_exact]
  rfl

/-- The complete source-level `compress` transformer implements one pure
RIPEMD-160 compression step.  Its hypotheses expose only the sixteen message
words, the fixed lookup tables, and the incoming five-word chaining state. -/
theorem compressionState_correct (st : EvmState) (msgOff : U256)
    (word : Nat → UInt32) (h : Compression.HashState)
    (lookup : LookupCorrect (scheduleState msgOff st).memory word)
    (hhash : workingAt (scheduleState msgOff st).memory 0x020 =
      sourceWorkingOf (CompressionCorrect.workingOfHash h)) :
    workingAt (compressionState st msgOff).memory 0x020 =
      sourceHashOf (CompressionCorrect.compressModel word h) := by
  exact compressionTailState_correct _ word h
    (compressionWorkState_correct st msgOff word h lookup hhash)

end Challenge.Ripemd160.Reference.Proofs.Yul.Algorithm
