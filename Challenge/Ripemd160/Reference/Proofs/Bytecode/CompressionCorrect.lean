import Challenge.Ripemd160.Reference.Proofs.Bytecode.Compression
import Mathlib.Tactic.IntervalCases
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
/-!
# Functional correctness of both RIPEMD-160 round lines

This file lifts the one-round EVM theorem across the two 80-round loops and
their final cross-combination.  The message schedule is an explicit function;
the bytecode schedule proof supplies that function from memory.
-/

namespace Challenge.Ripemd160.Reference.Proofs.Bytecode.CompressionCorrect

open EvmSemantics
open Challenge.EvmProof.Word
open Compression

private theorem leftRotation_pos (i : Nat) (hi : i < 80) :
    0 < Crypto.Ripemd160.s[i]! := by
  interval_cases i <;> decide

private theorem leftRotation_lt (i : Nat) (hi : i < 80) :
    Crypto.Ripemd160.s[i]! < 32 := by
  interval_cases i <;> decide

private theorem rightRotation_pos (i : Nat) (hi : i < 80) :
    0 < Crypto.Ripemd160.sP[i]! := by
  interval_cases i <;> decide

private theorem rightRotation_lt (i : Nat) (hi : i < 80) :
    Crypto.Ripemd160.sP[i]! < 32 := by
  interval_cases i <;> decide

def leftStep (word : Nat → UInt32) (i : Nat) (x : Working) : Working :=
  round x (i / 16) (word (Crypto.Ripemd160.r[i]!))
    (Crypto.Ripemd160.s[i]!) (Crypto.Ripemd160.K[i / 16]!)

def rightStep (word : Nat → UInt32) (i : Nat) (x : Working) : Working :=
  round x (4 - i / 16) (word (Crypto.Ripemd160.rP[i]!))
    (Crypto.Ripemd160.sP[i]!) (Crypto.Ripemd160.KP[i / 16]!)

/-- EVM-level left transition after table lookup and schedule load. -/
def evmLeftStep (word : Nat → UInt32) (i : Nat) (x : EvmWorking) : EvmWorking :=
  evmRound x (i / 16) (ofUInt32 (word (Crypto.Ripemd160.r[i]!)))
    (Crypto.Ripemd160.s[i]!) (ofUInt32 (Crypto.Ripemd160.K[i / 16]!))

/-- EVM-level right transition after table lookup and schedule load. -/
def evmRightStep (word : Nat → UInt32) (i : Nat) (x : EvmWorking) : EvmWorking :=
  evmRound x (4 - i / 16) (ofUInt32 (word (Crypto.Ripemd160.rP[i]!)))
    (Crypto.Ripemd160.sP[i]!) (ofUInt32 (Crypto.Ripemd160.KP[i / 16]!))

theorem evmLeftStep_embed (word : Nat → UInt32) (i : Nat) (x : Working)
    (hi : i < 80) :
    evmLeftStep word i (embed x) = embed (leftStep word i x) := by
  unfold evmLeftStep leftStep
  exact evmRound_embed x (i / 16) _ _ _ (by omega)
    (leftRotation_pos i hi) (leftRotation_lt i hi)

theorem evmRightStep_embed (word : Nat → UInt32) (i : Nat) (x : Working)
    (hi : i < 80) :
    evmRightStep word i (embed x) = embed (rightStep word i x) := by
  unfold evmRightStep rightStep
  exact evmRound_embed x (4 - i / 16) _ _ _ (by omega)
    (rightRotation_pos i hi) (rightRotation_lt i hi)

def leftRounds (word : Nat → UInt32) : Nat → Working → Working
  | 0, x => x
  | i + 1, x => leftStep word i (leftRounds word i x)

def evmLeftRounds (word : Nat → UInt32) : Nat → EvmWorking → EvmWorking
  | 0, x => x
  | i + 1, x => evmLeftStep word i (evmLeftRounds word i x)

def rightRounds (word : Nat → UInt32) : Nat → Working → Working
  | 0, x => x
  | i + 1, x => rightStep word i (rightRounds word i x)

def evmRightRounds (word : Nat → UInt32) : Nat → EvmWorking → EvmWorking
  | 0, x => x
  | i + 1, x => evmRightStep word i (evmRightRounds word i x)

theorem evmLeftRounds_embed (word : Nat → UInt32) (count : Nat) (x : Working)
    (hc : count ≤ 80) :
    evmLeftRounds word count (embed x) = embed (leftRounds word count x) := by
  induction count with
  | zero => rfl
  | succ i ih =>
      rw [evmLeftRounds, leftRounds, ih (by omega)]
      exact evmLeftStep_embed word i _ (by omega)

theorem evmRightRounds_embed (word : Nat → UInt32) (count : Nat) (x : Working)
    (hc : count ≤ 80) :
    evmRightRounds word count (embed x) = embed (rightRounds word count x) := by
  induction count with
  | zero => rfl
  | succ i ih =>
      rw [evmRightRounds, rightRounds, ih (by omega)]
      exact evmRightStep_embed word i _ (by omega)

def workingOfHash (h : HashState) : Working :=
  { a := h.h0, b := h.h1, c := h.h2, d := h.h3, e := h.h4 }

def evmWorkingOfHash (h : EvmHashState) : EvmWorking :=
  { a := h.h0, b := h.h1, c := h.h2, d := h.h3, e := h.h4 }

@[simp] theorem evmWorkingOfHash_embed (h : HashState) :
    evmWorkingOfHash (embedHash h) = embed (workingOfHash h) := by
  rfl

/-- Pure block-compression model using an already parsed 16-word schedule. -/
def compressModel (word : Nat → UInt32) (h : HashState) : HashState :=
  combine h
    (leftRounds word 80 (workingOfHash h))
    (rightRounds word 80 (workingOfHash h))

/-- EVM-word counterpart of `compressModel`. -/
def evmCompressModel (word : Nat → UInt32) (h : EvmHashState) : EvmHashState :=
  evmCombine h
    (evmLeftRounds word 80 (evmWorkingOfHash h))
    (evmRightRounds word 80 (evmWorkingOfHash h))

/-- Both complete 80-round EVM lines and the cross-combination refine the
mathematical compression model. -/
theorem evmCompressModel_embed (word : Nat → UInt32) (h : HashState) :
    evmCompressModel word (embedHash h) = embedHash (compressModel word h) := by
  rw [evmCompressModel, compressModel, evmWorkingOfHash_embed,
    evmLeftRounds_embed _ 80 _ (by omega),
    evmRightRounds_embed _ 80 _ (by omega), evmCombine_embed]

/-- The 16 little-endian words parsed by the specification. -/
def schedule (bs : ByteArray) (blockOff : Nat) : Array UInt32 := Id.run do
  let mut words : Array UInt32 := Array.replicate 16 0
  for i in [0:16] do
    words := words.set! i (Crypto.Ripemd160.readLE32 bs (blockOff + i * 4))
  return words

def hashArray (h : HashState) : Array UInt32 :=
  #[h.h0, h.h1, h.h2, h.h3, h.h4]

abbrev RoundTuple := UInt32 × UInt32 × UInt32 × UInt32 × UInt32

def toTuple (x : Working) : RoundTuple :=
  ⟨x.a, x.b, x.c, x.d, x.e⟩

def tupleLeftStep (word : Nat → UInt32) (x : RoundTuple) (i : Nat) : RoundTuple :=
  let ⟨a, b, c, d, e⟩ := x
  let j := i / 16
  let t := a + Crypto.Ripemd160.f j b c d +
    word (Crypto.Ripemd160.r[i]!) + Crypto.Ripemd160.K[j]!
  let t := Crypto.Ripemd160.rotl32 t Crypto.Ripemd160.s[i]! + e
  ⟨e, t, b, Crypto.Ripemd160.rotl32 c 10, d⟩

def tupleRightStep (word : Nat → UInt32) (x : RoundTuple) (i : Nat) : RoundTuple :=
  let ⟨a, b, c, d, e⟩ := x
  let j := i / 16
  let t := a + Crypto.Ripemd160.f (4 - j) b c d +
    word (Crypto.Ripemd160.rP[i]!) + Crypto.Ripemd160.KP[j]!
  let t := Crypto.Ripemd160.rotl32 t Crypto.Ripemd160.sP[i]! + e
  ⟨e, t, b, Crypto.Ripemd160.rotl32 c 10, d⟩

def tupleLeftRounds (word : Nat → UInt32) (count : Nat)
    (initial : Working) : RoundTuple :=
  (List.range' 0 count).foldl (tupleLeftStep word) (toTuple initial)

def tupleRightRounds (word : Nat → UInt32) (count : Nat)
    (initial : Working) : RoundTuple :=
  (List.range' 0 count).foldl (tupleRightStep word) (toTuple initial)

@[simp] theorem tupleLeftStep_toTuple (word : Nat → UInt32) (x : Working)
    (i : Nat) :
    tupleLeftStep word (toTuple x) i = toTuple (leftStep word i x) := by
  rfl

@[simp] theorem tupleRightStep_toTuple (word : Nat → UInt32) (x : Working)
    (i : Nat) :
    tupleRightStep word (toTuple x) i = toTuple (rightStep word i x) := by
  rfl

theorem tupleLeftRounds_eq (word : Nat → UInt32) (count : Nat)
    (initial : Working) :
    tupleLeftRounds word count initial = toTuple (leftRounds word count initial) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [tupleLeftRounds, List.range'_concat, List.foldl_append]
      simp only [Nat.one_mul, Nat.zero_add, List.foldl_cons, List.foldl_nil]
      change tupleLeftStep word (tupleLeftRounds word count initial) count = _
      rw [ih]
      rfl

theorem tupleRightRounds_eq (word : Nat → UInt32) (count : Nat)
    (initial : Working) :
    tupleRightRounds word count initial = toTuple (rightRounds word count initial) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [tupleRightRounds, List.range'_concat, List.foldl_append]
      simp only [Nat.one_mul, Nat.zero_add, List.foldl_cons, List.foldl_nil]
      change tupleRightStep word (tupleRightRounds word count initial) count = _
      rw [ih]
      rfl

def tupleCombineArray (h : Array UInt32) (left right : RoundTuple) :
    Array UInt32 :=
  let ⟨a, b, c, d, e⟩ := left
  let ⟨aP, bP, cP, dP, eP⟩ := right
  #[h[1]! + c + dP, h[2]! + d + eP, h[3]! + e + aP,
    h[4]! + a + bP, h[0]! + b + cP]

def normalizedCompress (h : Array UInt32) (words : Array UInt32) : Array UInt32 :=
  let left : RoundTuple := (List.range' 0 80).foldl (fun (x : RoundTuple) i =>
    let ⟨a, b, c, d, e⟩ := x
    let j := i / 16
    let t := a + Crypto.Ripemd160.f j b c d +
      words[Crypto.Ripemd160.r[i]!]! + Crypto.Ripemd160.K[j]!
    let t := Crypto.Ripemd160.rotl32 t Crypto.Ripemd160.s[i]! + e
    ⟨e, t, b, Crypto.Ripemd160.rotl32 c 10, d⟩) <|
      ⟨h[0]!, h[1]!, h[2]!, h[3]!, h[4]!⟩
  let right : RoundTuple := (List.range' 0 80).foldl (fun (x : RoundTuple) i =>
    let ⟨a, b, c, d, e⟩ := x
    let j := i / 16
    let t := a + Crypto.Ripemd160.f (4 - j) b c d +
      words[Crypto.Ripemd160.rP[i]!]! + Crypto.Ripemd160.KP[j]!
    let t := Crypto.Ripemd160.rotl32 t Crypto.Ripemd160.sP[i]! + e
    ⟨e, t, b, Crypto.Ripemd160.rotl32 c 10, d⟩) <|
      ⟨h[0]!, h[1]!, h[2]!, h[3]!, h[4]!⟩
  tupleCombineArray h left right

theorem compressBlock_eq_normalized (h : Array UInt32) (bs : ByteArray)
    (blockOff : Nat) :
    Crypto.Ripemd160.compressBlock h bs blockOff =
      normalizedCompress h (schedule bs blockOff) := by
  unfold Crypto.Ripemd160.compressBlock schedule normalizedCompress tupleCombineArray
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure]

theorem normalizedCompress_hashArray (words : Array UInt32) (h : HashState) :
    normalizedCompress (hashArray h) words =
      hashArray (compressModel (fun i => words[i]!) h) := by
  change tupleCombineArray (hashArray h)
      (tupleLeftRounds (fun i => words[i]!) 80 (workingOfHash h))
      (tupleRightRounds (fun i => words[i]!) 80 (workingOfHash h)) = _
  rw [tupleLeftRounds_eq, tupleRightRounds_eq]
  unfold tupleCombineArray hashArray compressModel combine
  rfl

/-- The reusable pure model used by the direct trace is exactly the pinned
RIPEMD-160 block compressor. -/
theorem compressModel_eq_compressBlock (bs : ByteArray) (blockOff : Nat)
    (h : HashState) :
    hashArray (compressModel (fun i => (schedule bs blockOff)[i]!) h) =
      Crypto.Ripemd160.compressBlock (hashArray h) bs blockOff := by
  rw [compressBlock_eq_normalized, normalizedCompress_hashArray]

end Challenge.Ripemd160.Reference.Proofs.Bytecode.CompressionCorrect
