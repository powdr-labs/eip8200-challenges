import Challenge.Blake2f.ProofSupport.Word
set_option warningAsError true

/-!
# Reusable pure model of BLAKE2f rounds

This module names the eight-quarter-round transition and iteration used by the
pinned crypto specification. Candidate proofs can maintain this model without
depending on the bundled reference's memory layout or control flow.
-/

namespace Challenge.Blake2f.ProofSupport.Algorithm

open EvmSemantics

/-- The four lanes touched by one BLAKE2b quarter-round. Keeping this view
separate from any concrete memory layout makes the arithmetic bridge reusable
by candidate implementations. -/
structure Lanes (α : Type) where
  a : α
  b : α
  c : α
  d : α
  deriving DecidableEq

@[ext] theorem Lanes.ext {α : Type} {x y : Lanes α}
    (ha : x.a = y.a) (hb : x.b = y.b) (hc : x.c = y.c) (hd : x.d = y.d) :
    x = y := by
  cases x
  cases y
  simp_all

def Lanes.embed (v : Lanes UInt64) : Lanes UInt256 :=
  ⟨Word.ofUInt64 v.a, Word.ofUInt64 v.b, Word.ofUInt64 v.c,
    Word.ofUInt64 v.d⟩

/-- The masked EVM shift/or idiom used for a 64-bit right rotation. -/
def rotrWord (x : UInt256) (n : Nat) : UInt256 :=
  Word.mask64 (UInt256.shiftRight x (UInt256.ofNat n) |||
    UInt256.shiftLeft x (UInt256.ofNat (64 - n)))

/-- Pure four-lane form of the pinned `Crypto.Blake2f.mixG` arithmetic. -/
def mixLanes64 (v : Lanes UInt64) (x y : UInt64) : Lanes UInt64 :=
  let a := v.a + v.b + x
  let d := Crypto.Blake2f.rotr64 (v.d ^^^ a) 32
  let c := v.c + d
  let b := Crypto.Blake2f.rotr64 (v.b ^^^ c) 24
  let a := a + b + y
  let d := Crypto.Blake2f.rotr64 (d ^^^ a) 16
  let c := c + d
  let b := Crypto.Blake2f.rotr64 (b ^^^ c) 63
  ⟨a, b, c, d⟩

/-- The same quarter-round expressed with the exact 256-bit operations used by
proof-friendly EVM bytecode. -/
def mixLanesEVM (v : Lanes UInt256) (x y : UInt256) : Lanes UInt256 :=
  let a := Word.mask64 (v.a + v.b + x)
  let d := rotrWord (v.d ^^^ a) 32
  let c := Word.mask64 (v.c + d)
  let b := rotrWord (v.b ^^^ c) 24
  let a := Word.mask64 (a + b + y)
  let d := rotrWord (d ^^^ a) 16
  let c := Word.mask64 (c + d)
  let b := rotrWord (b ^^^ c) 63
  ⟨a, b, c, d⟩

@[simp] theorem rotrWord_ofUInt64 (x : UInt64) (n : Nat)
    (hn0 : 0 < n) (hn : n < 64) :
    rotrWord (Word.ofUInt64 x) n =
      Word.ofUInt64 (Crypto.Blake2f.rotr64 x (UInt64.ofNat n)) := by
  exact Word.evm_rotr64 x n hn0 hn

/-- The EVM quarter-round is exactly the 64-bit BLAKE2b quarter-round whenever
its six inputs are embedded algorithm words. -/
theorem mixLanesEVM_embed (v : Lanes UInt64) (x y : UInt64) :
    mixLanesEVM v.embed (Word.ofUInt64 x) (Word.ofUInt64 y) =
      (mixLanes64 v x y).embed := by
  cases v with
  | mk a b c d =>
    simp only [mixLanesEVM, mixLanes64, Lanes.embed, Word.mask64_add3]
    rw [← Word.ofUInt64_xor, rotrWord_ofUInt64 _ 32 (by omega) (by omega)]
    rw [Word.mask64_add]
    rw [← Word.ofUInt64_xor, rotrWord_ofUInt64 _ 24 (by omega) (by omega)]
    rw [Word.mask64_add3]
    rw [← Word.ofUInt64_xor, rotrWord_ofUInt64 _ 16 (by omega) (by omega)]
    rw [Word.mask64_add]
    rw [← Word.ofUInt64_xor, rotrWord_ofUInt64 _ 63 (by omega) (by omega)]
    have h32 : UInt64.ofNat 32 = 32 := by decide
    have h24 : UInt64.ofNat 24 = 24 := by decide
    have h16 : UInt64.ofNat 16 = 16 := by decide
    have h63 : UInt64.ofNat 63 = 63 := by decide
    simp only [h32, h24, h16, h63]

/-- Project four algorithm lanes from an array using the same zero-defaulting
indexing convention as the pinned crypto implementation. -/
def lanesAt (v : Array UInt64) (a b c d : Nat) : Lanes UInt64 :=
  ⟨v[a]!, v[b]!, v[c]!, v[d]!⟩

/-- The pinned array implementation of `mixG`, viewed at its four distinct
in-bounds lanes, is the reusable pure four-lane transition above. -/
theorem lanesAt_crypto_mixG (v : Array UInt64) (a b c d : Nat) (x y : UInt64)
    (ha : a < v.size) (hb : b < v.size) (hc : c < v.size) (hd : d < v.size)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    lanesAt (Crypto.Blake2f.mixG v a b c d x y) a b c d =
      mixLanes64 (lanesAt v a b c d) x y := by
  simp [Crypto.Blake2f.mixG, lanesAt, mixLanes64,
    Array.set!_eq_setIfInBounds, ha, hb, hc, hd,
    hab, hac, had, hbc, hbd, hcd,
    Ne.symm hab, Ne.symm hac, Ne.symm had, Ne.symm hbc, Ne.symm hbd,
    Ne.symm hcd]

@[simp] theorem crypto_mixG_size (v : Array UInt64) (a b c d : Nat)
    (x y : UInt64) :
    (Crypto.Blake2f.mixG v a b c d x y).size = v.size := by
  simp [Crypto.Blake2f.mixG, Array.set!_eq_setIfInBounds]

@[simp] theorem getElem!_set!_other {α : Type} [Inhabited α] (values : Array α)
    (target i : Nat) (value : α) (hi : i < values.size)
    (hne : target ≠ i) :
    (values.set! target value)[i]! = values[i]! := by
  rw [Array.set!_eq_setIfInBounds]
  rw [getElem!_pos _ i (by simpa using hi),
    Array.getElem_setIfInBounds (by simpa using hi), if_neg hne]
  exact (getElem!_pos values i hi).symm

/-- A quarter-round leaves every non-target lane unchanged. -/
theorem crypto_mixG_getElem!_other (v : Array UInt64)
    (a b c d i : Nat) (x y : UInt64)
    (hi : i < v.size) (hia : i ≠ a) (hib : i ≠ b)
    (hic : i ≠ c) (hid : i ≠ d) :
    (Crypto.Blake2f.mixG v a b c d x y)[i]! = v[i]! := by
  simp [Crypto.Blake2f.mixG, hi,
    Ne.symm hia, Ne.symm hib, Ne.symm hic, Ne.symm hid]

/-- One complete BLAKE2b mixing round, including columns then diagonals. -/
def roundStep (message : Array UInt64) (v : Array UInt64) (round : Nat) :
    Array UInt64 :=
  let sigma := Crypto.Blake2f.SIGMA[round % 10]!
  let v := Crypto.Blake2f.mixG v 0 4 8 12 message[sigma[0]!]! message[sigma[1]!]!
  let v := Crypto.Blake2f.mixG v 1 5 9 13 message[sigma[2]!]! message[sigma[3]!]!
  let v := Crypto.Blake2f.mixG v 2 6 10 14 message[sigma[4]!]! message[sigma[5]!]!
  let v := Crypto.Blake2f.mixG v 3 7 11 15 message[sigma[6]!]! message[sigma[7]!]!
  let v := Crypto.Blake2f.mixG v 0 5 10 15 message[sigma[8]!]! message[sigma[9]!]!
  let v := Crypto.Blake2f.mixG v 1 6 11 12 message[sigma[10]!]! message[sigma[11]!]!
  let v := Crypto.Blake2f.mixG v 2 7 8 13 message[sigma[12]!]! message[sigma[13]!]!
  Crypto.Blake2f.mixG v 3 4 9 14 message[sigma[14]!]! message[sigma[15]!]!

/-- Iterate the mathematical round transition in execution order. -/
def rounds (message : Array UInt64) : Nat → Array UInt64 → Array UInt64
  | 0, v => v
  | count + 1, v => roundStep message (rounds message count v) count

@[simp] theorem rounds_zero (message v) : rounds message 0 v = v := rfl

theorem rounds_succ (message v) (count : Nat) :
    rounds message (count + 1) v =
      roundStep message (rounds message count v) count := rfl

/-- The work vector before the first mixing round, factored out of the pinned
`compress` implementation for bytecode refinement proofs. -/
def initialVector (h : Array UInt64) (t0 t1 : UInt64) (f : Bool) :
    Array UInt64 := Id.run do
  let mut v : Array UInt64 := Array.mkEmpty 16
  for i in [0:8] do v := v.push h[i]!
  for i in [0:8] do v := v.push Crypto.Blake2f.IV[i]!
  v := v.set! 12 (v[12]! ^^^ t0)
  v := v.set! 13 (v[13]! ^^^ t1)
  if f then v := v.set! 14 (v[14]! ^^^ 0xffffffffffffffff)
  return v

@[simp] theorem initialVector_size (h : Array UInt64) (t0 t1 : UInt64)
    (f : Bool) :
    (initialVector h t0 t1 f).size = 16 := by
  cases f <;> simp [initialVector]

def counterVector (h : Array UInt64) (t0 t1 : UInt64) : Array UInt64 :=
  let v := initialVector h 0 0 false
  let v := v.set! 12 (v[12]! ^^^ t0)
  v.set! 13 (v[13]! ^^^ t1)

def flaggedVector (h : Array UInt64) (t0 t1 : UInt64) : Array UInt64 :=
  let v := counterVector h t0 t1
  v.set! 14 (v[14]! ^^^ 0xffffffffffffffff)

theorem counterVector_eq (h : Array UInt64) (t0 t1 : UInt64) :
    counterVector h t0 t1 = initialVector h t0 t1 false := by
  simp [counterVector, initialVector]
  norm_num [List.range', List.range.loop]

theorem flaggedVector_eq (h : Array UInt64) (t0 t1 : UInt64) :
    flaggedVector h t0 t1 = initialVector h t0 t1 true := by
  simp [flaggedVector, counterVector, initialVector]
  norm_num [List.range', List.range.loop]

/-- Fold the two halves of a completed work vector back into the chaining
state. -/
def foldVector (h v : Array UInt64) : Array UInt64 := Id.run do
  let mut out : Array UInt64 := Array.mkEmpty 8
  for i in [0:8] do out := out.push (h[i]! ^^^ v[i]! ^^^ v[i + 8]!)
  return out

@[simp] theorem foldVector_size (h v : Array UInt64) :
    (foldVector h v).size = 8 := by
  simp [foldVector]

theorem foldVector_getElem! (h v : Array UInt64) (i : Nat) (hi : i < 8) :
    (foldVector h v)[i]! = h[i]! ^^^ v[i]! ^^^ v[i + 8]! := by
  simp [foldVector, hi]

private def runRounds (message : Array UInt64) (count : Nat)
    (vector : Array UInt64) : Array UInt64 :=
  (List.range' 0 count).foldl (fun vector round =>
    roundStep message vector round) vector

private theorem runRounds_eq (message vector : Array UInt64) (count : Nat) :
    runRounds message count vector = rounds message count vector := by
  unfold runRounds
  rw [show List.range' 0 count = List.range count by
    simp [List.range'_eq_map_range]]
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [List.range_succ, List.foldl_append]
      simpa [rounds] using congrArg (roundStep message · count) ih

/-- Decomposition of the pinned crypto function into the reusable initial,
round, and fold models. -/
theorem compress_eq (count : Nat) (h message : Array UInt64) (t0 t1 : UInt64)
    (f : Bool) :
    Crypto.Blake2f.compress count h message t0 t1 f =
      foldVector h (rounds message count (initialVector h t0 t1 f)) := by
  rw [← runRounds_eq]
  by_cases hf : f = true
  · simp [Crypto.Blake2f.compress, initialVector, foldVector, runRounds,
      roundStep, hf]
  · simp [Crypto.Blake2f.compress, initialVector, foldVector, runRounds,
      roundStep, hf]

@[simp] theorem roundStep_size (message v : Array UInt64) (round : Nat) :
    (roundStep message v round).size = v.size := by
  simp [roundStep]

@[simp] theorem rounds_size (message : Array UInt64) (count : Nat)
    (v : Array UInt64) :
    (rounds message count v).size = v.size := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [rounds_succ, roundStep_size, ih]

end Challenge.Blake2f.ProofSupport.Algorithm
