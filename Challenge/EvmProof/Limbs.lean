import Challenge.EvmProof.Bytes
import Mathlib.Data.Nat.Digits.Lemmas
set_option warningAsError true
/-!
# Little-endian 256-bit limbs

The general MODEXP path stores an arbitrary-precision integer as consecutive
EVM words, least-significant word first.  This module gives that memory layout
a small mathematical interface.  It deliberately does not mention the
reference control flow, so all helper and loop certificates can share it.
-/

namespace Challenge.EvmProof.Limbs

open EvmSemantics

/-- Three little-endian digits reconstruct as the expected quadratic radix
polynomial. -/
theorem ofDigits_three (base x y z : Nat) :
    Nat.ofDigits base [x, y, z] = x + base * y + base ^ 2 * z := by
  simp [Nat.ofDigits_cons]
  ring

/-- Radix of one EVM word. -/
def radix : Nat := 2 ^ 256

/-- Number of 256-bit limbs required for a byte width. -/
def limbCount (width : Nat) : Nat := (width + 31) / 32

/-- The fixed-width little-endian radix expansion of `value`. -/
def limbDigits (count value : Nat) : List Nat :=
  Nat.digitsAppend radix count value

/-- Short family-neutral name for the fixed-width digits. -/
abbrev digits := limbDigits

/-- Consecutive little-endian EVM words read from memory. -/
def memoryLimbs (memory : ByteArray) (ptr count : Nat) : List Nat :=
  (List.range count).map fun i =>
    (MachineState.readWord memory (ptr + 32 * i)).toNat

/-- `memory[ptr .. ptr + 32*count]` is the fixed-width limb encoding of
`value`.  The explicit range premise rules out truncating high limbs. -/
def Represents (memory : ByteArray) (ptr count value : Nat) : Prop :=
  value < radix ^ count ∧ memoryLimbs memory ptr count = limbDigits count value

/-- Split a natural into its low word and remaining high part. -/
def splitTwo (value : Nat) : Nat × Nat :=
  (value % radix, value / radix)

/-- Reconstruct a two-limb value, low word first. -/
def joinTwo (limbs : Nat × Nat) : Nat :=
  limbs.1 + radix * limbs.2

/-! ## Width-generic word splitting

The concrete EVM algorithms below use 256-bit words, but the arithmetic facts
that justify splitting, carries, and reconstruction do not depend on that
width.  Keeping the base explicit makes the same lemmas reusable for smaller
test models and future word sizes.
-/

/-- Split a natural at an arbitrary positive word base, low word first. -/
def splitAt (base value : Nat) : Nat × Nat :=
  (value % base, value / base)

/-- Reconstruct a low/high pair at an arbitrary word base. -/
def joinAt (base : Nat) (words : Nat × Nat) : Nat :=
  words.1 + base * words.2

/-- Split the full natural-number product of two words at `base`. -/
def mulSplit (base a b : Nat) : Nat × Nat :=
  splitAt base (a * b)

/-- Add three words at an arbitrary base, retaining the two source-style
overflow bits as a (possibly two-valued) carry. -/
def addThreeAt (base x y z : Nat) : Nat × Nat :=
  let first := (x + y) % base
  let carry₁ := if first < x then 1 else 0
  let result := (first + z) % base
  let carry₂ := if result < first then 1 else 0
  (result, carry₁ + carry₂)

/-- Result word and carry word produced by the EVM's two-`ADD` accumulation
pattern.  The carry can be 0, 1, or 2. -/
structure WordSum where
  word : UInt256
  carry : UInt256
deriving DecidableEq, Repr

namespace WordSum

def value (sum : WordSum) : Nat :=
  sum.word.toNat + radix * sum.carry.toNat

/-- Append one source-style wrapped addition to an existing word/carry state. -/
def add (sum : WordSum) (term : UInt256) : WordSum :=
  let result := sum.word + term
  let overflow := UInt256.lt result sum.word
  { word := result, carry := sum.carry + overflow }

end WordSum

/-- Add two EVM words using one wrapped `ADD` and the source's `LT` overflow
test. -/
def addTwo256 (x y : UInt256) : WordSum :=
  let result := x + y
  { word := result, carry := UInt256.lt result x }

/-- Add three EVM words exactly as the source does: two wrapped `ADD`s and the
sum of their two `LT` overflow bits. -/
def addThree256 (x y z : UInt256) : WordSum :=
  let first := x + y
  let carry₁ := UInt256.lt first x
  let result := first + z
  let carry₂ := UInt256.lt result first
  { word := result, carry := carry₁ + carry₂ }

@[simp] theorem join_splitAt {base : Nat} (_hbase : 0 < base) (value : Nat) :
    joinAt base (splitAt base value) = value := by
  simpa [joinAt, splitAt] using Nat.mod_add_div value base

@[simp] theorem join_mulSplit {base : Nat} (hbase : 0 < base) (a b : Nat) :
    joinAt base (mulSplit base a b) = a * b := by
  exact join_splitAt hbase (a * b)

theorem splitAt_low_lt {base value : Nat} (hbase : 0 < base) :
    (splitAt base value).1 < base := by
  exact Nat.mod_lt value hbase

/-- Two base-bounded digits reconstruct below the square of the base. -/
theorem twoDigits_lt {base lo hi : Nat} (hbase : 1 < base)
    (hlo : lo < base) (hhi : hi < base) :
    lo + base * hi < base ^ 2 := by
  rw [show lo + base * hi = Nat.ofDigits base [lo, hi] by
    simp [Nat.ofDigits_cons]]
  apply Nat.ofDigits_lt_base_pow_length hbase
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  intro digit hdigit
  rcases hdigit with rfl | rfl
  · exact hlo
  · exact hhi

/-- Removing one exact modulus from a value leaves its canonical remainder. -/
theorem residual_eq_mod_of_eq_add {modulus total residual : Nat}
    (htotal : total = modulus + residual) (hresidual : residual < modulus) :
    residual = total % modulus := by
  rw [htotal, Nat.add_mod, Nat.mod_self, Nat.zero_add]
  rw [Nat.mod_mod]
  exact (Nat.mod_eq_of_lt hresidual).symm

theorem mulSplit_high_lt {base a b : Nat} (hbase : 0 < base)
    (ha : a < base) (hb : b < base) :
    (mulSplit base a b).2 < base := by
  simp only [mulSplit, splitAt]
  rw [Nat.div_lt_iff_lt_mul hbase]
  nlinarith

/-- A product of two base-bounded digits plus a third digit still fits in two
base digits.  This generic carry bound avoids normalizing any concrete word
radix. -/
theorem mul_add_lt_sq {base a b c : Nat} (hbase : 0 < base)
    (ha : a < base) (hb : b < base) (hc : c < base) :
    a * b + c < base ^ 2 := by
  have ha' : a ≤ base - 1 := Nat.le_pred_of_lt ha
  have hb' : b ≤ base - 1 := Nat.le_pred_of_lt hb
  have hc' : c ≤ base - 1 := Nat.le_pred_of_lt hc
  have hbase' : base - 1 + 1 = base :=
    Nat.sub_add_cancel (Nat.succ_le_of_lt hbase)
  calc
    a * b + c ≤ (base - 1) * (base - 1) + (base - 1) :=
      Nat.add_le_add (Nat.mul_le_mul ha' hb') hc'
    _ = (base - 1) * base := by
      calc
        (base - 1) * (base - 1) + (base - 1) =
            (base - 1) * (base - 1) + (base - 1) * 1 := by rw [Nat.mul_one]
        _ = (base - 1) * ((base - 1) + 1) := (Nat.mul_add _ _ _).symm
        _ = (base - 1) * base := by rw [hbase']
    _ < base * base := (Nat.mul_lt_mul_right hbase).2
      (Nat.sub_lt hbase (by omega))
    _ = base ^ 2 := by rw [pow_two]

/-- Product-form variant for concrete machine-word consumers.  Keeping the
square unexpanded at a fixed huge radix can make kernel conversion expensive. -/
theorem mul_add_lt_mul_self {base a b c : Nat} (hbase : 0 < base)
    (ha : a < base) (hb : b < base) (hc : c < base) :
    a * b + c < base * base := by
  rw [← pow_two]
  exact mul_add_lt_sq hbase ha hb hc

/-- Width-generic algebra behind one coarsely integrated operand-scanning
Montgomery reduction step.  All variables are unbounded naturals; concrete
word-range and no-wrap obligations remain with the source adapter. -/
theorem ciosReduction_reconstruct
    {base t0 t1 t2 m n0 n1 carry low1 high1
      sum1 carry1 sum2 carry2 : Nat}
    (hcarry : base * carry = t0 + m * n0)
    (hprod1 : low1 + base * high1 = m * n1)
    (hsum1 : sum1 + base * carry1 = t1 + low1)
    (hsum2 : sum2 + base * carry2 = sum1 + carry) :
    base * (sum2 + base * (t2 + high1 + carry1 + carry2)) =
      t0 + base * t1 + base * base * t2 + m * (n0 + base * n1) := by
  ring_nf at *
  nlinarith

/-- Width-generic algebra for the product-accumulation half of a CIOS
iteration, before its low word is cancelled by Montgomery reduction. -/
theorem ciosAccumulate_reconstruct
    {base t0 t1 m n0 n1 low0 carry low1 high1
      sum1 carry1 sum2 carry2 : Nat}
    (hcarry : low0 + base * carry = t0 + m * n0)
    (hprod1 : low1 + base * high1 = m * n1)
    (hsum1 : sum1 + base * carry1 = t1 + low1)
    (hsum2 : sum2 + base * carry2 = sum1 + carry) :
    low0 + base * (sum2 + base * (high1 + carry1 + carry2)) =
      t0 + base * t1 + m * (n0 + base * n1) := by
  ring_nf at *
  nlinarith

/-- Width-generic algebra composing two CIOS multiply/reduce iterations. -/
theorem ciosTwoStep_reconstruct
    {base x0 x1 y modulus first second m0 m1 : Nat}
    (hfirst : base * first = x0 * y + m0 * modulus)
    (hsecond : base * second = first + x1 * y + m1 * modulus) :
    base * base * second =
      (x0 + base * x1) * y + (m0 + base * m1) * modulus := by
  ring_nf at *
  nlinarith

/-! ## Source-faithful EVM full-word multiplication -/

/-- Two EVM words holding a 512-bit product, low word first. -/
structure WideProduct where
  hi : UInt256
  lo : UInt256
deriving DecidableEq, Repr

namespace WideProduct

/-- Reconstruct the natural value of a low/high EVM-word pair. -/
def value (product : WideProduct) : Nat :=
  product.lo.toNat + radix * product.hi.toNat

/-- Every low/high EVM-word pair reconstructs below the two-word radix. -/
theorem value_lt (product : WideProduct) : value product < radix ^ 2 := by
  rw [show value product = Nat.ofDigits radix
      [product.lo.toNat, product.hi.toNat] by
    simp [value, Nat.ofDigits_cons]]
  apply Nat.ofDigits_lt_base_pow_length (by norm_num [radix])
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  intro digit hdigit
  rcases hdigit with rfl | rfl
  · exact product.lo.val.isLt
  · exact product.hi.val.isLt

end WideProduct

/-- The exact EVM full-multiply idiom used by `Fp.sol`: the low word comes
from `MUL`, while the high word is recovered with `MULMOD (2^256-1)` and two
wrapped subtractions. -/
def fullMul256 (a b : UInt256) : WideProduct :=
  let lo := a * b
  let mm := UInt256.mulMod a b (UInt256.lnot (UInt256.ofNat 0))
  let borrow := UInt256.lt mm lo
  { hi := mm - lo - borrow, lo := lo }

/-- Double a two-word value using the exact EVM `SHL`/`SHR`/`OR` schedule:
shift the low word, splice its top bit into the shifted high word, and discard
any carry beyond the two-word boundary. -/
def doubleWide256 (input : WideProduct) : WideProduct :=
  let one := UInt256.ofNat 1
  let carryShift := UInt256.ofNat 255
  { hi := UInt256.lor
      (UInt256.shiftLeft input.hi one)
      (UInt256.shiftRight input.lo carryShift)
    lo := UInt256.shiftLeft input.lo one }

/-- Exact two-word EVM subtraction schedule: subtract the low words, propagate
the `LT` borrow, then perform the two wrapped high-word `SUB`s. -/
def subWide256 (a b : WideProduct) : WideProduct :=
  let borrow := UInt256.lt a.lo b.lo
  { hi := a.hi - b.hi - borrow, lo := a.lo - b.lo }

/-- Exact two-word EVM addition schedule: add the low words, test the wrapped
result against the first low operand, then add both high words and that carry.
-/
def addWide256 (a b : WideProduct) : WideProduct :=
  let low := addTwo256 a.lo b.lo
  { hi := a.hi + b.hi + low.carry, lo := low.word }

/-- Low two words of the schoolbook product of two two-word values.  Terms at
word position two and above are deliberately discarded. -/
def mulWideLow256 (a b : WideProduct) : WideProduct :=
  let low := fullMul256 a.lo b.lo
  { hi := low.hi + a.lo * b.hi + a.hi * b.lo, lo := low.lo }

/-- Exact two-word unsigned `>=` condition used by the source: compare high
words first, then compare low words only when the high words are equal. -/
def wideGeWord (a b : WideProduct) : UInt256 :=
  UInt256.lor (UInt256.gt a.hi b.hi)
    (UInt256.land (UInt256.eq a.hi b.hi)
      (UInt256.isZero (UInt256.lt a.lo b.lo)))

/-- Execute the source's two-word conditional subtraction, branching on the
EVM comparison word rather than a semantic natural-number comparison. -/
def conditionalSubWide256 (a b : WideProduct) : WideProduct :=
  if (wideGeWord a b).toNat ≠ 0 then subWide256 a b else a

/-- Reconstructing the exact two-word EVM subtraction gives ordinary
subtraction when it does not underflow, and the radix-squared wrapped value
otherwise. -/
theorem subWide256_value (a b : WideProduct) :
    (subWide256 a b).value =
      if b.value ≤ a.value then a.value - b.value
      else radix ^ 2 + a.value - b.value := by
  have halo := a.lo.val.isLt
  have hahi := a.hi.val.isLt
  have hblo := b.lo.val.isLt
  have hbhi := b.hi.val.isLt
  change a.lo.toNat < radix at halo
  change a.hi.toNat < radix at hahi
  change b.lo.toNat < radix at hblo
  change b.hi.toNat < radix at hbhi
  unfold subWide256 WideProduct.value
  simp only [Challenge.EvmProof.Word.word_toNat_sub_cond,
    Challenge.EvmProof.Word.word_toNat_lt,
    show 2 ^ 256 = radix by rfl]
  unfold radix at *
  split_ifs <;> omega

theorem fullMul256_words_lt (a b : UInt256) :
    (fullMul256 a b).lo.toNat < radix ∧
      (fullMul256 a b).hi.toNat < radix := by
  exact ⟨(fullMul256 a b).lo.val.isLt, (fullMul256 a b).hi.val.isLt⟩

@[simp] theorem join_splitTwo (value : Nat) :
    joinTwo (splitTwo value) = value := by
  simpa [joinTwo, splitTwo] using Nat.mod_add_div value radix


theorem radix_eq : radix = 256 ^ 32 := by
  simp [radix]

theorem radix_gt_one : 1 < radix := by
  norm_num [radix]

theorem radix_pos : 0 < radix := by
  exact Nat.zero_lt_of_lt radix_gt_one

/-- Two-word subtraction is subtraction modulo the two-word radix. -/
theorem subWide256_value_mod (a b : WideProduct) :
    (subWide256 a b).value =
      (a.value + radix ^ 2 - b.value) % radix ^ 2 := by
  have ha : a.value < radix ^ 2 := by
    have hlo := a.lo.val.isLt
    have hhi := a.hi.val.isLt
    change a.lo.toNat < radix at hlo
    change a.hi.toNat < radix at hhi
    unfold WideProduct.value
    nlinarith
  have hb : b.value < radix ^ 2 := by
    have hlo := b.lo.val.isLt
    have hhi := b.hi.val.isLt
    change b.lo.toNat < radix at hlo
    change b.hi.toNat < radix at hhi
    unfold WideProduct.value
    nlinarith
  rw [subWide256_value]
  split_ifs with hle
  · have hdifference : a.value - b.value < radix ^ 2 :=
      (Nat.sub_le _ _).trans_lt ha
    have hrearrange : a.value + radix ^ 2 - b.value =
        radix ^ 2 + (a.value - b.value) := by omega
    rw [hrearrange, Nat.add_mod, Nat.mod_self, Nat.zero_add]
    simpa using (Nat.mod_eq_of_lt hdifference).symm
  · have hwrapped : radix ^ 2 + a.value - b.value < radix ^ 2 := by omega
    have hrearrange : a.value + radix ^ 2 - b.value =
        radix ^ 2 + a.value - b.value := by omega
    rw [hrearrange]
    exact (Nat.mod_eq_of_lt hwrapped).symm

/-- The EVM comparison word is nonzero exactly when the reconstructed first
operand is at least the second. -/
theorem wideGeWord_nonzero_iff (a b : WideProduct) :
    (wideGeWord a b).toNat ≠ 0 ↔ b.value ≤ a.value := by
  have halo := a.lo.val.isLt
  have hahi := a.hi.val.isLt
  have hblo := b.lo.val.isLt
  have hbhi := b.hi.val.isLt
  change a.lo.toNat < radix at halo
  change a.hi.toNat < radix at hahi
  change b.lo.toNat < radix at hblo
  change b.hi.toNat < radix at hbhi
  have hword : (wideGeWord a b).toNat ≠ 0 ↔
      b.hi.toNat < a.hi.toNat ∨
        (a.hi.toNat = b.hi.toNat ∧ ¬a.lo.toNat < b.lo.toNat) := by
    unfold wideGeWord
    simp only [Challenge.EvmProof.Word.word_toNat_lor,
      Challenge.EvmProof.Word.word_toNat_gt,
      Challenge.EvmProof.Word.word_toNat_land,
      Challenge.EvmProof.Word.word_toNat_eq,
      Challenge.EvmProof.Word.word_toNat_isZero,
      Challenge.EvmProof.Word.word_toNat_lt]
    by_cases hgt : b.hi.toNat < a.hi.toNat <;>
      by_cases heq : a.hi.toNat = b.hi.toNat <;>
      by_cases hlo : b.lo.toNat ≤ a.lo.toNat <;>
      simp [hgt, heq, hlo]
  rw [hword]
  unfold WideProduct.value
  unfold radix at *
  omega

/-- The source conditional subtraction either subtracts the second pair once
or leaves the first pair unchanged. -/
theorem conditionalSubWide256_value (a b : WideProduct) :
    (conditionalSubWide256 a b).value =
      if b.value ≤ a.value then a.value - b.value else a.value := by
  unfold conditionalSubWide256
  by_cases hcondition : (wideGeWord a b).toNat ≠ 0
  · rw [if_pos hcondition]
    have hle := (wideGeWord_nonzero_iff a b).mp hcondition
    rw [subWide256_value]
    simp [hle]
  · rw [if_neg hcondition]
    have hnle : ¬b.value ≤ a.value := by
      intro hle
      apply hcondition
      exact (wideGeWord_nonzero_iff a b).mpr hle
    simp [hnle]

/-- Three EVM words always reconstruct below the three-word radix bound. -/
theorem threeWords_lt (x y z : UInt256) :
    x.toNat + radix * y.toNat + radix ^ 2 * z.toNat < radix ^ 3 := by
  rw [← ofDigits_three]
  apply Nat.ofDigits_lt_base_pow_length radix_gt_one
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  intro digit hdigit
  rcases hdigit with rfl | rfl | rfl
  · exact x.val.isLt
  · exact y.val.isLt
  · exact z.val.isLt

theorem splitTwo_low_lt (value : Nat) : (splitTwo value).1 < radix := by
  exact Nat.mod_lt _ radix_pos

theorem splitTwo_high_lt {value : Nat} (hvalue : value < radix ^ 2) :
    (splitTwo value).2 < radix := by
  rw [splitTwo]
  rw [Nat.div_lt_iff_lt_mul radix_pos]
  simpa [pow_two] using hvalue

theorem limbCount_le_32 (width : Nat) (hwidth : width ≤ 1024) :
    limbCount width ≤ 32 := by
  unfold limbCount
  omega

theorem width_le_limbs (width : Nat) : width ≤ 32 * limbCount width := by
  unfold limbCount
  omega

theorem limbCount_pos {width : Nat} (hwidth : 0 < width) :
    0 < limbCount width := by
  unfold limbCount
  omega

theorem pow_radix (count : Nat) :
    radix ^ count = 256 ^ (32 * count) := by
  rw [radix_eq, ← Nat.pow_mul]

theorem byteValue_fits (input : ByteArray) (offset width : Nat) :
    EvmSemantics.EVM.Precompile.bytesToNatPadded input offset width <
      radix ^ limbCount width := by
  have hbytes := Challenge.EvmProof.Bytes.bytesToNatPadded_lt_pow
    input offset width
  have hwidth := width_le_limbs width
  have hpow : 256 ^ width ≤ 256 ^ (32 * limbCount width) := by
    exact Nat.pow_le_pow_right (by omega) hwidth
  rw [pow_radix]
  exact hbytes.trans_le hpow

@[simp] theorem length_limbDigits {count value : Nat}
    (hvalue : value < radix ^ count) :
    (limbDigits count value).length = count := by
  exact Nat.length_digitsAppend radix_gt_one count hvalue

theorem limbDigits_lt {count value digit : Nat}
    (hdigit : digit ∈ limbDigits count value) : digit < radix := by
  exact Nat.lt_of_mem_digitsAppend radix_gt_one count digit hdigit

theorem value_limbDigits (count value : Nat) :
    Nat.ofDigits radix (limbDigits count value) = value := by
  rw [limbDigits, Nat.digitsAppend, Nat.ofDigits_append_replicate_zero,
    Nat.ofDigits_digits]

theorem memoryLimb_lt (memory : ByteArray) (ptr count : Nat)
    {digit : Nat} (hdigit : digit ∈ memoryLimbs memory ptr count) :
    digit < radix := by
  simp only [memoryLimbs, List.mem_map] at hdigit
  rcases hdigit with ⟨i, _, rfl⟩
  exact (MachineState.readWord memory (ptr + 32 * i)).val.isLt

@[simp] theorem length_memoryLimbs (memory : ByteArray) (ptr count : Nat) :
    (memoryLimbs memory ptr count).length = count := by
  simp [memoryLimbs]

theorem value_of_represents {memory : ByteArray} {ptr count value : Nat}
    (hrep : Represents memory ptr count value) :
    Nat.ofDigits radix (memoryLimbs memory ptr count) = value := by
  rw [hrep.2, value_limbDigits]

theorem represents_value_unique {memory : ByteArray} {ptr count a b : Nat}
    (ha : Represents memory ptr count a) (hb : Represents memory ptr count b) :
    a = b := by
  rw [← value_of_represents ha, ← value_of_represents hb]

theorem represents_iff_value {memory : ByteArray} {ptr count value : Nat}
    (hvalue : value < radix ^ count) :
    Represents memory ptr count value ↔
      Nat.ofDigits radix (memoryLimbs memory ptr count) = value := by
  constructor
  · exact value_of_represents
  · intro heq
    refine ⟨hvalue, ?_⟩
    apply Nat.ofDigits_inj_of_len_eq radix_gt_one
    · rw [length_memoryLimbs, length_limbDigits hvalue]
    · exact fun digit hdigit => memoryLimb_lt _ _ _ hdigit
    · exact fun digit hdigit => limbDigits_lt hdigit
    · rw [heq, value_limbDigits]

/-! ## Arithmetic used by `addMaskedMod`

The bytecode adds either zero or one residue and then performs one conditional
subtraction.  These lemmas isolate the mathematical reason one subtraction is
enough from the word-by-word carry and borrow implementation proved below the
bytecode layer.
-/

theorem masked_sum_lt_twice {x y take modulus : Nat}
    (hx : x < modulus) (hy : y < modulus) (htake : take ≤ 1) :
    x + take * y < 2 * modulus := by
  interval_cases take <;> simp_all <;> omega

theorem masked_sum_lt_twice_of_le {x y take modulus : Nat}
    (hx : x < modulus) (hy : y ≤ modulus) (htake : take ≤ 1) :
    x + take * y < 2 * modulus := by
  interval_cases take <;> simp_all <;> omega

theorem mod_eq_cond_sub {total modulus : Nat}
    (htotal : total < 2 * modulus) :
    total % modulus = if total < modulus then total else total - modulus := by
  split_ifs with hlt
  · exact Nat.mod_eq_of_lt hlt
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

@[simp] theorem join_addThreeAt {base x y z : Nat} (_hbase : 0 < base)
    (hx : x < base) (hy : y < base) (hz : z < base) :
    joinAt base (addThreeAt base x y z) = x + y + z := by
  have hxy : x + y < 2 * base := by omega
  simp only [addThreeAt]
  rw [mod_eq_cond_sub hxy]
  by_cases hfirst : x + y < base
  · simp only [hfirst, ↓reduceIte]
    have hfirstCarry : ¬x + y < x := by omega
    rw [if_neg hfirstCarry]
    have hxyz : x + y + z < 2 * base := by omega
    rw [mod_eq_cond_sub hxyz]
    by_cases hresult : x + y + z < base
    · simp [hresult, joinAt]
    · simp only [hresult, ↓reduceIte]
      have hoverflow : x + y + z - base < x + y := by omega
      simp [hoverflow, joinAt]
      omega
  · simp only [hfirst, ↓reduceIte]
    have hfirstOverflow : x + y - base < x := by omega
    rw [if_pos hfirstOverflow]
    have hnext : x + y - base + z < 2 * base := by omega
    rw [mod_eq_cond_sub hnext]
    by_cases hresult : x + y - base + z < base
    · simp only [hresult, ↓reduceIte]
      have hnotCarry : ¬x + y - base + z < x + y - base := by omega
      simp [hnotCarry, joinAt]
      omega
    · simp only [hresult, ↓reduceIte]
      have hoverflow : x + y - base + z - base < x + y - base := by omega
      simp [hoverflow, joinAt]
      omega

theorem addThree256_value (x y z : UInt256) :
    (addThree256 x y z).value = x.toNat + y.toNat + z.toNat := by
  unfold WordSum.value addThree256
  dsimp only
  simp only [Challenge.EvmProof.Word.word_toNat_add,
    Challenge.EvmProof.Word.word_toNat_lt]
  rw [show 2 ^ 256 = radix by rfl]
  have hcarry :
      (if (x.toNat + y.toNat) % radix < x.toNat then 1 else 0) +
          (if ((x.toNat + y.toNat) % radix + z.toNat) % radix <
            (x.toNat + y.toNat) % radix then 1 else 0) < radix := by
    split_ifs <;> norm_num [radix]
  rw [Nat.mod_eq_of_lt hcarry]
  convert join_addThreeAt (base := radix) radix_pos
      x.val.isLt y.val.isLt z.val.isLt using 1 <;>
    simp [joinAt, addThreeAt, UInt256.toNat]

/-- The wrapped result word and overflow bit reconstruct ordinary addition. -/
theorem addTwo256_value (x y : UInt256) :
    (addTwo256 x y).value = x.toNat + y.toNat := by
  unfold addTwo256 WordSum.value
  dsimp only
  simp only [Challenge.EvmProof.Word.word_toNat_add,
    Challenge.EvmProof.Word.word_toNat_lt]
  rw [show 2 ^ 256 = radix by rfl]
  have hx := x.val.isLt
  have hy := y.val.isLt
  change x.toNat < radix at hx
  change y.toNat < radix at hy
  have hsum : x.toNat + y.toNat < 2 * radix := by omega
  rw [mod_eq_cond_sub hsum]
  by_cases hoverflow : x.toNat + y.toNat < radix
  · rw [if_pos hoverflow, if_neg (by omega)]
    simp
  · rw [if_neg hoverflow, if_pos (by omega)]
    norm_num [radix]
    exact Nat.sub_add_cancel (by
      simpa [radix] using (Nat.le_of_not_gt hoverflow))

/-- The exact two-word source addition reconstructs addition modulo the
two-word radix. -/
theorem addWide256_value_mod (a b : WideProduct) :
    (addWide256 a b).value = (a.value + b.value) % radix ^ 2 := by
  let low := addTwo256 a.lo b.lo
  have hlow : low.value = a.lo.toNat + b.lo.toNat :=
    addTwo256_value a.lo b.lo
  have hcarry : low.carry.toNat < 2 := by
    unfold low addTwo256
    dsimp only
    rw [Challenge.EvmProof.Word.word_toNat_lt]
    split <;> norm_num
  have halo := a.lo.val.isLt
  have hblo := b.lo.val.isLt
  have hahi := a.hi.val.isLt
  have hbhi := b.hi.val.isLt
  change a.lo.toNat < radix at halo
  change b.lo.toNat < radix at hblo
  change a.hi.toNat < radix at hahi
  change b.hi.toNat < radix at hbhi
  have hlowWord : low.word.toNat < radix := low.word.val.isLt
  have hhighSum : a.hi.toNat + b.hi.toNat + low.carry.toNat < 2 * radix := by
    omega
  have htotal : a.value + b.value =
      low.word.toNat + radix *
        (a.hi.toNat + b.hi.toNat + low.carry.toNat) := by
    change low.word.toNat + radix * low.carry.toNat =
      a.lo.toNat + b.lo.toNat at hlow
    calc
      a.value + b.value =
          (a.lo.toNat + b.lo.toNat) +
            radix * (a.hi.toNat + b.hi.toNat) := by
        unfold WideProduct.value
        ring
      _ = (low.word.toNat + radix * low.carry.toNat) +
            radix * (a.hi.toNat + b.hi.toNat) := by rw [hlow]
      _ = low.word.toNat + radix *
            (a.hi.toNat + b.hi.toNat + low.carry.toNat) := by ring
  unfold addWide256
  change low.word.toNat + radix *
      (a.hi + b.hi + low.carry).toNat = _
  simp only [Challenge.EvmProof.Word.word_toNat_add]
  rw [show 2 ^ 256 = radix by rfl]
  have hhighMod :
      ((a.hi.toNat + b.hi.toNat) % radix + low.carry.toNat) % radix =
        (a.hi.toNat + b.hi.toNat + low.carry.toNat) % radix := by
    simp [Nat.add_mod]
  rw [hhighMod, htotal]
  by_cases hhigh : a.hi.toNat + b.hi.toNat + low.carry.toNat < radix
  · rw [Nat.mod_eq_of_lt hhigh]
    apply (Nat.mod_eq_of_lt _).symm
    nlinarith
  · have hhighLe : radix ≤
        a.hi.toNat + b.hi.toNat + low.carry.toNat := Nat.le_of_not_gt hhigh
    rw [mod_eq_cond_sub hhighSum, if_neg hhigh]
    have hresult : low.word.toNat + radix *
        (a.hi.toNat + b.hi.toNat + low.carry.toNat - radix) <
          radix ^ 2 := by
      apply twoDigits_lt radix_gt_one hlowWord
      omega
    have hsplit : radix +
        (a.hi.toNat + b.hi.toNat + low.carry.toNat - radix) =
          a.hi.toNat + b.hi.toNat + low.carry.toNat := by omega
    have hrearrange :
        low.word.toNat + radix *
            (a.hi.toNat + b.hi.toNat + low.carry.toNat) =
          radix ^ 2 +
            (low.word.toNat + radix *
              (a.hi.toNat + b.hi.toNat + low.carry.toNat - radix)) := by
      calc
        _ = low.word.toNat + radix *
              (radix +
                (a.hi.toNat + b.hi.toNat + low.carry.toNat - radix)) := by
          rw [hsplit]
        _ = _ := by ring
    exact residual_eq_mod_of_eq_add hrearrange hresult

theorem addTwo256_carry_lt_two (x y : UInt256) :
    (addTwo256 x y).carry.toNat < 2 := by
  unfold addTwo256
  dsimp only
  simp only [Challenge.EvmProof.Word.word_toNat_lt]
  split_ifs <;> norm_num

/-- If the mathematical sum is zero modulo one word, the exact wrapped source
`ADD` result is the zero word. -/
theorem addTwo256_word_eq_zero_of_modEq (x y : UInt256)
    (hzero : x.toNat + y.toNat ≡ 0 [MOD radix]) :
    (addTwo256 x y).word = UInt256.ofNat 0 := by
  apply congrArg UInt256.mk
  apply Fin.ext
  change (x + y).toNat = (UInt256.ofNat 0).toNat
  rw [Challenge.EvmProof.Word.word_toNat_add,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact hzero

theorem addThree256_carry_lt_three (x y z : UInt256) :
    (addThree256 x y z).carry.toNat < 3 := by
  unfold addThree256
  dsimp only
  simp only [Challenge.EvmProof.Word.word_toNat_add,
    Challenge.EvmProof.Word.word_toNat_lt]
  split_ifs <;> norm_num

theorem WordSum.value_add (sum : WordSum) (term : UInt256)
    (hcarry : sum.carry.toNat + 1 < radix) :
    (sum.add term).value = sum.value + term.toNat := by
  unfold WordSum.add WordSum.value
  dsimp only
  simp only [Challenge.EvmProof.Word.word_toNat_add,
    Challenge.EvmProof.Word.word_toNat_lt]
  rw [show 2 ^ 256 = radix by rfl]
  have hsumWord := sum.word.val.isLt
  have hterm := term.val.isLt
  change sum.word.toNat < radix at hsumWord
  change term.toNat < radix at hterm
  have hword : sum.word.toNat + term.toNat < 2 * radix := by
    omega
  rw [mod_eq_cond_sub hword]
  by_cases hoverflow : sum.word.toNat + term.toNat < radix
  · rw [if_pos hoverflow, if_neg (by omega), Nat.add_zero,
      Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [if_neg hoverflow, if_pos (by omega),
      Nat.mod_eq_of_lt hcarry]
    rw [Nat.mul_add, Nat.mul_one]
    omega

theorem WordSum.carry_add_le (sum : WordSum) (term : UInt256)
    (hcarry : sum.carry.toNat + 1 < radix) :
    (sum.add term).carry.toNat ≤ sum.carry.toNat + 1 := by
  unfold WordSum.add
  dsimp only
  simp only [Challenge.EvmProof.Word.word_toNat_add,
    Challenge.EvmProof.Word.word_toNat_lt]
  rw [show 2 ^ 256 = radix by rfl]
  split_ifs <;> rw [Nat.mod_eq_of_lt (by omega)]
  omega

/-- The high-word identity behind the EVM `mul`/`mulmod (base - 1)` trick.
The conditional subtraction is exactly the pair of wrapped `SUB`s used by the
source implementation. -/
theorem mulSplit_high_eq_mersenne {base a b : Nat} (hbase : 1 < base)
    (ha : a < base) (hb : b < base) :
    let words := mulSplit base a b
    let mm := (a * b) % (base - 1)
    (if mm < words.1 then base + mm - words.1 - 1 else mm - words.1) =
      words.2 := by
  dsimp only
  by_cases htwo : base = 2
  · subst base
    interval_cases a <;> interval_cases b <;>
      norm_num [mulSplit, splitAt]
  have hbase2 : 2 < base := by omega
  let lo := (mulSplit base a b).1
  let hi := (mulSplit base a b).2
  have hbase0 : 0 < base := by omega
  have hlo : lo < base := splitAt_low_lt hbase0
  have hhi : hi < base - 1 := by
    have ha' : a ≤ base - 1 := by omega
    have hb' : b ≤ base - 1 := by omega
    have hproduct : a * b ≤ (base - 1) * (base - 1) :=
      Nat.mul_le_mul ha' hb'
    have hstrict : a * b < (base - 1) * base :=
      hproduct.trans_lt ((Nat.mul_lt_mul_left (by omega : 0 < base - 1)).2
        (by omega : base - 1 < base))
    simpa [hi, mulSplit, splitAt, Nat.div_lt_iff_lt_mul hbase0]
      using hstrict
  have hreconstruct : lo + base * hi = a * b := by
    change joinAt base (mulSplit base a b) = a * b
    exact join_mulSplit hbase0 a b
  have hbaseMod : base % (base - 1) = 1 := by
    rw [Nat.mod_eq_sub_mod (by omega : base - 1 ≤ base)]
    have hdiff : base - (base - 1) = 1 := by omega
    rw [hdiff, Nat.mod_eq_of_lt (by omega)]
  have hmm : (a * b) % (base - 1) = (lo + hi) % (base - 1) := by
    have heq := congrArg (fun n => n % (base - 1)) hreconstruct
    simpa [Nat.add_mod, Nat.mul_mod, hbaseMod] using heq.symm
  have hsum : lo + hi < 2 * (base - 1) := by omega
  rw [hmm, mod_eq_cond_sub hsum]
  change (if (if lo + hi < base - 1 then lo + hi
      else lo + hi - (base - 1)) < lo then
        base + (if lo + hi < base - 1 then lo + hi
          else lo + hi - (base - 1)) - lo - 1
      else (if lo + hi < base - 1 then lo + hi
        else lo + hi - (base - 1)) - lo) = hi
  split_ifs <;> omega

theorem fullMul256_value (a b : UInt256) :
    (fullMul256 a b).value = a.toNat * b.toNat := by
  have hlo : (a * b).toNat = (a.toNat * b.toNat) % radix := by
    change (a.val * b.val).val = _
    rw [Fin.val_mul]
    rfl
  have hmax : (UInt256.lnot (UInt256.ofNat 0)).toNat = radix - 1 := by
    norm_num [UInt256.lnot, UInt256.ofNat, UInt256.toNat, UInt256.size, radix]
  have hmm :
      (UInt256.mulMod a b (UInt256.lnot (UInt256.ofNat 0))).toNat =
        (a.toNat * b.toNat) % (radix - 1) := by
    unfold UInt256.mulMod
    rw [if_neg]
    · rw [Challenge.EvmProof.Word.word_toNat_ofNat]
      rw [hmax]
      apply Nat.mod_eq_of_lt
      exact (Nat.mod_lt _ (by norm_num [radix])).trans
        (by norm_num [radix])
    · simpa [UInt256.toNat] using (show
        (UInt256.lnot (UInt256.ofNat 0)).toNat ≠ 0 by
          rw [hmax]
          norm_num [radix])
  unfold WideProduct.value fullMul256
  dsimp only
  rw [Challenge.EvmProof.Word.word_toNat_sub_cond]
  rw [Challenge.EvmProof.Word.word_toNat_lt]
  rw [Challenge.EvmProof.Word.word_toNat_sub_cond]
  rw [hlo, hmm]
  rw [show 2 ^ 256 = radix by rfl]
  have hhigh := mulSplit_high_eq_mersenne
    (base := radix) (a := a.toNat) (b := b.toNat)
    (by norm_num [radix]) a.val.isLt b.val.isLt
  dsimp only at hhigh
  simp only [mulSplit, splitAt] at hhigh
  have hloBound : a.toNat * b.toNat % radix < radix :=
    Nat.mod_lt _ radix_pos
  by_cases hborrow : a.toNat * b.toNat % (radix - 1) <
      a.toNat * b.toNat % radix
  · simp only [if_pos hborrow]
    rw [if_neg (by omega)]
    rw [if_pos hborrow] at hhigh
    rw [hhigh]
    simpa [joinAt, mulSplit, splitAt] using
      join_mulSplit (base := radix) radix_pos a.toNat b.toNat

  · simp only [if_neg hborrow, Nat.not_lt_zero, ↓reduceIte, Nat.sub_zero]
    rw [if_neg hborrow] at hhigh
    rw [hhigh]
    simpa [joinAt, mulSplit, splitAt] using
      join_mulSplit (base := radix) radix_pos a.toNat b.toNat

/-- A product of two words cannot have the maximal word as its high half. -/
theorem fullMul256_hi_lt_pred (a b : UInt256) :
    (fullMul256 a b).hi.toNat < radix - 1 := by
  have hvalue := fullMul256_value a b
  have ha : a.toNat ≤ radix - 1 := Nat.le_pred_of_lt a.val.isLt
  have hb : b.toNat ≤ radix - 1 := Nat.le_pred_of_lt b.val.isLt
  have hproduct : a.toNat * b.toNat ≤ (radix - 1) * (radix - 1) :=
    Nat.mul_le_mul ha hb
  have hpredPos : 0 < radix - 1 := Nat.sub_pos_of_lt radix_gt_one
  by_contra hnot
  have hhigh : radix - 1 ≤ (fullMul256 a b).hi.toNat :=
    Nat.le_of_not_gt hnot
  have hscaled : radix * (radix - 1) ≤
      radix * (fullMul256 a b).hi.toNat := Nat.mul_le_mul_left radix hhigh
  have htoProduct : radix * (radix - 1) ≤ a.toNat * b.toNat := by
    calc
      radix * (radix - 1) ≤ radix * (fullMul256 a b).hi.toNat := hscaled
      _ ≤ (fullMul256 a b).lo.toNat +
          radix * (fullMul256 a b).hi.toNat := Nat.le_add_left _ _
      _ = a.toNat * b.toNat := hvalue
  have hstrict : (radix - 1) * (radix - 1) < radix * (radix - 1) :=
    (Nat.mul_lt_mul_right hpredPos).2 (Nat.sub_lt radix_pos (by omega))
  exact (Nat.not_lt_of_ge (htoProduct.trans hproduct)) hstrict

/-- The high half of a word product is at most either operand. -/
theorem fullMul256_hi_le_right (a b : UInt256) :
    (fullMul256 a b).hi.toNat ≤ b.toNat := by
  have hvalue := fullMul256_value a b
  by_cases hb : b.toNat = 0
  · unfold WideProduct.value at hvalue
    rw [hb] at hvalue ⊢
    simp only [Nat.mul_zero] at hvalue
    have hmul : radix * (fullMul256 a b).hi.toNat = 0 :=
      Nat.eq_zero_of_add_eq_zero_left hvalue
    rcases Nat.mul_eq_zero.mp hmul with hradix | hhi
    · exact False.elim (Nat.ne_of_gt radix_pos hradix)
    · exact Nat.le_of_eq hhi
  · have hbpos : 0 < b.toNat := Nat.pos_of_ne_zero hb
    have ha := a.val.isLt
    change a.toNat < radix at ha
    have hproduct : a.toNat * b.toNat < radix * b.toNat :=
      (Nat.mul_lt_mul_right hbpos).2 ha
    have hscaled : radix * (fullMul256 a b).hi.toNat <
        radix * b.toNat := by
      calc
        radix * (fullMul256 a b).hi.toNat ≤
            (fullMul256 a b).lo.toNat +
              radix * (fullMul256 a b).hi.toNat := Nat.le_add_left _ _
        _ = a.toNat * b.toNat := hvalue
        _ < radix * b.toNat := hproduct
    exact Nat.le_of_lt ((Nat.mul_lt_mul_left radix_pos).mp hscaled)

/-- The source-style shift/splice schedule reconstructs exact doubling when
the mathematical result fits in two EVM words. -/
theorem doubleWide256_value (input : WideProduct)
    (hdouble : 2 * input.value < radix ^ 2) :
    (doubleWide256 input).value = 2 * input.value := by
  have hlo := input.lo.val.isLt
  have hhi := input.hi.val.isLt
  change input.lo.toNat < radix at hlo
  change input.hi.toNat < radix at hhi
  have hlow : (UInt256.shiftLeft input.lo (UInt256.ofNat 1)).toNat =
      (2 * input.lo.toNat) % radix := by
    rw [Challenge.EvmProof.Word.shiftLeft_toNat input.lo (by omega)]
    change (input.lo.toNat * 2) % radix = _
    rw [Nat.mul_comm]
  have hcarry : (UInt256.shiftRight input.lo (UInt256.ofNat 255)).toNat =
      input.lo.toNat / 2 ^ 255 := by
    rw [Challenge.EvmProof.Word.shiftRight_toNat input.lo (by omega)]
    exact Nat.shiftRight_eq_div_pow input.lo.toNat 255
  have hcarryLt : input.lo.toNat / 2 ^ 255 < 2 := by
    rw [Nat.div_lt_iff_lt_mul (by positivity)]
    change input.lo.toNat < radix
    exact hlo
  have hhighBound : 2 * input.hi.toNat + input.lo.toNat / 2 ^ 255 <
      radix := by
    unfold WideProduct.value at hdouble
    have hsplit := Nat.mod_add_div input.lo.toNat (2 ^ 255)
    have hmodLt := Nat.mod_lt input.lo.toNat (by positivity : 0 < 2 ^ 255)
    have hradix : radix = 2 * 2 ^ 255 := by
      norm_num [radix]
    rw [hradix] at hdouble ⊢
    have hdecomp :
        2 * (input.lo.toNat + (2 * 2 ^ 255) * input.hi.toNat) =
          2 * (input.lo.toNat % 2 ^ 255) +
            (2 * 2 ^ 255) *
              (2 * input.hi.toNat + input.lo.toNat / 2 ^ 255) := by
      omega
    by_contra hnot
    have htop : 2 * 2 ^ 255 ≤
        2 * input.hi.toNat + input.lo.toNat / 2 ^ 255 := by omega
    have hscaled := Nat.mul_le_mul_left (2 * 2 ^ 255) htop
    rw [hdecomp] at hdouble
    omega
  have hhighShift :
      (UInt256.shiftLeft input.hi (UInt256.ofNat 1)).toNat =
        2 * input.hi.toNat := by
    rw [Challenge.EvmProof.Word.shiftLeft_toNat input.hi (by omega)]
    change (input.hi.toNat * 2) % radix = _
    rw [Nat.mul_comm, Nat.mod_eq_of_lt (by omega)]
  have hor :
      (UInt256.lor
        (UInt256.shiftLeft input.hi (UInt256.ofNat 1))
        (UInt256.shiftRight input.lo (UInt256.ofNat 255))).toNat =
          2 * input.hi.toNat + input.lo.toNat / 2 ^ 255 := by
    rw [Challenge.EvmProof.Word.word_toNat_lor, hhighShift, hcarry]
    simpa [Nat.shiftLeft_eq, Nat.mul_comm] using
      (Nat.shiftLeft_add_eq_or_of_lt (i := 1)
        (b := input.lo.toNat / 2 ^ 255) hcarryLt input.hi.toNat).symm
  unfold doubleWide256 WideProduct.value
  dsimp only
  rw [hlow, hor]
  have hsplit := Nat.mod_add_div (2 * input.lo.toNat) radix
  have hdiv : (2 * input.lo.toNat) / radix =
      input.lo.toNat / 2 ^ 255 := by
    change (2 * input.lo.toNat) / (2 * 2 ^ 255) = _
    rw [Nat.mul_div_mul_left _ _ (by omega : 0 < 2)]
  rw [hdiv] at hsplit
  nlinarith

/-- The source-style low product reconstructs multiplication modulo two EVM
words. -/
theorem mulWideLow256_value (a b : WideProduct) :
    (mulWideLow256 a b).value = (a.value * b.value) % radix ^ 2 := by
  let low := fullMul256 a.lo b.lo
  let cross := low.hi.toNat + a.lo.toNat * b.hi.toNat +
    a.hi.toNat * b.lo.toNat
  have hlow := fullMul256_value a.lo b.lo
  change low.value = a.lo.toNat * b.lo.toNat at hlow
  have hhi : (low.hi + a.lo * b.hi + a.hi * b.lo).toNat =
      cross % radix := by
    dsimp only [cross]
    simp only [Challenge.EvmProof.Word.word_toNat_add,
      Challenge.EvmProof.Word.word_toNat_mul,
      show 2 ^ 256 = radix by rfl]
    simp [Nat.add_mod, Nat.mul_mod]
  have hcrossSplit : cross % radix + radix * (cross / radix) = cross :=
    Nat.mod_add_div cross radix
  have hresultLt : low.lo.toNat + radix * (cross % radix) < radix ^ 2 := by
    have hlo := low.lo.val.isLt
    have hcross := Nat.mod_lt cross radix_pos
    change low.lo.toNat < radix at hlo
    nlinarith
  have hdecomp : a.value * b.value =
      (low.lo.toNat + radix * (cross % radix)) +
        radix ^ 2 * (cross / radix + a.hi.toNat * b.hi.toNat) := by
    calc
      a.value * b.value =
          a.lo.toNat * b.lo.toNat + radix *
            (a.lo.toNat * b.hi.toNat + a.hi.toNat * b.lo.toNat) +
            radix ^ 2 * (a.hi.toNat * b.hi.toNat) := by
              unfold WideProduct.value
              ring
      _ = low.lo.toNat + radix * cross +
          radix ^ 2 * (a.hi.toNat * b.hi.toNat) := by
            unfold WideProduct.value at hlow
            rw [← hlow]
            dsimp only [cross]
            ring
      _ = (low.lo.toNat + radix * (cross % radix)) +
          radix ^ 2 * (cross / radix + a.hi.toNat * b.hi.toNat) := by
            nlinarith [hcrossSplit]
  unfold mulWideLow256
  change low.lo.toNat + radix *
      (low.hi + a.lo * b.hi + a.hi * b.lo).toNat =
        (a.value * b.value) % radix ^ 2
  rw [hhi, hdecomp, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt hresultLt]

theorem masked_sum_mod_eq_cond_sub {x y take modulus : Nat}
    (hx : x < modulus) (hy : y < modulus) (htake : take ≤ 1) :
    (x + take * y) % modulus =
      if x + take * y < modulus then x + take * y
      else x + take * y - modulus := by
  exact mod_eq_cond_sub (masked_sum_lt_twice hx hy htake)

/-- The bytecode selects its subtraction candidate exactly when the
mathematical sum is at least the modulus.  The first disjunct is the final
carry out of the fixed-width addition; the second is a borrow-free comparison
of the wrapped sum with the modulus. -/
theorem useSub_iff {total modulus bound : Nat} (hmodulus : modulus < bound) :
    (bound ≤ total ∨ modulus ≤ total % bound) ↔ modulus ≤ total := by
  constructor
  · rintro (hcarry | hwrapped)
    · exact hmodulus.le.trans hcarry
    · exact hwrapped.trans (Nat.mod_le total bound)
  · intro htotal
    by_cases hcarry : bound ≤ total
    · exact Or.inl hcarry
    · right
      rwa [Nat.mod_eq_of_lt (Nat.lt_of_not_ge hcarry)]

/-! ## Canonical carry recurrence -/

/-- Add two equally-sized little-endian limb lists, returning the result limbs
and the carry beyond their common width. -/
def addDigitLists : List Nat → List Nat → Nat → List Nat × Nat
  | [], [], carry => ([], carry)
  | x :: xs, y :: ys, carry =>
      let total := x + y + carry
      let next := addDigitLists xs ys (total / radix)
      (total % radix :: next.1, next.2)
  | _, _, carry => ([], carry)

theorem length_addDigitLists_left {xs ys : List Nat} {carry : Nat}
    (hlength : xs.length = ys.length) :
    (addDigitLists xs ys carry).1.length = xs.length := by
  induction xs generalizing ys carry with
  | nil =>
      cases ys <;> simp_all [addDigitLists]
  | cons x xs ih =>
      cases ys with
      | nil => simp_all
      | cons y ys =>
          have hlength' : xs.length = ys.length := by simpa using hlength
          simp [addDigitLists, ih hlength']

theorem addDigitLists_value {xs ys : List Nat} {carry : Nat}
    (hlength : xs.length = ys.length) :
    Nat.ofDigits radix (addDigitLists xs ys carry).1 +
        radix ^ xs.length * (addDigitLists xs ys carry).2 =
      Nat.ofDigits radix xs + Nat.ofDigits radix ys + carry := by
  induction xs generalizing ys carry with
  | nil =>
      cases ys <;> simp_all [addDigitLists]
  | cons x xs ih =>
      cases ys with
      | nil => simp_all
      | cons y ys =>
          have hlength' : xs.length = ys.length := by simpa using hlength
          let total := x + y + carry
          let next := addDigitLists xs ys (total / radix)
          have hnext := ih (carry := total / radix) hlength'
          have hdivide := Nat.mod_add_div total radix
          simp only [addDigitLists, Nat.ofDigits_cons,
            List.length_cons, pow_succ]
          simp only [total] at hnext hdivide
          nlinarith

theorem addDigitLists_append_single {xs ys : List Nat} {carry x y : Nat}
    (hlength : xs.length = ys.length) :
    addDigitLists (xs ++ [x]) (ys ++ [y]) carry =
      let before := addDigitLists xs ys carry
      let total := x + y + before.2
      (before.1 ++ [total % radix], total / radix) := by
  induction xs generalizing ys carry with
  | nil =>
      cases ys with
      | nil => rfl
      | cons y ys => simp at hlength
  | cons head xs ih =>
      cases ys with
      | nil => simp at hlength
      | cons other ys =>
          have hlength' : xs.length = ys.length := by simpa using hlength
          simp only [List.cons_append, addDigitLists]
          rw [ih hlength']

theorem addDigitLists_digits_lt {xs ys : List Nat} {carry digit : Nat}
    (hdigit : digit ∈ (addDigitLists xs ys carry).1) : digit < radix := by
  induction xs generalizing ys carry with
  | nil =>
      cases ys <;> simp_all [addDigitLists]
  | cons x xs ih =>
      cases ys with
      | nil => simp_all [addDigitLists]
      | cons y ys =>
          simp only [addDigitLists, List.mem_cons] at hdigit
          rcases hdigit with rfl | hdigit
          · exact Nat.mod_lt _ radix_pos
          · exact ih hdigit

theorem addDigitLists_carry_le_one {xs ys : List Nat} {carry : Nat}
    (hlength : xs.length = ys.length)
    (hxs : ∀ digit ∈ xs, digit < radix)
    (hys : ∀ digit ∈ ys, digit < radix) (hcarry : carry ≤ 1) :
    (addDigitLists xs ys carry).2 ≤ 1 := by
  induction xs generalizing ys carry with
  | nil =>
      cases ys <;> simp_all [addDigitLists]
  | cons x xs ih =>
      cases ys with
      | nil => simp_all
      | cons y ys =>
          have hlength' : xs.length = ys.length := by simpa using hlength
          have hx : x < radix := hxs x (by simp)
          have hy : y < radix := hys y (by simp)
          have hquotient : (x + y + carry) / radix ≤ 1 := by
            rw [Nat.div_le_iff_le_mul radix_pos]
            omega
          simp only [addDigitLists]
          exact ih hlength' (fun digit hdigit => hxs digit (by simp [hdigit]))
            (fun digit hdigit => hys digit (by simp [hdigit])) hquotient

theorem ofDigits_map_mul (digits : List Nat) (take : Nat) :
    Nat.ofDigits radix (digits.map (take * ·)) =
      take * Nat.ofDigits radix digits := by
  induction digits with
  | nil => simp
  | cons digit digits ih =>
      simp [Nat.ofDigits_cons, ih]
      ring

theorem addDigitLists_masked_value_mod {xs ys : List Nat} {take : Nat}
    (hlength : xs.length = ys.length) :
    Nat.ofDigits radix (addDigitLists xs (ys.map (take * ·)) 0).1 =
      (Nat.ofDigits radix xs + take * Nat.ofDigits radix ys) %
        radix ^ xs.length := by
  have hmaskedLength : xs.length = (ys.map (take * ·)).length := by
    simpa using hlength
  have hvalue := addDigitLists_value (carry := 0) hmaskedLength
  rw [ofDigits_map_mul] at hvalue
  simp only [Nat.add_zero] at hvalue
  have hresultLength := length_addDigitLists_left
    (carry := 0) hmaskedLength
  have hresultDigits : ∀ digit ∈
      (addDigitLists xs (ys.map (take * ·)) 0).1, digit < radix :=
    fun digit hdigit => addDigitLists_digits_lt hdigit
  have hresultLt :
      Nat.ofDigits radix (addDigitLists xs (ys.map (take * ·)) 0).1 <
        radix ^ xs.length := by
    rw [← hresultLength]
    exact Nat.ofDigits_lt_base_pow_length radix_gt_one hresultDigits
  rw [← hvalue, Nat.add_mod, Nat.mul_mod, Nat.mod_self, Nat.zero_mul,
    Nat.zero_mod, Nat.add_zero, Nat.mod_mod]
  exact (Nat.mod_eq_of_lt hresultLt).symm

theorem addDigitLists_masked_carry_le_one {xs ys : List Nat} {take : Nat}
    (hlength : xs.length = ys.length)
    (hxs : ∀ digit ∈ xs, digit < radix)
    (hys : ∀ digit ∈ ys, digit < radix) (htake : take ≤ 1) :
    (addDigitLists xs (ys.map (take * ·)) 0).2 ≤ 1 := by
  apply addDigitLists_carry_le_one (by simpa using hlength) hxs
  · intro digit hdigit
    simp only [List.mem_map] at hdigit
    rcases hdigit with ⟨source, hsource, rfl⟩
    have hsourceLt := hys source hsource
    interval_cases take
    · simpa using radix_pos
    · simpa using hsourceLt
  · omega

private theorem div_eq_one_of_le_of_lt_twice {value divisor : Nat}
    (_hdivisor : 0 < divisor) (hle : divisor ≤ value)
    (hlt : value < 2 * divisor) : value / divisor = 1 := by
  apply Nat.div_eq_of_lt_le
  · simpa using hle
  · omega

/-- The two EVM overflow tests in one `addMaskedMod` limb iteration compute
exactly the carry quotient of the three-term natural sum. -/
theorem addCarryBits {x y carry : Nat}
    (hx : x < radix) (hy : y < radix) (hcarry : carry ≤ 1) :
    ((if (x + y) % radix < x then 1 else 0) |||
        (if ((x + y) % radix + carry) % radix < (x + y) % radix
          then 1 else 0)) =
      (x + y + carry) / radix := by
  have hsum : x + y < 2 * radix := by omega
  by_cases hwrap : x + y < radix
  · rw [Nat.mod_eq_of_lt hwrap]
    have hnotFirst : ¬ x + y < x := by omega
    simp only [if_neg hnotFirst, Nat.zero_or]
    by_cases htotal : x + y + carry < radix
    · rw [Nat.mod_eq_of_lt htotal, if_neg (by omega),
        Nat.div_eq_of_lt htotal]
    · have htotalLe : radix ≤ x + y + carry := by omega
      have htotalTwo : x + y + carry < 2 * radix := by omega
      have hzero : x + y + carry - radix = 0 := by omega
      have hsumPos : 0 < x + y := by
        have := radix_gt_one
        omega
      rw [mod_eq_cond_sub htotalTwo, if_neg htotal,
        hzero, if_pos hsumPos,
        div_eq_one_of_le_of_lt_twice radix_pos htotalLe htotalTwo]
  · have hwrapLe : radix ≤ x + y := by omega
    rw [mod_eq_cond_sub hsum, if_neg hwrap]
    have hfirst : x + y - radix < x := by omega
    rw [if_pos hfirst]
    have hdiv : (x + y + carry) / radix = 1 :=
      div_eq_one_of_le_of_lt_twice radix_pos (by omega) (by omega)
    rw [hdiv]
    split <;> norm_num

/-! ## Canonical borrow recurrence -/

/-- Subtract the second equally-sized little-endian limb list from the first,
returning the wrapped result and the final borrow. -/
def subDigitLists : List Nat → List Nat → Nat → List Nat × Nat
  | [], [], borrow => ([], borrow)
  | x :: xs, y :: ys, borrow =>
      let nextBorrow := if x < y + borrow then 1 else 0
      let digit := x + radix * nextBorrow - y - borrow
      let next := subDigitLists xs ys nextBorrow
      (digit :: next.1, next.2)
  | _, _, borrow => ([], borrow)

theorem subDigitLists_append_single {xs ys : List Nat} {borrow x y : Nat}
    (hlength : xs.length = ys.length) :
    subDigitLists (xs ++ [x]) (ys ++ [y]) borrow =
      let before := subDigitLists xs ys borrow
      let nextBorrow := if x < y + before.2 then 1 else 0
      (before.1 ++ [x + radix * nextBorrow - y - before.2], nextBorrow) := by
  induction xs generalizing ys borrow with
  | nil =>
      cases ys with
      | nil => rfl
      | cons y ys => simp at hlength
  | cons head xs ih =>
      cases ys with
      | nil => simp at hlength
      | cons other ys =>
          have hlength' : xs.length = ys.length := by simpa using hlength
          simp only [List.cons_append, subDigitLists]
          rw [ih hlength']
          rfl

theorem subDigitLists_value {xs ys : List Nat} {borrow : Nat}
    (hlength : xs.length = ys.length)
    (hxs : ∀ digit ∈ xs, digit < radix)
    (hys : ∀ digit ∈ ys, digit < radix) (hborrow : borrow ≤ 1) :
    Nat.ofDigits radix (subDigitLists xs ys borrow).1 +
        Nat.ofDigits radix ys + borrow =
      Nat.ofDigits radix xs +
        radix ^ xs.length * (subDigitLists xs ys borrow).2 := by
  induction xs generalizing ys borrow with
  | nil =>
      cases ys <;> simp_all [subDigitLists]
  | cons x xs ih =>
      cases ys with
      | nil => simp_all
      | cons y ys =>
          have hlength' : xs.length = ys.length := by simpa using hlength
          have hx : x < radix := hxs x (by simp)
          have hy : y < radix := hys y (by simp)
          let nextBorrow := if x < y + borrow then 1 else 0
          have hnextBorrow : nextBorrow ≤ 1 := by
            dsimp only [nextBorrow]
            split <;> omega
          have hstep :
              x + radix * nextBorrow - y - borrow + y + borrow =
                x + radix * nextBorrow := by
            dsimp only [nextBorrow]
            split <;> omega
          have hnext := ih hlength'
            (fun digit hdigit => hxs digit (by simp [hdigit]))
            (fun digit hdigit => hys digit (by simp [hdigit])) hnextBorrow
          simp only [subDigitLists, Nat.ofDigits_cons, List.length_cons,
            pow_succ]
          dsimp only [nextBorrow] at hstep hnext ⊢
          nlinarith

theorem subDigitLists_borrow_le_one {xs ys : List Nat} {borrow : Nat}
    (hlength : xs.length = ys.length) (hborrow : borrow ≤ 1) :
    (subDigitLists xs ys borrow).2 ≤ 1 := by
  induction xs generalizing ys borrow with
  | nil =>
      cases ys <;> simp_all [subDigitLists]
  | cons x xs ih =>
      cases ys with
      | nil => simp_all
      | cons y ys =>
          have hlength' : xs.length = ys.length := by simpa using hlength
          simp only [subDigitLists]
          exact ih hlength' (by split <;> simp)

theorem subDigitLists_digits_lt {xs ys : List Nat} {borrow digit : Nat}
    (hlength : xs.length = ys.length)
    (hxs : ∀ value ∈ xs, value < radix)
    (hys : ∀ value ∈ ys, value < radix) (hborrow : borrow ≤ 1)
    (hdigit : digit ∈ (subDigitLists xs ys borrow).1) : digit < radix := by
  induction xs generalizing ys borrow digit with
  | nil =>
      cases ys <;> simp_all [subDigitLists]
  | cons x xs ih =>
      cases ys with
      | nil => simp_all
      | cons y ys =>
          have hlength' : xs.length = ys.length := by simpa using hlength
          have hx : x < radix := hxs x (by simp)
          have hy : y < radix := hys y (by simp)
          simp only [subDigitLists, List.mem_cons] at hdigit
          rcases hdigit with rfl | hdigit
          · split <;> omega
          · apply ih hlength'
              (fun value hvalue => hxs value (by simp [hvalue]))
              (fun value hvalue => hys value (by simp [hvalue]))
              (by split <;> simp) hdigit

/-- Natural-number specification of the EVM's two-stage `SUB`/`LT` borrow
sequence for one limb. -/
theorem subLimbBits {x y borrow : Nat}
    (hx : x < radix) (hy : y < radix) (hborrow : borrow ≤ 1) :
    let difference := if x < y then radix + x - y else x - y
    let digit := if difference < borrow then radix + difference - borrow
      else difference - borrow
    let nextBorrow := if x < y + borrow then 1 else 0
    digit = x + radix * nextBorrow - y - borrow ∧
      ((if x < y then 1 else 0) |||
        (if difference < borrow then 1 else 0)) = nextBorrow := by
  dsimp only
  interval_cases borrow
  · by_cases hxy : x < y
    · rw [if_pos hxy, if_neg (by omega), if_pos (by omega),
        if_pos hxy, if_neg (by omega)]
      constructor
      · omega
      · norm_num
    · rw [if_neg hxy, if_neg (by omega), if_neg (by omega),
        if_neg hxy, if_neg (by omega)]
      constructor <;> norm_num
  · by_cases hxy : x < y
    · have hdiffPos : 0 < radix + x - y := by omega
      rw [if_pos hxy, if_neg (by omega), if_pos (by omega),
        if_pos hxy, if_neg (by omega)]
      constructor
      · omega
      · norm_num
    · rw [if_neg hxy, if_neg hxy]
      by_cases heq : x = y
      · subst x
        rw [Nat.sub_self, if_pos (by omega), if_pos (by omega),
          if_pos (by omega)]
        constructor <;> norm_num
      · have hyxStrict : y < x := by omega
        have hdiffPos : 0 < x - y := by omega
        rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
        constructor
        · omega
        · norm_num

end Challenge.EvmProof.Limbs
