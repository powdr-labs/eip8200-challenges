import Challenge.EvmProof.Word
set_option warningAsError true
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

/-!
# The 32-bit reasoning layer for the optimized SHA-256 artifact

The optimized artifact rests on two facts that the reference implementation
never needed, and this file turns each into a *simp-normal* rewrite so that
proofs about round code never reason about them by hand.

**1. `toUInt32` is a homomorphism** — the formal content of "lazy masking".
The artifact leaves garbage above bit 31 in every intermediate, because ADD
carries only upward and the final `& 0xffffffff` erases it.  Formally: the
low-32-bit projection commutes with `+`, `&&&`, `|||`, `^^^`, and it absorbs
`mask32`.  Once those are simp lemmas, a round's raw EVM expression collapses
to the corresponding SHA expression automatically, and *no* intermediate
masking obligation is ever generated.

**2. Rotation by doubling** — for a 32-bit `w`, `dbl w = w * (2^32 + 1)` holds
two copies of `w`, so a single right shift extracts either a rotation (shift
`< 32`) or a plain shift (shift `≥ 32`).  Combined with shift composition,
every Sigma/sigma gadget in the artifact is a chain of `SHR`s over one `dbl`.
-/

namespace Challenge.Sha256.Fast

open EvmSemantics
open Challenge.EvmProof.Word

abbrev W256 := EvmSemantics.UInt256

/-- The artifact's doubling constant, in the operand order the stepper
produces (`PUSH k; MUL` puts the constant on top). -/
def dbl (x : W256) : W256 := UInt256.ofNat 0x100000001 * x

/-! ## 0. A reusable tactic for 32-bit bitwise identities

The obvious tool is `bv_decide`, and it must not be used: it closes these
goals but adds a `._native.bv_decide.ax_N` axiom, and the challenge admits
only `propext`, `Classical.choice`, `Quot.sound`.  `native_decide` is out for
the same reason, and plain `decide` is hopeless (2^96 cases for a ternary
identity).  Instead: push through `UInt32.toBitVec`, take bit extensionality,
normalise to `Bool` connectives on the `i`-th bits, and let `grind` do the
Boolean case analysis.  `grind` finds the atoms itself, so the tactic is
independent of how many variables the identity mentions. -/

macro "bit_blast32" : tactic =>
  `(tactic|
    (apply UInt32.toBitVec_inj.mp
     ext i
     have hall : (UInt32.toBitVec 4294967295)[i] = true := by revert i; decide
     simp only [UInt32.toBitVec_xor, UInt32.toBitVec_and, UInt32.toBitVec_or,
       BitVec.getElem_xor, BitVec.getElem_and, BitVec.getElem_or, hall]
     grind))

/-! ## 1. The homomorphism layer -/

@[simp] theorem toUInt32_land (x y : W256) :
    toUInt32 (x &&& y) = toUInt32 x &&& toUInt32 y := by
  apply ofUInt32_injective
  rw [← mask32_eq_ofUInt32, mask32_and]

@[simp] theorem toUInt32_mask32 (x : W256) : toUInt32 (mask32 x) = toUInt32 x := by
  apply UInt32.toNat_inj.mp
  rw [toUInt32_toNat, mask32_toNat, toUInt32_toNat,
    show (0xffffffff : Nat) = 2 ^ 32 - 1 by norm_num,
    Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_mod_of_dvd _ dvd_rfl

/-! ## 2. Shift composition -/

@[simp] theorem shiftRight_shiftRight (x : W256) (a b : Nat)
    (ha : a < 256) (hb : b < 256) (hab : a + b < 256) :
    UInt256.shiftRight (UInt256.shiftRight x (UInt256.ofNat a)) (UInt256.ofNat b) =
      UInt256.shiftRight x (UInt256.ofNat (a + b)) := by
  apply word_ext
  rw [shiftRight_toNat _ hb, shiftRight_toNat _ ha, shiftRight_toNat _ hab,
    Nat.shiftRight_add]

/-! ## 3. Rotation by doubling -/

theorem word_toNat_mul (a b : W256) :
    (a * b).toNat = (a.toNat * b.toNat) % 2 ^ 256 := by
  change (a.val * b.val).val = _
  rw [Fin.val_mul]
  rfl

theorem dbl_toNat (w : UInt32) :
    (dbl (ofUInt32 w)).toNat = w.toNat + w.toNat * 2 ^ 32 := by
  have hw : w.toNat < 2 ^ 32 := w.toNat_lt
  unfold dbl
  rw [word_toNat_mul, word_toNat_ofNat, ofUInt32_toNat]
  have h : 4294967297 * w.toNat ≤ 4294967297 * 4294967295 :=
    Nat.mul_le_mul_left _ (by omega)
  omega

/-- The arithmetic heart: shifting the doubled word right by `n < 32` splits
into the low part of `w` shifted down and the high copy shifted up — which is
precisely the reference's `SHR/SHL/OR` rotation idiom. -/
theorem nat_dbl_shiftRight (W n : Nat) (hW : W < 2 ^ 32) (hn : n ≤ 32) :
    (W + W * 2 ^ 32) >>> n = (W >>> n) ||| (W * 2 ^ (32 - n)) := by
  have hsplit : W * 2 ^ 32 = W * 2 ^ (32 - n) * 2 ^ n := by
    rw [Nat.mul_assoc, ← Nat.pow_add]
    congr 2
    omega
  have hlow : W >>> n < 2 ^ (32 - n) := by
    rw [Nat.shiftRight_eq_div_pow]
    apply Nat.div_lt_of_lt_mul
    have hpow : (2 : Nat) ^ n * 2 ^ (32 - n) = 2 ^ 32 := by
      rw [← Nat.pow_add]; congr 1; omega
    omega
  have key := Nat.shiftLeft_add_eq_or_of_lt hlow W
  rw [Nat.shiftLeft_eq] at key
  rw [Nat.shiftRight_eq_div_pow, hsplit, Nat.add_mul_div_right _ _ (Nat.two_pow_pos n),
    ← Nat.shiftRight_eq_div_pow, Nat.add_comm, key, Nat.or_comm]

theorem shiftRight_dbl (w : UInt32) (n : Nat) (hn0 : 0 < n) (hn : n < 32) :
    UInt256.shiftRight (dbl (ofUInt32 w)) (UInt256.ofNat n) =
      UInt256.shiftRight (ofUInt32 w) (UInt256.ofNat n) |||
        UInt256.shiftLeft (ofUInt32 w) (UInt256.ofNat (32 - n)) := by
  have hw : w.toNat < 2 ^ 32 := w.toNat_lt
  have hshl : UInt256.shiftLeft (ofUInt32 w) (UInt256.ofNat (32 - n)) =
      UInt256.ofNat (w.toNat * 2 ^ (32 - n)) := by
    have := shiftLeft_ofNat (value := w.toNat) (shift := 32 - n)
      (by omega) (by omega) (by
        have : w.toNat * 2 ^ (32 - n) ≤ w.toNat * 2 ^ 32 :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))
        have h2 : w.toNat * 2 ^ 32 ≤ 4294967295 * 2 ^ 32 :=
          Nat.mul_le_mul_right _ (by omega)
        omega)
    simpa [ofUInt32] using this
  have hlor : ∀ a b : W256, (a ||| b).toNat = a.toNat ||| b.toNat := word_toNat_lor
  have hbound : w.toNat * 2 ^ (32 - n) < 2 ^ 256 := by
    have h1 : w.toNat * 2 ^ (32 - n) ≤ w.toNat * 2 ^ 32 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))
    have h2 : w.toNat * 2 ^ 32 ≤ 4294967295 * 2 ^ 32 :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  apply word_ext
  rw [hshl, hlor, shiftRight_toNat _ (show n < 256 by omega),
    shiftRight_toNat _ (show n < 256 by omega), dbl_toNat, ofUInt32_toNat,
    word_toNat_ofNat, Nat.mod_eq_of_lt hbound]
  exact nat_dbl_shiftRight w.toNat n hw (by omega)

/-- Shift amounts at or above 32 read the *upper* copy, giving a plain
logical shift with nothing above bit 31 — this is what lets `σ0`/`σ1` take
their `SHR` terms from the same doubled word as their rotations. -/
theorem shiftRight_dbl_high (w : UInt32) (n : Nat) (hn : n < 32) :
    UInt256.shiftRight (dbl (ofUInt32 w)) (UInt256.ofNat (32 + n)) =
      ofUInt32 (w >>> UInt32.ofNat n) := by
  have hw : w.toNat < 2 ^ 32 := w.toNat_lt
  apply word_ext
  rw [shiftRight_toNat _ (by omega), dbl_toNat, ofUInt32_toNat,
    UInt32.toNat_shiftRight, UInt32.toNat_ofNat',
    Nat.mod_eq_of_lt (show n < 2 ^ 32 by omega), Nat.shiftRight_add]
  congr 1 <;> (try rw [Nat.shiftRight_eq_div_pow]) <;> omega

/-! ## 4. The two gadget shapes

Every Sigma/sigma in the artifact is one of exactly two code shapes: the
doubled word shifted right three times in a chain, with the three
intermediates XORed.  `Σ0`/`Σ1` keep all three shifts below 32 (three
rotations); `σ0`/`σ1` put the last one at `32 + k` (two rotations and a plain
shift, read off the same doubled word).  These two lemmas are proved once and
instantiated 224 times per compressed block. -/

/-- The stepper emits the doubling as a bare multiplication by the pushed
constant; fold it back so the `dbl` lemmas apply. -/
@[simp] theorem dbl_fold (x : W256) :
    UInt256.ofNat 4294967297 * x = dbl x := rfl

@[simp] theorem toUInt32_ofNat (n : Nat) :
    toUInt32 (UInt256.ofNat n) = UInt32.ofNat n := by
  apply UInt32.toNat_inj.mp
  rw [toUInt32_toNat, word_toNat_ofNat, UInt32.toNat_ofNat']
  exact Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega))

/-! The stepper emits `UInt256.xor`/`UInt256.land` and puts a pushed constant
on *top* of the stack, so the simp set must be keyed on those exact forms
rather than on the `^^^`/`&&&` notation. -/

@[simp] theorem toUInt32_xor' (a b : W256) :
    toUInt32 (UInt256.xor a b) = toUInt32 a ^^^ toUInt32 b := toUInt32_xor a b

@[simp] theorem toUInt32_land' (a b : W256) :
    toUInt32 (UInt256.land a b) = toUInt32 a &&& toUInt32 b := toUInt32_land a b

/-- `toUInt32` sees through the doubling: the low half of `dbl w` is `w`.
This is what lets the artifact store the message schedule pre-doubled. -/
@[simp] theorem toUInt32_dbl (w : UInt32) : toUInt32 (dbl (ofUInt32 w)) = w := by
  apply UInt32.toNat_inj.mp
  rw [toUInt32_toNat, dbl_toNat]
  have hw : w.toNat < 2 ^ 32 := w.toNat_lt
  omega

/-- The artifact's truncation: `PUSH 0xffffffff; AND` leaves the mask on top,
so the constant is the *first* operand. -/
def maskC (v : W256) : W256 := UInt256.land (UInt256.ofNat 0xffffffff) v

theorem land_comm (a b : W256) : UInt256.land a b = UInt256.land b a := by
  apply word_ext
  have h : ∀ x y : W256, (UInt256.land x y).toNat = x.toNat &&& y.toNat :=
    word_toNat_land
  rw [h, h, Nat.and_comm]

@[simp] theorem maskC_eq (v : W256) : maskC v = ofUInt32 (toUInt32 v) := by
  unfold maskC
  rw [land_comm]
  exact mask32_eq_ofUInt32 v

/-- The artifact's Sigma/sigma code shape: three chained right shifts of a
doubled word, XORed in the order the stack produces them. -/
def sigmaChain (x : W256) (s0 d1 d2 : Nat) : W256 :=
  UInt256.xor
    (UInt256.xor
      (UInt256.shiftRight (UInt256.shiftRight
        (UInt256.shiftRight x (UInt256.ofNat s0)) (UInt256.ofNat d1))
          (UInt256.ofNat d2))
      (UInt256.shiftRight (UInt256.shiftRight x (UInt256.ofNat s0))
        (UInt256.ofNat d1)))
    (UInt256.shiftRight x (UInt256.ofNat s0))

@[simp] theorem toUInt32_shiftRight_dbl (w : UInt32) (n : Nat)
    (hn0 : 0 < n) (hn : n < 32) :
    toUInt32 (UInt256.shiftRight (dbl (ofUInt32 w)) (UInt256.ofNat n)) =
      EvmSemantics.Crypto.Sha256.rotr32 w n := by
  rw [shiftRight_dbl w n hn0 hn, ← toUInt32_mask32, evm_rotr32 w n hn0 hn,
    toUInt32_ofUInt32]

/-- Companion to `toUInt32_shiftRight_dbl` for shift amounts at or above 32:
same left-hand side, disjoint side condition, so simp picks whichever
applies. -/
@[simp] theorem toUInt32_shiftRight_dbl_high (w : UInt32) (n : Nat)
    (hlo : 32 ≤ n) (hhi : n < 64) :
    toUInt32 (UInt256.shiftRight (dbl (ofUInt32 w)) (UInt256.ofNat n)) =
      EvmSemantics.Crypto.Sha256.shr32 w (n - 32) := by
  have h : n = 32 + (n - 32) := by omega
  rw [show EvmSemantics.Crypto.Sha256.shr32 w (n - 32) = w >>> UInt32.ofNat (n - 32) from rfl]
  conv_lhs => rw [h]
  rw [shiftRight_dbl_high w (n - 32) (by omega), toUInt32_ofUInt32]

theorem gadget_rot3 (w : UInt32) (s0 d1 d2 : Nat)
    (h0 : 0 < s0) (h1 : 0 < d1) (h2 : 0 < d2) (hlt : s0 + d1 + d2 < 32) :
    toUInt32 (sigmaChain (dbl (ofUInt32 w)) s0 d1 d2) =
      EvmSemantics.Crypto.Sha256.rotr32 w s0 ^^^
        EvmSemantics.Crypto.Sha256.rotr32 w (s0 + d1) ^^^
        EvmSemantics.Crypto.Sha256.rotr32 w (s0 + d1 + d2) := by
  unfold sigmaChain
  rw [shiftRight_shiftRight _ s0 d1 (by omega) (by omega) (by omega),
    shiftRight_shiftRight _ (s0 + d1) d2 (by omega) (by omega) (by omega),
    toUInt32_xor', toUInt32_xor',
    toUInt32_shiftRight_dbl w s0 (by omega) (by omega),
    toUInt32_shiftRight_dbl w (s0 + d1) (by omega) (by omega),
    toUInt32_shiftRight_dbl w (s0 + d1 + d2) (by omega) (by omega)]
  ac_rfl

theorem gadget_rot2_shr (w : UInt32) (s0 d1 d2 k : Nat)
    (h0 : 0 < s0) (h1 : 0 < d1) (hs1 : s0 + d1 < 32)
    (hk : k < 32) (heq : s0 + d1 + d2 = 32 + k) :
    toUInt32 (sigmaChain (dbl (ofUInt32 w)) s0 d1 d2) =
      EvmSemantics.Crypto.Sha256.rotr32 w s0 ^^^
        EvmSemantics.Crypto.Sha256.rotr32 w (s0 + d1) ^^^
        EvmSemantics.Crypto.Sha256.shr32 w k := by
  unfold sigmaChain
  rw [shiftRight_shiftRight _ s0 d1 (by omega) (by omega) (by omega),
    shiftRight_shiftRight _ (s0 + d1) d2 (by omega) (by omega) (by omega),
    heq, toUInt32_xor', toUInt32_xor',
    shiftRight_dbl_high w k hk, toUInt32_ofUInt32,
    toUInt32_shiftRight_dbl w s0 (by omega) (by omega),
    toUInt32_shiftRight_dbl w (s0 + d1) (by omega) (by omega)]
  unfold EvmSemantics.Crypto.Sha256.shr32
  ac_rfl

/-- The four concrete gadgets, as `simp` lemmas.  Each Sigma/sigma occurrence
in the artifact matches one of these directly. -/
@[simp] theorem gadget_bigSigma1 (w : UInt32) :
    toUInt32 (sigmaChain (dbl (ofUInt32 w)) 6 5 14) =
      EvmSemantics.Crypto.Sha256.bigSigma1 w :=
  gadget_rot3 w 6 5 14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

@[simp] theorem gadget_bigSigma0 (w : UInt32) :
    toUInt32 (sigmaChain (dbl (ofUInt32 w)) 2 11 9) =
      EvmSemantics.Crypto.Sha256.bigSigma0 w :=
  gadget_rot3 w 2 11 9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

@[simp] theorem gadget_smallSigma1 (w : UInt32) :
    toUInt32 (sigmaChain (dbl (ofUInt32 w)) 17 2 23) =
      EvmSemantics.Crypto.Sha256.smallSigma1 w :=
  gadget_rot2_shr w 17 2 23 10 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

@[simp] theorem gadget_smallSigma0 (w : UInt32) :
    toUInt32 (sigmaChain (dbl (ofUInt32 w)) 7 11 17) =
      EvmSemantics.Crypto.Sha256.smallSigma0 w :=
  gadget_rot2_shr w 7 11 17 3 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

/-! ## 5. Ch and Maj in the artifact's cheaper forms -/

/-- `ch` in exactly the operand order `DUP f; DUP g; XOR; DUP e; AND; DUP g;
XOR` produces. -/
@[simp] theorem ch_eq (e f g : UInt32) :
    g ^^^ (e &&& (g ^^^ f)) = EvmSemantics.Crypto.Sha256.Ch e f g := by
  unfold EvmSemantics.Crypto.Sha256.Ch; bit_blast32

/-- `maj` in exactly the operand order the artifact generates. -/
@[simp] theorem maj_eq (a b c : UInt32) :
    (c &&& (b ^^^ a)) ^^^ (b &&& a) = EvmSemantics.Crypto.Sha256.Maj a b c := by
  unfold EvmSemantics.Crypto.Sha256.Maj; bit_blast32

/-! ## 6. One compression round

`rawRound` is the round exactly as the artifact computes it: operand orders as
the stack produces them, `w` the *doubled* schedule word, and the two words
written back are the new `a` and the new `e` (the only two that change). -/

def rawRound (a b c d e f g h k w : W256) : W256 × W256 :=
  let s1 := sigmaChain (dbl e) 6 5 14
  let ch := UInt256.xor g (UInt256.land e (UInt256.xor g f))
  let t1 := w + (k + (h + (ch + s1)))
  let s0 := sigmaChain (dbl a) 2 11 9
  let mj := UInt256.xor (UInt256.land c (UInt256.xor b a)) (UInt256.land b a)
  (maskC ((mj + s0) + t1), maskC (d + t1))

open EvmSemantics.Crypto.Sha256 in
theorem rawRound_correct (A B C D E F G H Kc Wt : UInt32) :
    rawRound (ofUInt32 A) (ofUInt32 B) (ofUInt32 C) (ofUInt32 D) (ofUInt32 E)
        (ofUInt32 F) (ofUInt32 G) (ofUInt32 H) (ofUInt32 Kc)
        (dbl (ofUInt32 Wt)) =
      (ofUInt32 ((H + bigSigma1 E + Ch E F G + Kc + Wt) +
          (bigSigma0 A + Maj A B C)),
       ofUInt32 (D + (H + bigSigma1 E + Ch E F G + Kc + Wt))) := by
  unfold rawRound
  simp only [maskC_eq, Prod.mk.injEq]
  constructor <;> (apply congrArg ofUInt32; simp; ac_rfl)

/-! ## 7. One message-schedule step

The artifact keeps `W` pre-doubled in memory, so a schedule step consumes four
doubled words and stores a doubled word.  Adding doubled values is harmless:
the upper copy only pollutes bits ≥ 32, which the `maskC` erases. -/

def rawSchedule (x2 x7 x15 x16 : W256) : W256 :=
  dbl (maskC (x16 + (x7 + (sigmaChain x15 7 11 17 + sigmaChain x2 17 2 23))))

open EvmSemantics.Crypto.Sha256 in
theorem rawSchedule_correct (W2 W7 W15 W16 : UInt32) :
    rawSchedule (dbl (ofUInt32 W2)) (dbl (ofUInt32 W7)) (dbl (ofUInt32 W15))
        (dbl (ofUInt32 W16)) =
      dbl (ofUInt32 (smallSigma1 W2 + W7 + smallSigma0 W15 + W16)) := by
  unfold rawSchedule
  rw [maskC_eq]
  apply congrArg dbl
  apply congrArg ofUInt32
  simp
  ac_rfl

end Challenge.Sha256.Fast
