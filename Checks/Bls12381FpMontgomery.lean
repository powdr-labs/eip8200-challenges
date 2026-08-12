import Challenge.Bls12381.ProofSupport.FpMontgomeryLawful

set_option warningAsError true

namespace Checks.Bls12381FpMontgomery

open EvmSemantics.Crypto.Bls12381
open EvmSemantics
open Challenge.Bls12381.ProofSupport

/-! The constants are written literally in `Fp.sol::_modexp.montMul2`. -/

example : Fp.montgomeryN0Inv.toNat =
    0x19ecca0e8eb2db4c16ef2ef0c8e30b48286adb92d9d113e889f3fffcfffcfffd :=
  Fp.montgomeryN0Inv_value

example : Fp.montgomeryR2Lo.toNat =
    0xcc0868ce6a76590c76e5bc3ff951c543861c23693de6a351fb73eaead26ebe58 :=
  Fp.montgomeryR2Lo_value

example : Fp.montgomeryR2Hi.toNat =
    0x0010a8c1a49a064ff0a85a3f35446d0b :=
  Fp.montgomeryR2Hi_value

example :
    (Fp.montgomeryN0Inv.toNat * Fp.modulusLo.toNat) %
        Challenge.EvmProof.Limbs.radix =
      Challenge.EvmProof.Limbs.radix - 1 :=
  Fp.montgomeryN0Inv_spec

example : Fp.montgomeryR2Value =
    Challenge.EvmProof.Limbs.radix ^ 4 % p :=
  Fp.montgomeryR2_spec

/-! First CIOS iteration: the source starts from zero and accumulates `x₀*y`. -/

example (x0 y0 y1 : UInt256) :
    Fp.montgomeryAccumulateZero x0 y0 y1 =
      let p0 := Challenge.EvmProof.Limbs.fullMul256 x0 y0
      let p1 := Challenge.EvmProof.Limbs.fullMul256 x0 y1
      let middle := Challenge.EvmProof.Limbs.addTwo256 p1.lo p0.hi
      { t0 := p0.lo
        t1 := middle.word
        t2 := p1.hi + middle.carry : Fp.MontgomeryState } :=
  rfl

example (x0 y0 y1 : UInt256) :
    (Fp.montgomeryAccumulateZero x0 y0 y1).value =
      x0.toNat * (y0.toNat + Challenge.EvmProof.Limbs.radix * y1.toNat) :=
  Fp.montgomeryAccumulateZero_value x0 y0 y1

example (x0 y0 y1 : UInt256) :
    (Fp.montgomeryAccumulateZero x0 y0 y1).t2.toNat <
      Challenge.EvmProof.Limbs.radix :=
  Fp.montgomeryAccumulateZero_top_lt x0 y0 y1

/-! Each CIOS reduction chooses `m` so the low word cancels exactly. -/

example (state : Fp.MontgomeryState) :
    Fp.montgomeryReductionMultiplier state =
      state.t0 * Fp.montgomeryN0Inv :=
  rfl

example (state : Fp.MontgomeryState) :
    Challenge.EvmProof.Limbs.radix * Fp.montgomeryReductionQuotient state =
      state.t0.toNat + Challenge.EvmProof.Limbs.radix * state.t1.toNat +
        Challenge.EvmProof.Limbs.radix * Challenge.EvmProof.Limbs.radix *
          state.t2.toNat +
        (Fp.montgomeryReductionMultiplier state).toNat * p :=
  Fp.montgomeryReduction_reconstruct state

example (state : Fp.MontgomeryState)
    (hbound : Fp.montgomeryReductionNumerator state <
      Challenge.EvmProof.Limbs.radix *
        (Challenge.EvmProof.Limbs.radix * Challenge.EvmProof.Limbs.radix)) :
    Fp.montgomeryReductionTopNat state < Challenge.EvmProof.Limbs.radix :=
  Fp.montgomeryReductionTopNat_lt state hbound

example (state : Fp.MontgomeryState)
    (hbound : Fp.montgomeryReductionNumerator state <
      Challenge.EvmProof.Limbs.radix *
        (Challenge.EvmProof.Limbs.radix * Challenge.EvmProof.Limbs.radix)) :
    (Fp.montgomeryReduceStep state).value =
      Fp.montgomeryReductionQuotient state :=
  Fp.montgomeryReduceStep_value state hbound

example (state : Fp.MontgomeryState)
    (hbound : Fp.montgomeryReductionNumerator state <
      Challenge.EvmProof.Limbs.radix *
        (Challenge.EvmProof.Limbs.radix * Challenge.EvmProof.Limbs.radix)) :
    Challenge.EvmProof.Limbs.radix *
        (Fp.montgomeryReduceStep state).value =
      Fp.montgomeryReductionNumerator state :=
  Fp.montgomeryReduceStep_scaled state hbound

example (state : Fp.MontgomeryState)
    (htop : Fp.montgomeryReductionTopNat state <
      Challenge.EvmProof.Limbs.radix) :
    (Fp.montgomeryReduceStep state).value =
      Fp.montgomeryReductionQuotient state :=
  Fp.montgomeryReduceStep_value_of_top_lt state htop

example (state : Fp.MontgomeryState)
    (htop : Fp.montgomeryReductionTopNat state <
      Challenge.EvmProof.Limbs.radix) :
    Challenge.EvmProof.Limbs.radix *
        (Fp.montgomeryReduceStep state).value =
      Fp.montgomeryReductionNumerator state :=
  Fp.montgomeryReduceStep_scaled_of_top_lt state htop

example {y : Fp.Limbs} (hy : Fp.Canonical y) :
    y.hi.toNat ≤ Fp.modulusHi.toNat :=
  Fp.canonical_hi_le_modulusHi hy

example (x0 : UInt256) {y : Fp.Limbs} (hy : Fp.Canonical y) :
    Fp.montgomeryReductionTopNat
        (Fp.montgomeryAccumulateZero x0 y.lo y.hi) <
      Challenge.EvmProof.Limbs.radix :=
  Fp.montgomeryFirstTop_lt x0 hy

example (x0 : UInt256) {y : Fp.Limbs} (hy : Fp.Canonical y) :
    Challenge.EvmProof.Limbs.radix *
        (Fp.montgomeryFirstReduce x0 y).value =
      Fp.montgomeryReductionNumerator
        (Fp.montgomeryAccumulateZero x0 y.lo y.hi) :=
  Fp.montgomeryFirstReduce_scaled x0 hy

example (state : Fp.MontgomeryState) (x1 : UInt256) (y : Fp.Limbs) :
    Fp.montgomeryAccumulateNext state x1 y =
      let lowSum := Challenge.EvmProof.Limbs.addTwo256 state.t0
        (Challenge.EvmProof.Limbs.fullMul256 x1 y.lo).lo
      let carry := (Challenge.EvmProof.Limbs.fullMul256 x1 y.lo).hi +
        lowSum.carry
      let highProduct := Challenge.EvmProof.Limbs.fullMul256 x1 y.hi
      let highSum := Challenge.EvmProof.Limbs.addTwo256 state.t1 highProduct.lo
      let shiftedSum := Challenge.EvmProof.Limbs.addTwo256 highSum.word carry
      { t0 := lowSum.word
        t1 := shiftedSum.word
        t2 := highProduct.hi + (highSum.carry + shiftedSum.carry) :
          Fp.MontgomeryState } :=
  rfl

example (state : Fp.MontgomeryState) (x1 : UInt256) (y : Fp.Limbs) :
    (Fp.montgomeryNextCarry state x1 y).toNat =
      (Fp.montgomeryNextLowProduct x1 y).hi.toNat +
        (Fp.montgomeryNextLowSum state x1 y).carry.toNat :=
  Fp.montgomeryNextCarry_value state x1 y

example (state : Fp.MontgomeryState) (x1 : UInt256) {y : Fp.Limbs}
    (hy : Fp.Canonical y) :
    Fp.montgomeryNextTopNat state x1 y <
      Challenge.EvmProof.Limbs.radix :=
  Fp.montgomeryNextTopNat_lt state x1 hy

example (state : Fp.MontgomeryState) (x1 : UInt256) {y : Fp.Limbs}
    (hy : Fp.Canonical y) :
    (Fp.montgomeryAccumulateNext state x1 y).t2.toNat =
      Fp.montgomeryNextTopNat state x1 y :=
  Fp.montgomeryAccumulateNext_t2_value state x1 hy

example (state : Fp.MontgomeryState) (x1 : UInt256) (y : Fp.Limbs) :
    (Fp.montgomeryNextLowSum state x1 y).word.toNat +
        Challenge.EvmProof.Limbs.radix *
          (Fp.montgomeryNextCarry state x1 y).toNat =
      state.t0.toNat + x1.toNat * y.lo.toNat :=
  Fp.montgomeryNextLow_reconstruct state x1 y

example (state : Fp.MontgomeryState) (x1 : UInt256) {y : Fp.Limbs}
    (hy : Fp.Canonical y) :
    (Fp.montgomeryAccumulateNext state x1 y).value =
      state.t0.toNat + Challenge.EvmProof.Limbs.radix * state.t1.toNat +
        x1.toNat * Fp.value y :=
  Fp.montgomeryAccumulateNext_value state x1 hy

example (state : Fp.MontgomeryState) (x1 : UInt256) {y : Fp.Limbs}
    (hy : Fp.Canonical y) (ht2 : state.t2 = UInt256.ofNat 0) :
    (Fp.montgomeryAccumulateNext state x1 y).value =
      state.value + x1.toNat * Fp.value y :=
  Fp.montgomeryAccumulateNext_value_of_t2_zero state x1 hy ht2

example (state : Fp.MontgomeryState) (x1 : UInt256) {y : Fp.Limbs}
    (hy : Fp.Canonical y) :
    (Fp.montgomeryAccumulateNext state x1 y).t2.toNat ≤ y.hi.toNat + 2 :=
  Fp.montgomeryAccumulateNext_t2_le state x1 hy

example (x y : Fp.Limbs) :
    Fp.montgomerySecondAccumulate x y =
      Fp.montgomeryAccumulateNext (Fp.montgomeryFirstReduce x.lo y) x.hi y :=
  rfl

example (x y : Fp.Limbs) :
    Fp.montgomeryCorrectionFactor x y <
      Challenge.EvmProof.Limbs.radix ^ 2 :=
  Fp.montgomeryCorrectionFactor_lt x y

example (x : Fp.Limbs) {y : Fp.Limbs} (hy : Fp.Canonical y) :
    Challenge.EvmProof.Limbs.radix * Challenge.EvmProof.Limbs.radix *
        (Fp.montgomeryResultWords x y).value =
      Fp.value x * Fp.value y + Fp.montgomeryCorrectionFactor x y * p :=
  Fp.montgomeryTwoStep_reconstruct x hy

example {x y : Fp.Limbs} (hx : Fp.Canonical x) (hy : Fp.Canonical y) :
    (Fp.montgomeryResultWords x y).value < 2 * p :=
  Fp.montgomeryResultWords_lt_two_modulus hx hy

example {x y : Fp.Limbs} (hx : Fp.Canonical x) (hy : Fp.Canonical y) :
    Fp.value (Fp.montMul2 x y) =
      (Fp.montgomeryResultWords x y).value % p :=
  Fp.value_montMul2 hx hy

example {x y : Fp.Limbs} (hx : Fp.Canonical x) (hy : Fp.Canonical y) :
    Fp.Canonical (Fp.montMul2 x y) :=
  Fp.canonical_montMul2 hx hy

example {x y : Fp.Limbs} (hx : Fp.Canonical x) (hy : Fp.Canonical y) :
    Fp.montgomeryRadix * Fp.value (Fp.montMul2 x y) ≡
      Fp.value x * Fp.value y [MOD p] :=
  Fp.montMul2_modEq hx hy

example {x y : Fp.Limbs} (hx : Fp.Canonical x) (hy : Fp.Canonical y) :
    (Fp.value (Fp.montMul2 x y) : PrimeField.LawfulFp) =
      (Fp.value x : PrimeField.LawfulFp) *
        (Fp.value y : PrimeField.LawfulFp) *
          (Fp.montgomeryRadix : PrimeField.LawfulFp)⁻¹ :=
  Fp.lawful_montMul2 hx hy

example {x y : Fp.Limbs} (hx : Fp.Canonical x) (hy : Fp.Canonical y) :
    PrimeField.finEquiv (Fp.toField (Fp.montMul2 x y)) =
      PrimeField.finEquiv (Fp.toField x) *
        PrimeField.finEquiv (Fp.toField y) *
          (Fp.montgomeryRadix : PrimeField.LawfulFp)⁻¹ :=
  Fp.toLawful_montMul2 hx hy

example : Fp.Canonical Fp.montgomeryR2 :=
  Fp.canonical_montgomeryR2

example : Fp.Canonical Fp.montgomeryOneInput :=
  Fp.canonical_montgomeryOneInput

example {a : Fp.Limbs} (ha : Fp.Canonical a) :
    (Fp.value (Fp.montgomeryEncode a) : PrimeField.LawfulFp) =
      (Fp.value a : PrimeField.LawfulFp) *
        (Fp.montgomeryRadix : PrimeField.LawfulFp) :=
  Fp.lawful_montgomeryEncode ha

example :
    (Fp.value Fp.montgomeryOne : PrimeField.LawfulFp) =
      (Fp.montgomeryRadix : PrimeField.LawfulFp) :=
  Fp.lawful_montgomeryOne

example : Fp.Canonical Fp.montgomeryOne :=
  Fp.canonical_montgomeryOne

example {a : Fp.Limbs} (ha : Fp.Canonical a) :
    (Fp.value (Fp.montgomeryDecode (Fp.montgomeryEncode a)) :
        PrimeField.LawfulFp) = (Fp.value a : PrimeField.LawfulFp) :=
  Fp.lawful_montgomeryDecode_encode ha

example {a : Fp.Limbs} (ha : Fp.Canonical a) :
    Fp.toField (Fp.montgomeryDecode (Fp.montgomeryEncode a)) = Fp.toField a :=
  Fp.toField_montgomeryDecode_encode ha

example {a : Fp.Limbs} (ha : Fp.Canonical a) :
    Fp.montgomeryDecode (Fp.montgomeryEncode a) = a :=
  Fp.montgomeryDecode_encode ha

example (x : Fp.Limbs) {y : Fp.Limbs} (hy : Fp.Canonical y) :
    Fp.montgomeryReductionTopNat (Fp.montgomerySecondAccumulate x y) <
      Challenge.EvmProof.Limbs.radix :=
  Fp.montgomerySecondTop_lt x hy

example (x : Fp.Limbs) {y : Fp.Limbs} (hy : Fp.Canonical y) :
    Challenge.EvmProof.Limbs.radix *
        (Fp.montgomerySecondReduce x y).value =
      Fp.montgomeryReductionNumerator (Fp.montgomerySecondAccumulate x y) :=
  Fp.montgomerySecondReduce_scaled x hy

example (result : Challenge.EvmProof.Limbs.WideProduct) :
    Fp.montgomeryFinalSubModulus result =
      let newZ0 := result.lo - Fp.modulusLo
      { hi := result.hi - Fp.modulusHi - UInt256.gt Fp.modulusLo result.lo
        lo := newZ0 : Challenge.EvmProof.Limbs.WideProduct } :=
  rfl

example (result : Challenge.EvmProof.Limbs.WideProduct) :
    Fp.montgomeryFinalCorrect result =
      if (Challenge.EvmProof.Limbs.wideGeWord result
        Fp.modulusWide).toNat ≠ 0
      then Fp.montgomeryFinalSubModulus result
      else result :=
  rfl

example (result : Challenge.EvmProof.Limbs.WideProduct) :
    Fp.montgomeryFinalCorrect result =
      if (UInt256.lor (UInt256.gt result.hi Fp.modulusHi)
        (UInt256.land (UInt256.eq result.hi Fp.modulusHi)
          (UInt256.isZero (UInt256.lt result.lo Fp.modulusLo)))).toNat ≠ 0
      then Fp.montgomeryFinalSubModulus result
      else result :=
  rfl

example (result : Challenge.EvmProof.Limbs.WideProduct) :
    (Fp.montgomeryFinalCorrect result).value =
      if p ≤ result.value then result.value - p else result.value :=
  Fp.montgomeryFinalCorrect_value result

example (x y : Fp.Limbs) :
    Fp.montMul2Words x y =
      Fp.montgomeryFinalCorrect (Fp.montgomeryResultWords x y) :=
  rfl

example (state : Fp.MontgomeryState) :
    (Fp.montgomeryReductionMultiplier state).toNat =
      (state.t0.toNat * Fp.montgomeryN0Inv.toNat) %
        Challenge.EvmProof.Limbs.radix :=
  Fp.montgomeryReductionMultiplier_value state

example (state : Fp.MontgomeryState) :
    (Fp.montgomeryReductionLowProduct state).lo.toNat =
      ((Fp.montgomeryReductionMultiplier state).toNat *
        Fp.modulusLo.toNat) % Challenge.EvmProof.Limbs.radix :=
  Fp.montgomeryReductionLowProduct_lo_value state

example : Fp.montgomeryN0Inv.toNat * Fp.modulusLo.toNat ≡
    Challenge.EvmProof.Limbs.radix - 1
      [MOD Challenge.EvmProof.Limbs.radix] :=
  Fp.montgomeryN0Inv_modEq

example (state : Fp.MontgomeryState) :
    (Fp.montgomeryReductionMultiplier state).toNat * Fp.modulusLo.toNat ≡
      state.t0.toNat * (Challenge.EvmProof.Limbs.radix - 1)
        [MOD Challenge.EvmProof.Limbs.radix] :=
  Fp.montgomeryReductionProduct_modEq state

example (state : Fp.MontgomeryState) :
    state.t0.toNat +
        (Fp.montgomeryReductionMultiplier state).toNat * Fp.modulusLo.toNat ≡ 0
      [MOD Challenge.EvmProof.Limbs.radix] :=
  Fp.montgomeryReductionCancellation_modEq state

example (state : Fp.MontgomeryState) :
    (Fp.montgomeryReductionLowSum state).word = UInt256.ofNat 0 :=
  Fp.montgomeryReductionLowSum_word_eq_zero state

example (state : Fp.MontgomeryState) :
    (Fp.montgomeryReductionCarry state).toNat =
      (Fp.montgomeryReductionLowProduct state).hi.toNat +
        (Fp.montgomeryReductionLowSum state).carry.toNat :=
  Fp.montgomeryReductionCarry_value state

/-! The reduction step preserves every source `ADD`/`LT` operand order. -/

example (state : Fp.MontgomeryState) :
    Fp.montgomeryReduceStep state =
      let highProduct := Challenge.EvmProof.Limbs.fullMul256
        (Fp.montgomeryReductionMultiplier state) Fp.modulusHi
      let highSum := Challenge.EvmProof.Limbs.addTwo256 state.t1 highProduct.lo
      let shiftedSum := Challenge.EvmProof.Limbs.addTwo256 highSum.word
        (Fp.montgomeryReductionCarry state)
      { t0 := shiftedSum.word
        t1 := state.t2 +
          (highProduct.hi + (highSum.carry + shiftedSum.carry))
        t2 := UInt256.ofNat 0 : Fp.MontgomeryState } :=
  rfl

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.montgomeryN0Inv_spec' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Fp.montgomeryN0Inv_spec

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.montgomeryR2_spec' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Fp.montgomeryR2_spec

/--
info: 'Challenge.Bls12381.ProofSupport.Fp.montgomeryAccumulateZero_value' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fp.montgomeryAccumulateZero_value

/--
info: 'Challenge.Bls12381.ProofSupport.Fp.montgomeryAccumulateZero_top_lt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fp.montgomeryAccumulateZero_top_lt

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.montgomeryReductionMultiplier_modEq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Fp.montgomeryReductionMultiplier_modEq

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.montgomeryN0Inv_modEq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp.montgomeryN0Inv_modEq

/--
info: 'Challenge.Bls12381.ProofSupport.Fp.montgomeryReductionProduct_modEq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fp.montgomeryReductionProduct_modEq

/--
info: 'Challenge.Bls12381.ProofSupport.Fp.montgomeryReductionCancellation_modEq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fp.montgomeryReductionCancellation_modEq

/--
info: 'Challenge.Bls12381.ProofSupport.Fp.montgomeryReductionLowSum_word_eq_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fp.montgomeryReductionLowSum_word_eq_zero

/--
info: 'Challenge.Bls12381.ProofSupport.Fp.montgomeryReductionCarry_value' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fp.montgomeryReductionCarry_value

/--
info: 'Challenge.Bls12381.ProofSupport.Fp.montgomeryReduction_reconstruct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fp.montgomeryReduction_reconstruct

/--
info: 'Challenge.Bls12381.ProofSupport.Fp.montgomeryReductionTopNat_lt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fp.montgomeryReductionTopNat_lt

/--
info: 'Challenge.Bls12381.ProofSupport.Fp.montgomeryReduceStep_value' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fp.montgomeryReduceStep_value

/--
info: 'Challenge.Bls12381.ProofSupport.Fp.montgomeryReduceStep_scaled' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fp.montgomeryReduceStep_scaled

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.montgomeryReduceStep_value_of_top_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Fp.montgomeryReduceStep_value_of_top_lt

/--
info: 'Challenge.Bls12381.ProofSupport.Fp.montgomeryReduceStep_scaled_of_top_lt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fp.montgomeryReduceStep_scaled_of_top_lt

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.canonical_hi_le_modulusHi' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Fp.canonical_hi_le_modulusHi

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.montgomeryFirstTop_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp.montgomeryFirstTop_lt

/--
info: 'Challenge.Bls12381.ProofSupport.Fp.montgomeryFirstReduce_scaled' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fp.montgomeryFirstReduce_scaled

/--
info: 'Challenge.Bls12381.ProofSupport.Fp.montgomeryNextCarry_value' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fp.montgomeryNextCarry_value

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.montgomeryNextTopNat_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp.montgomeryNextTopNat_lt

/--
info: 'Challenge.Bls12381.ProofSupport.Fp.montgomeryAccumulateNext_t2_value' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fp.montgomeryAccumulateNext_t2_value

/--
info: 'Challenge.Bls12381.ProofSupport.Fp.montgomeryNextLow_reconstruct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fp.montgomeryNextLow_reconstruct

/--
info: 'Challenge.Bls12381.ProofSupport.Fp.montgomeryAccumulateNext_value' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fp.montgomeryAccumulateNext_value

/--
info: 'Challenge.Bls12381.ProofSupport.Fp.montgomeryAccumulateNext_value_of_t2_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fp.montgomeryAccumulateNext_value_of_t2_zero

/--
info: 'Challenge.Bls12381.ProofSupport.Fp.montgomeryAccumulateNext_t2_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fp.montgomeryAccumulateNext_t2_le

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.montgomerySecondTop_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp.montgomerySecondTop_lt

/--
info: 'Challenge.Bls12381.ProofSupport.Fp.montgomerySecondReduce_scaled' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fp.montgomerySecondReduce_scaled

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.montgomeryFinalSubModulus_eq_subWide256' does not depend on any axioms -/
#guard_msgs in
#print axioms Fp.montgomeryFinalSubModulus_eq_subWide256

/--
info: 'Challenge.Bls12381.ProofSupport.Fp.montgomeryFinalCorrect_value' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fp.montgomeryFinalCorrect_value

/--
info: 'Challenge.Bls12381.ProofSupport.Fp.montgomeryCorrectionFactor_lt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fp.montgomeryCorrectionFactor_lt

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.montgomeryResultWords_value' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Fp.montgomeryResultWords_value

/--
info: 'Challenge.Bls12381.ProofSupport.Fp.montgomeryTwoStep_reconstruct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fp.montgomeryTwoStep_reconstruct

/--
info: 'Challenge.Bls12381.ProofSupport.Fp.montgomeryResultWords_lt_two_modulus' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fp.montgomeryResultWords_lt_two_modulus

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.oneConditionalSubtraction_eq_mod' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Fp.oneConditionalSubtraction_eq_mod

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.value_montMul2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp.value_montMul2

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.canonical_montMul2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp.canonical_montMul2

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.montMul2_modEq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp.montMul2_modEq

/--
info: 'Challenge.Bls12381.ProofSupport.Fp.lawful_montgomeryRadix_ne_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fp.lawful_montgomeryRadix_ne_zero

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.eq_mul_inv_of_mul_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp.eq_mul_inv_of_mul_eq

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.lawful_montMul2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp.lawful_montMul2

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.finEquiv_toField' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp.finEquiv_toField

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.toLawful_montMul2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp.toLawful_montMul2

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.canonical_montgomeryR2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp.canonical_montgomeryR2

/--
info: 'Challenge.Bls12381.ProofSupport.Fp.canonical_montgomeryOneInput' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fp.canonical_montgomeryOneInput

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.lawful_montgomeryR2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp.lawful_montgomeryR2

/--
info: 'Challenge.Bls12381.ProofSupport.Fp.canonical_montgomeryEncode' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fp.canonical_montgomeryEncode

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.lawful_montgomeryEncode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp.lawful_montgomeryEncode

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.lawful_montgomeryOne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp.lawful_montgomeryOne

/--
info: 'Challenge.Bls12381.ProofSupport.Fp.canonical_montgomeryDecode' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fp.canonical_montgomeryDecode

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.lawful_montgomeryDecode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp.lawful_montgomeryDecode

/--
info: 'Challenge.Bls12381.ProofSupport.Fp.lawful_montgomeryDecode_encode' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fp.lawful_montgomeryDecode_encode

/--
info: 'Challenge.Bls12381.ProofSupport.Fp.toField_montgomeryDecode_encode' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fp.toField_montgomeryDecode_encode

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.montgomeryDecode_encode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp.montgomeryDecode_encode

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.montgomeryN0Inv_value' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Fp.montgomeryN0Inv_value

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.montgomeryR2Lo_value' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Fp.montgomeryR2Lo_value

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.montgomeryR2Hi_value' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Fp.montgomeryR2Hi_value

/--
info: 'Challenge.Bls12381.ProofSupport.Fp.montgomeryAccumulateZeroTop_lt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fp.montgomeryAccumulateZeroTop_lt

/--
info: 'Challenge.Bls12381.ProofSupport.Fp.montgomeryAccumulateZero_top_value' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fp.montgomeryAccumulateZero_top_value

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.montgomeryReductionMultiplier_value' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Fp.montgomeryReductionMultiplier_value

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.montgomeryReductionLowProduct_lo_value' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Fp.montgomeryReductionLowProduct_lo_value

/--
info: 'Challenge.Bls12381.ProofSupport.Fp.montgomeryReductionCarry_scaled' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fp.montgomeryReductionCarry_scaled

/--
info: 'Challenge.Bls12381.ProofSupport.Fp.montgomeryReduction_reconstruct_numerator' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fp.montgomeryReduction_reconstruct_numerator

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.montgomeryReduceStep_t1_value_of_top_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Fp.montgomeryReduceStep_t1_value_of_top_lt

/--
info: 'Challenge.Bls12381.ProofSupport.Fp.montgomeryReduceStep_t1_value' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fp.montgomeryReduceStep_t1_value

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.montgomeryInitial_t2_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp.montgomeryInitial_t2_le

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.montgomeryTopConstant_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp.montgomeryTopConstant_lt

/--
info: 'Challenge.Bls12381.ProofSupport.Fp.montgomeryNextTopConstant_lt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fp.montgomeryNextTopConstant_lt

/--
info: 'Challenge.Bls12381.ProofSupport.Fp.montgomerySecondTopConstant_lt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fp.montgomerySecondTopConstant_lt

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.value_montMul2_words' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Fp.value_montMul2_words

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.value_montgomeryR2' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Fp.value_montgomeryR2

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.value_montgomeryOneInput' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Fp.value_montgomeryOneInput

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.canonical_montgomeryOne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp.canonical_montgomeryOne

end Checks.Bls12381FpMontgomery
