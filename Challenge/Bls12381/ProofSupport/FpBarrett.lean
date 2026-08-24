import Challenge.Bls12381.ProofSupport.FpBarrettSchedule

set_option warningAsError true

/-!
# BLS12-381 fixed Barrett quotient

This module identifies the two quotient words produced by the source-level
schedule with the high two words of `(x / 2^256) * mu`.  The proof is split
into small opaque declarations so checking the final theorem does not replay
the schedule reconstruction's larger proof term.
-/

namespace Challenge.Bls12381.ProofSupport.Fp

/-- Dropping the low product word is exactly division by the EVM radix. -/
theorem schoolbookHigh_eq_div (product : SchoolbookProduct) :
    product.value / Challenge.EvmProof.Limbs.radix =
      product.r1.toNat + Challenge.EvmProof.Limbs.radix * product.r2.toNat := by
  have hr0 := product.r0.val.isLt
  change product.r0.toNat < Challenge.EvmProof.Limbs.radix at hr0
  unfold SchoolbookProduct.value
  rw [show product.r0.toNat + Challenge.EvmProof.Limbs.radix *
      product.r1.toNat + Challenge.EvmProof.Limbs.radix ^ 2 *
        product.r2.toNat =
      product.r0.toNat + Challenge.EvmProof.Limbs.radix *
        (product.r1.toNat + Challenge.EvmProof.Limbs.radix *
          product.r2.toNat) by ring]
  rw [Nat.add_mul_div_left _ _ Challenge.EvmProof.Limbs.radix_pos,
    Nat.div_eq_of_lt hr0, Nat.zero_add]

/-- The low three words discarded by the Barrett quotient fit below the
three-word divisor. -/
theorem barrettLower_lt (product : SchoolbookProduct) :
    let partials := barrettPartials product
    let l1 := barrettL1 partials
    let l2 := barrettL2 partials
    partials.p00.lo.toNat + Challenge.EvmProof.Limbs.radix * l1.word.toNat +
        Challenge.EvmProof.Limbs.radix ^ 2 * l2.word.toNat <
      Challenge.EvmProof.Limbs.radix ^ 3 := by
  exact Challenge.EvmProof.Limbs.threeWords_lt _ _ _

/-- Regroup the reconstructed schedule around the three discarded words. -/
theorem barrettSchedule_regroup (product : SchoolbookProduct) :
    let partials := barrettPartials product
    let l1 := barrettL1 partials
    let l2 := barrettL2 partials
    let l3 := barrettL3 partials
    (product.r1.toNat + Challenge.EvmProof.Limbs.radix * product.r2.toNat) *
        barrettMu =
      (partials.p00.lo.toNat +
        Challenge.EvmProof.Limbs.radix * l1.word.toNat +
        Challenge.EvmProof.Limbs.radix ^ 2 * l2.word.toNat) +
      Challenge.EvmProof.Limbs.radix ^ 3 *
        (l3.word.toNat + Challenge.EvmProof.Limbs.radix *
          (partials.p12.hi.toNat + l3.carry.toNat)) := by
  dsimp only
  rw [barrettSchedule_value product]
  simp only [pow_succ]
  ring

/-- Dividing the schedule by three words leaves exactly its two quotient
words. -/
theorem barrettSchedule_div (product : SchoolbookProduct) :
    ((product.r1.toNat + Challenge.EvmProof.Limbs.radix * product.r2.toNat) *
        barrettMu) / Challenge.EvmProof.Limbs.radix ^ 3 =
      let partials := barrettPartials product
      let l3 := barrettL3 partials
      l3.word.toNat + Challenge.EvmProof.Limbs.radix *
        (partials.p12.hi.toNat + l3.carry.toNat) := by
  rw [barrettSchedule_regroup product]
  rw [Nat.add_mul_div_left _ _
    (pow_pos Challenge.EvmProof.Limbs.radix_pos 3)]
  rw [Nat.div_eq_of_lt (barrettLower_lt product), Nat.zero_add]

/-- The quotient structure reconstructs the same two schedule words. -/
theorem barrettQuotient_value_eq_schedule (product : SchoolbookProduct) :
    (barrettQuotient product).value =
      let partials := barrettPartials product
      let l3 := barrettL3 partials
      l3.word.toNat + Challenge.EvmProof.Limbs.radix *
        (partials.p12.hi.toNat + l3.carry.toNat) := by
  have hq1 := barrettQuotient_q1_value product
  change (barrettQuotient product).q1.toNat =
    (barrettPartials product).p12.hi.toNat +
      (barrettL3 (barrettPartials product)).carry.toNat at hq1
  unfold BarrettQuotient.value
  change (barrettL3 (barrettPartials product)).word.toNat +
      Challenge.EvmProof.Limbs.radix *
        (barrettQuotient product).q1.toNat = _
  rw [hq1]

/-- The source-level quotient words reconstruct the mathematical Barrett
quotient `((x / 2^256) * mu) / 2^768`. -/
theorem value_barrettQuotient (product : SchoolbookProduct) :
    (barrettQuotient product).value =
      ((product.r1.toNat + Challenge.EvmProof.Limbs.radix *
          product.r2.toNat) * barrettMu) /
        Challenge.EvmProof.Limbs.radix ^ 3 := by
  rw [barrettQuotient_value_eq_schedule, barrettSchedule_div]

/-- The fixed Barrett quotient is an underestimate, so subtracting its
multiple of the modulus from the full product is exact in `Nat`. -/
theorem barrettQuotient_mul_modulus_le (product : SchoolbookProduct) :
    (barrettQuotient product).value * EvmSemantics.Crypto.Bls12381.p ≤
      product.value := by
  let divisor := Challenge.EvmProof.Limbs.radix ^ 3
  let high := product.value / Challenge.EvmProof.Limbs.radix
  let quotient := (barrettQuotient product).value
  have hquotient : quotient = high * barrettMu / divisor := by
    dsimp only [quotient, high, divisor]
    rw [value_barrettQuotient, schoolbookHigh_eq_div]
  have hqmul : quotient * divisor ≤ high * barrettMu := by
    rw [hquotient]
    exact Nat.div_mul_le_self _ _
  have hmumul : barrettMu * EvmSemantics.Crypto.Bls12381.p ≤
      Challenge.EvmProof.Limbs.radix ^ 4 := by
    rw [barrettMu_eq_floor]
    exact Nat.div_mul_le_self (Challenge.EvmProof.Limbs.radix ^ 4)
      EvmSemantics.Crypto.Bls12381.p
  have hhigh : high * Challenge.EvmProof.Limbs.radix ≤ product.value := by
    dsimp only [high]
    exact Nat.div_mul_le_self _ _
  have hscaled : divisor *
      (quotient * EvmSemantics.Crypto.Bls12381.p) ≤
      divisor * product.value := by
    calc
      divisor * (quotient * EvmSemantics.Crypto.Bls12381.p) =
          (quotient * divisor) * EvmSemantics.Crypto.Bls12381.p := by ring
      _ ≤ (high * barrettMu) * EvmSemantics.Crypto.Bls12381.p :=
        Nat.mul_le_mul_right EvmSemantics.Crypto.Bls12381.p hqmul
      _ = high * (barrettMu * EvmSemantics.Crypto.Bls12381.p) := by ring
      _ ≤ high * Challenge.EvmProof.Limbs.radix ^ 4 :=
        Nat.mul_le_mul_left high hmumul
      _ = divisor * (high * Challenge.EvmProof.Limbs.radix) := by
        dsimp only [divisor]
        ring
      _ ≤ divisor * product.value := Nat.mul_le_mul_left divisor hhigh
  exact Nat.le_of_mul_le_mul_left hscaled
    (pow_pos Challenge.EvmProof.Limbs.radix_pos 3)

/-- Exact scaled error identity for the fixed Barrett underestimate.  The
three summands expose the error introduced by discarding the product's low
word, flooring `mu`, and discarding the quotient product's low three words. -/
theorem barrettScaledRemainder_eq (product : SchoolbookProduct) :
    (product.value -
        (barrettQuotient product).value *
          EvmSemantics.Crypto.Bls12381.p) *
        Challenge.EvmProof.Limbs.radix ^ 3 =
      (product.value % Challenge.EvmProof.Limbs.radix) *
          Challenge.EvmProof.Limbs.radix ^ 3 +
        (product.value / Challenge.EvmProof.Limbs.radix) *
          (Challenge.EvmProof.Limbs.radix ^ 4 %
            EvmSemantics.Crypto.Bls12381.p) +
        ((product.value / Challenge.EvmProof.Limbs.radix) * barrettMu %
            Challenge.EvmProof.Limbs.radix ^ 3) *
          EvmSemantics.Crypto.Bls12381.p := by
  let radix := Challenge.EvmProof.Limbs.radix
  let modulus := EvmSemantics.Crypto.Bls12381.p
  let divisor := radix ^ 3
  let x := product.value
  let high := x / radix
  let quotient := (barrettQuotient product).value
  let muRemainder := radix ^ 4 % modulus
  let quotientRemainder := high * barrettMu % divisor
  have hxsplit : x % radix + radix * high = x := by
    exact Nat.mod_add_div x radix
  have hmusplit : muRemainder + modulus * barrettMu = radix ^ 4 := by
    dsimp only [muRemainder, modulus, radix]
    rw [barrettMu_eq_floor]
    exact Nat.mod_add_div (Challenge.EvmProof.Limbs.radix ^ 4)
      EvmSemantics.Crypto.Bls12381.p
  have hquotient : quotient = high * barrettMu / divisor := by
    dsimp only [quotient, high, x, divisor, radix]
    rw [value_barrettQuotient, schoolbookHigh_eq_div]
  have hquotientSplit : quotientRemainder + divisor * quotient =
      high * barrettMu := by
    dsimp only [quotientRemainder]
    rw [hquotient]
    exact Nat.mod_add_div (high * barrettMu) divisor
  have hdecomp : x * divisor =
      quotient * modulus * divisor +
        (x % radix * divisor + high * muRemainder +
          quotientRemainder * modulus) := by
    calc
      x * divisor = (x % radix + radix * high) * divisor := by rw [hxsplit]
      _ = x % radix * divisor + high * radix ^ 4 := by
        dsimp only [divisor]
        ring
      _ = x % radix * divisor +
          high * (muRemainder + modulus * barrettMu) := by rw [hmusplit]
      _ = x % radix * divisor + high * muRemainder +
          (high * barrettMu) * modulus := by ring
      _ = x % radix * divisor + high * muRemainder +
          (quotientRemainder + divisor * quotient) * modulus := by
            rw [hquotientSplit]
      _ = quotient * modulus * divisor +
          (x % radix * divisor + high * muRemainder +
            quotientRemainder * modulus) := by ring
  change (x - quotient * modulus) * divisor =
    x % radix * divisor + high * muRemainder + quotientRemainder * modulus
  rw [Nat.sub_mul, hdecomp]
  omega

/-- For products below `p²`, the fixed Barrett underestimate leaves less than
`3p`; therefore the source needs at most two corrective subtractions. -/
theorem barrettRemainder_lt_three_mul_modulus (product : SchoolbookProduct)
    (hproduct : product.value < EvmSemantics.Crypto.Bls12381.p ^ 2) :
    product.value -
        (barrettQuotient product).value * EvmSemantics.Crypto.Bls12381.p <
      3 * EvmSemantics.Crypto.Bls12381.p := by
  let radix := Challenge.EvmProof.Limbs.radix
  let modulus := EvmSemantics.Crypto.Bls12381.p
  let divisor := radix ^ 3
  let x := product.value
  let high := x / radix
  let remainder := x - (barrettQuotient product).value * modulus
  let muRemainder := radix ^ 4 % modulus
  let quotientRemainder := high * barrettMu % divisor
  have hscaled := barrettScaledRemainder_eq product
  change remainder * divisor =
    x % radix * divisor + high * muRemainder +
      quotientRemainder * modulus at hscaled
  have hradixPos : 0 < radix := Challenge.EvmProof.Limbs.radix_pos
  have hdivisorPos : 0 < divisor := pow_pos hradixPos 3
  have hmodulusPos : 0 < modulus := by
    dsimp only [modulus]
    norm_num [EvmSemantics.Crypto.Bls12381.p,
      EvmSemantics.Crypto.Bls12381.absU]
  have hradixLtModulus : radix < modulus := by
    dsimp only [radix, modulus]
    norm_num [Challenge.EvmProof.Limbs.radix,
      EvmSemantics.Crypto.Bls12381.p,
      EvmSemantics.Crypto.Bls12381.absU]
  have hmodulusSqLtDivisor : modulus ^ 2 < divisor := by
    dsimp only [modulus, divisor, radix]
    norm_num [Challenge.EvmProof.Limbs.radix,
      EvmSemantics.Crypto.Bls12381.p,
      EvmSemantics.Crypto.Bls12381.absU]
  have hlow : x % radix < radix := Nat.mod_lt x hradixPos
  have hmuRemainder : muRemainder < modulus := by
    exact Nat.mod_lt (radix ^ 4) hmodulusPos
  have hquotientRemainder : quotientRemainder < divisor := by
    exact Nat.mod_lt (high * barrettMu) hdivisorPos
  have hhigh : high < modulus ^ 2 := by
    exact (Nat.div_le_self x radix).trans_lt hproduct
  have hlowTerm : x % radix * divisor < modulus * divisor :=
    Nat.mul_lt_mul_of_pos_right (hlow.trans hradixLtModulus) hdivisorPos
  have hhighTerm : high * muRemainder < modulus * divisor := by
    have hproductTerms := Nat.mul_lt_mul_of_lt_of_lt hhigh hmuRemainder
    exact hproductTerms.trans <| by
      have hscaledBound := Nat.mul_lt_mul_of_pos_right hmodulusSqLtDivisor
        hmodulusPos
      simpa [Nat.mul_comm] using hscaledBound
  have hquotientTerm : quotientRemainder * modulus < modulus * divisor := by
    simpa [Nat.mul_comm] using
      Nat.mul_lt_mul_of_pos_right hquotientRemainder hmodulusPos
  have hsum : x % radix * divisor + high * muRemainder +
      quotientRemainder * modulus < 3 * (modulus * divisor) := by
    omega
  have hscaledLt : remainder * divisor < (3 * modulus) * divisor := by
    rw [hscaled]
    calc
      x % radix * divisor + high * muRemainder +
          quotientRemainder * modulus < 3 * (modulus * divisor) := hsum
      _ = (3 * modulus) * divisor := by ring
  exact Nat.lt_of_mul_lt_mul_right hscaledLt

end Challenge.Bls12381.ProofSupport.Fp
