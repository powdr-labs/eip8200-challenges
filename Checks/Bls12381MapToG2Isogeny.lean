import Challenge.Bls12381.ProofSupport.MapToG2Isogeny

set_option warningAsError true

namespace Challenge.Bls12381.ProofSupport.MapToG2

example : kXNum.length = 4 := kXNum_length
example : kXDen.length = 3 := kXDen_length
example : kYNum.length = 4 := kYNum_length
example : kYDen.length = 4 := kYDen_length

example : kXNumSourceOrder = kXNum.reverse := rfl
example : kXDenSourceOrder = kXDen.reverse.tail := rfl
example : kYNumSourceOrder = kYNum.reverse := rfl
example : kYDenSourceOrder = kYDen.reverse.tail := rfl

example :
    EvmSemantics.Crypto.Bls12381MapFp2ToG2.kXDen.map
        (fun value => LawfulFp2.ofWire value) = kXDen ++ [0] :=
  kXDen_pinned_padding

example : kXDenSourceOrder.length = 2 := kXDenSourceOrder_length
example : kYDenSourceOrder.length = 3 := kYDenSourceOrder_length

example (numerator denominator y : Field)
    (hpole :
      let values := iso3Components numerator denominator
      values.xDen * denominator = 0 ∨ values.yDen = 0) :
    iso3 numerator denominator y = G2Affine.infinity :=
  iso3_eq_infinity_of_pole numerator denominator y hpole

/-- info: 'Challenge.Bls12381.ProofSupport.MapToG2.kXNum_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms kXNum_length

/-- info: 'Challenge.Bls12381.ProofSupport.MapToG2.kXDen_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms kXDen_length

/-- info: 'Challenge.Bls12381.ProofSupport.MapToG2.kYNum_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms kYNum_length

/-- info: 'Challenge.Bls12381.ProofSupport.MapToG2.kYDen_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms kYDen_length

/-- info: 'Challenge.Bls12381.ProofSupport.MapToG2.kXDen_pinned_padding' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms kXDen_pinned_padding

/-- info: 'Challenge.Bls12381.ProofSupport.MapToG2.kXDenSourceOrder_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms kXDenSourceOrder_length

/-- info: 'Challenge.Bls12381.ProofSupport.MapToG2.kYDenSourceOrder_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms kYDenSourceOrder_length

/-- info: 'Challenge.Bls12381.ProofSupport.MapToG2.iso3_eq_infinity_of_pole' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms iso3_eq_infinity_of_pole

end Challenge.Bls12381.ProofSupport.MapToG2
