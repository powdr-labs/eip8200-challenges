import Challenge.Bls12381.ProofSupport.FpBarrettSchedule

set_option warningAsError true

namespace Checks.Bls12381FpBarrettSchedule

open Challenge.Bls12381.ProofSupport
open EvmSemantics

example (sum : Challenge.EvmProof.Limbs.WordSum) (term : UInt256) :
    (Fp.barrettAddTerm sum term).carry =
      sum.carry + UInt256.lt (sum.word + term) term := rfl

example (sum : Challenge.EvmProof.Limbs.WordSum) (term : UInt256)
    (hcarry : sum.carry.toNat + 1 < Challenge.EvmProof.Limbs.radix) :
    (Fp.barrettAddTerm sum term).value = sum.value + term.toNat :=
  Fp.barrettAddTerm_value sum term hcarry

example (partials : Fp.BarrettPartials) :
    Fp.barrettL1 partials =
      Fp.barrettAddTerm
        (Challenge.EvmProof.Limbs.addTwo256 partials.p00.hi partials.p01.lo)
        partials.p10.lo := rfl

example (partials : Fp.BarrettPartials) :
    Fp.barrettL2 partials =
      Fp.barrettAddTerm
        (Fp.barrettAddTerm
          (Fp.barrettAddTerm
            (Challenge.EvmProof.Limbs.addTwo256 partials.p01.hi partials.p10.hi)
            partials.p02.lo)
          partials.p11.lo)
        (Fp.barrettL1 partials).carry := rfl

example (partials : Fp.BarrettPartials) :
    Fp.barrettL3 partials =
      Fp.barrettAddTerm
        (Fp.barrettAddTerm
          (Challenge.EvmProof.Limbs.addTwo256 partials.p02.hi partials.p11.hi)
          partials.p12.lo)
        (Fp.barrettL2 partials).carry := rfl

example (product : Fp.SchoolbookProduct) :
    Fp.barrettQuotientTop product < Challenge.EvmProof.Limbs.radix :=
  Fp.barrettQuotientTop_lt product

example (product : Fp.SchoolbookProduct) :
    (Fp.barrettQuotient product).q1.toNat =
      Fp.barrettQuotientTop product :=
  Fp.barrettQuotient_q1_value product

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.barrettSchedule_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp.barrettSchedule_value

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.barrettQuotientTop_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp.barrettQuotientTop_lt

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.barrettQuotient_q1_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fp.barrettQuotient_q1_value

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.barrettAddTerm_value' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Fp.barrettAddTerm_value

/-- info: 'Challenge.Bls12381.ProofSupport.Fp.barrettAddTerm_carry_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Fp.barrettAddTerm_carry_le

end Checks.Bls12381FpBarrettSchedule
