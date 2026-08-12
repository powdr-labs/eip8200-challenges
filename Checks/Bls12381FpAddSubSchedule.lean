import Challenge.Bls12381.ProofSupport.FpAddSub

set_option warningAsError true

namespace Checks.Bls12381FpAddSubSchedule

open Challenge.Bls12381.ProofSupport
open EvmSemantics

example (a b : Fp.Limbs) :
    Fp.addRaw a b =
      let sLo := a.lo + b.lo
      let carry := UInt256.lt sLo a.lo
      { hi := a.hi + b.hi + carry, lo := sLo : Fp.Limbs } := rfl

example (sum : Fp.Limbs) :
    Fp.addNeedsCorrection sum =
      UInt256.lor (UInt256.gt sum.hi Fp.modulusHi)
        (UInt256.land (UInt256.eq sum.hi Fp.modulusHi)
          (UInt256.isZero (UInt256.lt sum.lo Fp.modulusLo))) := rfl

example (sum : Fp.Limbs) :
    Fp.addCorrect sum =
      let newLo := sum.lo - Fp.modulusLo
      { hi := sum.hi - (Fp.modulusHi + UInt256.gt Fp.modulusLo sum.lo)
        lo := newLo : Fp.Limbs } := rfl

example (a b : Fp.Limbs) :
    Fp.addSource a b =
      let sum := Fp.addRaw a b
      if (Fp.addNeedsCorrection sum).toNat ≠ 0 then Fp.addCorrect sum else sum := rfl

example (a b : Fp.Limbs) :
    Fp.subRaw a b =
      { hi := a.hi - b.hi - UInt256.gt b.lo a.lo
        lo := a.lo - b.lo : Fp.Limbs } := rfl

example (diff : Fp.Limbs) :
    Fp.subRepair diff =
      let newLo := diff.lo + Fp.modulusLo
      { hi := diff.hi + Fp.modulusHi + UInt256.lt newLo diff.lo
        lo := newLo : Fp.Limbs } := rfl

example (a b : Fp.Limbs) :
    Fp.subSource a b =
      let diff := Fp.subRaw a b
      if (UInt256.gt diff.hi Fp.modulusHi).toNat ≠ 0 then
        Fp.subRepair diff else diff := rfl

example (a : Fp.Limbs) :
    Fp.negNonzero a =
      { hi := Fp.modulusHi - a.hi - UInt256.gt a.lo Fp.modulusLo
        lo := Fp.modulusLo - a.lo : Fp.Limbs } := rfl

example (a : Fp.Limbs) : Fp.negSource a =
    if a.hi.toNat = 0 ∧ a.lo.toNat = 0 then Fp.pack 0
    else Fp.negNonzero a := rfl

end Checks.Bls12381FpAddSubSchedule
