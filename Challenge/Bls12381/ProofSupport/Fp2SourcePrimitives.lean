import Challenge.Bls12381.ProofSupport.Fp2SourceDefs

set_option warningAsError true

/-! # Opaque source-operation boundary for the parametric Fp2 program -/

namespace Challenge.Bls12381.ProofSupport.Fp2

def sourceAdd (a b : Fp.Limbs) : Fp.Limbs := Fp.addSource a b
def sourceSub (a b : Fp.Limbs) : Fp.Limbs := Fp.subSource a b
def sourceMul (a b : Fp.Limbs) : Fp.Limbs := Fp.mulCanonical a b
def sourceSquare (a : Fp.Limbs) : Fp.Limbs := Fp.squareCanonical a
def sourceInv (a : Fp.Limbs) : Fp.Limbs := Fp.invCanonical a
def sourceNeg (a : Fp.Limbs) : Fp.Limbs := Fp.negSource a

theorem sourceAdd_eq (a b : Fp.Limbs) :
    sourceAdd a b = Fp.addSource a b := rfl

theorem sourceSub_eq (a b : Fp.Limbs) :
    sourceSub a b = Fp.subSource a b := rfl

theorem sourceMul_eq (a b : Fp.Limbs) :
    sourceMul a b = Fp.mulCanonical a b := rfl

theorem sourceSquare_eq (a : Fp.Limbs) :
    sourceSquare a = Fp.squareCanonical a := rfl

theorem sourceInv_eq (a : Fp.Limbs) :
    sourceInv a = Fp.invCanonical a := rfl

theorem sourceNeg_eq (a : Fp.Limbs) :
    sourceNeg a = Fp.negSource a := rfl

theorem canonical_sourceAdd {a b : Fp.Limbs} (ha : Fp.Canonical a)
    (hb : Fp.Canonical b) : Fp.Canonical (sourceAdd a b) := by
  rw [sourceAdd_eq]
  exact Fp.canonical_addSource ha hb

theorem canonical_sourceSub {a b : Fp.Limbs} (ha : Fp.Canonical a)
    (hb : Fp.Canonical b) : Fp.Canonical (sourceSub a b) := by
  rw [sourceSub_eq]
  exact Fp.canonical_subSource ha hb

theorem canonical_sourceMul {a b : Fp.Limbs} (ha : Fp.Canonical a)
    (hb : Fp.Canonical b) : Fp.Canonical (sourceMul a b) := by
  rw [sourceMul_eq]
  exact Fp.canonical_mulCanonical ha hb

theorem canonical_sourceSquare {a : Fp.Limbs} (ha : Fp.Canonical a) :
    Fp.Canonical (sourceSquare a) := by
  rw [sourceSquare_eq]
  exact Fp.canonical_squareCanonical ha

theorem canonical_sourceInv {a : Fp.Limbs} (ha : Fp.Canonical a) :
    Fp.Canonical (sourceInv a) := by
  rw [sourceInv_eq]
  exact Fp.canonical_invCanonical ha

theorem canonical_sourceNeg {a : Fp.Limbs} (ha : Fp.Canonical a) :
    Fp.Canonical (sourceNeg a) := by
  rw [sourceNeg_eq]
  exact Fp.canonical_negSource ha

end Challenge.Bls12381.ProofSupport.Fp2
