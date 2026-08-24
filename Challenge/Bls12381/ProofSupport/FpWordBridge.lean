import Challenge.Bls12381.ProofSupport.FpConstants

set_option warningAsError true

/-! # BLS base-field / generic two-word bridge -/

namespace Challenge.Bls12381.ProofSupport.Fp

/-- View a BLS base-field limb pair as generic low/high EVM words. -/
def toWide (a : Limbs) : Challenge.EvmProof.Limbs.WideProduct :=
  { hi := a.hi, lo := a.lo }

/-- Reinterpret generic low/high EVM words as a BLS base-field limb pair. -/
def ofWide (words : Challenge.EvmProof.Limbs.WideProduct) : Limbs :=
  { hi := words.hi, lo := words.lo }

/-- The fixed BLS modulus as generic low/high EVM words. -/
def modulusWide : Challenge.EvmProof.Limbs.WideProduct :=
  { hi := modulusHi, lo := modulusLo }

@[simp] theorem toWide_value (a : Limbs) : (toWide a).value = value a := rfl

@[simp] theorem value_ofWide (words : Challenge.EvmProof.Limbs.WideProduct) :
    value (ofWide words) = words.value := rfl

@[simp] theorem modulusWide_value :
    modulusWide.value = EvmSemantics.Crypto.Bls12381.p := modulus_words

@[simp] theorem ofWide_toWide (a : Limbs) : ofWide (toWide a) = a := rfl

@[simp] theorem toWide_ofWide (words : Challenge.EvmProof.Limbs.WideProduct) :
    toWide (ofWide words) = words := by cases words; rfl

end Challenge.Bls12381.ProofSupport.Fp
