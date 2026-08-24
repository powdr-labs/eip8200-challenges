import Challenge.Bls12381G1Add.Reference.Proofs.SourceFpInvResultDefs

set_option warningAsError true

/-! # Auditor-facing refinement of native frozen G1ADD `fpInv` -/

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM
open Challenge.Bls12381.ProofSupport

/-- The stable public output words are exactly the shared canonical inversion
model.  The execution bridge establishing that source calls return these words
passes through `YulModexp.Refines`. -/
theorem fpInvOutput_eq_invCanonical (hi lo : U256)
    (_hcanonical : Fp.Canonical (fpInvInputLimbs hi lo)) :
    fpInvOutputLimbs hi lo =
      Fp.invCanonical (fpInvInputLimbs hi lo) := by
  unfold fpInvOutputLimbs
  rfl

theorem canonical_fpInvOutput (hi lo : U256)
    (hcanonical : Fp.Canonical (fpInvInputLimbs hi lo)) :
    Fp.Canonical (fpInvOutputLimbs hi lo) := by
  rw [fpInvOutput_eq_invCanonical hi lo hcanonical]
  exact Fp.canonical_invCanonical hcanonical

/-- The stable native result represents lawful field inversion. -/
theorem fpInvOutput_toLawful (hi lo : U256)
    (hcanonical : Fp.Canonical (fpInvInputLimbs hi lo)) :
    PrimeField.finEquiv (Fp.toField (fpInvOutputLimbs hi lo)) =
      (PrimeField.finEquiv (Fp.toField (fpInvInputLimbs hi lo)))⁻¹ := by
  rw [fpInvOutput_eq_invCanonical hi lo hcanonical,
    Fp.finEquiv_toField, Fp.finEquiv_toField,
    Fp.lawful_invCanonical hcanonical]

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
