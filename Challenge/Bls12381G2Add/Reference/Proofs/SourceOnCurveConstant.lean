import Challenge.Bls12381G2Add.Reference.Proofs.SourceFp2AddOutput
import Challenge.Bls12381G1Add.Reference.Proofs.SourceOnCurveRefinement
import Challenge.Bls12381.ProofSupport.G2Affine

set_option warningAsError true

/-! # Twist constant for frozen G2ADD `onCurve` -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open Challenge.Bls12381.ProofSupport

def onCurveTwistB : Fp2.Repr :=
  { c0 := Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.onCurveFour
    c1 := Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.onCurveFour }

theorem onCurveTwistB_canonical : Fp2.Canonical onCurveTwistB := by
  rw [Fp2.canonical_iff]
  exact ⟨Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.canonical_onCurveFour,
    Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.canonical_onCurveFour⟩

private theorem onCurveFour_toField :
    Fp.toField
      Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.onCurveFour =
      Fin.ofNat EvmSemantics.Crypto.Bls12381.p 4 := by
  rfl

theorem onCurveTwistB_toLawful :
    Fp2.toLawful onCurveTwistB = G2Affine.curve.b := by
  apply QuadraticAlgebra.ext
  · change PrimeField.finEquiv (Fp.toField
      Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.onCurveFour) =
      PrimeField.finEquiv (Fin.ofNat EvmSemantics.Crypto.Bls12381.p 4)
    rw [onCurveFour_toField]
  · change PrimeField.finEquiv (Fp.toField
      Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.onCurveFour) =
      PrimeField.finEquiv (Fin.ofNat EvmSemantics.Crypto.Bls12381.p 4)
    rw [onCurveFour_toField]

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
