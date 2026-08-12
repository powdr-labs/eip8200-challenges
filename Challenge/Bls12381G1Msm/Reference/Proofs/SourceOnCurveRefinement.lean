import Challenge.Bls12381G1Msm.Reference.Proofs.SourceOnCurveCall
import Challenge.Bls12381G1Msm.Reference.Proofs.SourceFpMulRefinement
import Challenge.Bls12381G1Msm.Reference.Proofs.SourceFpAddRefinement
import Challenge.Bls12381G1Add.Reference.Proofs.SourceOnCurveLawful

set_option warningAsError true

/-! Arithmetic refinement of the frozen G1MSM `onCurve` result graph. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics.EVM

def onCurveX (xhi xlo : U256) :
    Challenge.Bls12381.ProofSupport.Fp.Limbs :=
  { hi := YulEvmCompiler.conv xhi, lo := YulEvmCompiler.conv xlo }

def onCurveY (yhi ylo : U256) :
    Challenge.Bls12381.ProofSupport.Fp.Limbs :=
  { hi := YulEvmCompiler.conv yhi, lo := YulEvmCompiler.conv ylo }

theorem onCurveResult_eq_shared (xhi xlo yhi ylo : U256) (yst : EvmState) :
    onCurveResult xhi xlo yhi ylo yst =
      Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.onCurveResult
        yst xhi xlo yhi ylo := by
  unfold onCurveResult onCurveLhs onCurveRhs onCurveCube
  unfold Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.onCurveResult
  unfold Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.onCurveLhsWords
  unfold Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.onCurveRhsWords
  unfold Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.onCurveRhsCubeWords
  unfold Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.onCurveX2Words
  unfold Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.onCurveState1
  unfold Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.onCurveState2
  rw [fpAddResult_eq_shared]
  rfl

/-- The exact G1MSM helper result is true precisely for points satisfying the
shared lawful G1 equation `y² = x³ + 4`.

Ideally, the lawful affine interface used here would be upstreamed to the
elliptic-curve library, so challenge proofs could state this directly against
the upstream affine type rather than through the repository's compatibility
layer. -/
theorem onCurveResult_eq_one_iff (xhi xlo yhi ylo : U256) (yst : EvmState)
    (hx : Challenge.Bls12381.ProofSupport.Fp.Canonical
      (onCurveX xhi xlo))
    (hy : Challenge.Bls12381.ProofSupport.Fp.Canonical
      (onCurveY yhi ylo)) :
    onCurveResult xhi xlo yhi ylo yst = 1 ↔
      Challenge.Bls12381.ProofSupport.G1Affine.OnCurve
        (.affine
          (Challenge.Bls12381.ProofSupport.Fp.value (onCurveX xhi xlo))
          (Challenge.Bls12381.ProofSupport.Fp.value (onCurveY yhi ylo))) := by
  rw [onCurveResult_eq_shared]
  exact
    Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.onCurveResult_eq_one_iff
      yst xhi xlo yhi ylo hx hy

theorem onCurveResult_eq_zero_iff (xhi xlo yhi ylo : U256) (yst : EvmState)
    (hx : Challenge.Bls12381.ProofSupport.Fp.Canonical
      (onCurveX xhi xlo))
    (hy : Challenge.Bls12381.ProofSupport.Fp.Canonical
      (onCurveY yhi ylo)) :
    onCurveResult xhi xlo yhi ylo yst = 0 ↔
      ¬Challenge.Bls12381.ProofSupport.G1Affine.OnCurve
        (.affine
          (Challenge.Bls12381.ProofSupport.Fp.value (onCurveX xhi xlo))
          (Challenge.Bls12381.ProofSupport.Fp.value (onCurveY yhi ylo))) := by
  rw [onCurveResult_eq_shared]
  exact
    Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.onCurveResult_eq_zero_iff
      yst xhi xlo yhi ylo hx hy

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
