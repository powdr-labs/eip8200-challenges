import Challenge.Bls12381.ProofSupport.Fp2SqrtDefs
import Challenge.Bls12381.ProofSupport.Fp2SqrtLawful
import Challenge.Bls12381.ProofSupport.Fp2SqrtRefinement
import Challenge.Bls12381.ProofSupport.Fp2SourceLawful

set_option warningAsError true

/-! # Source-faithful BLS12-381 Fp2 square roots -/

namespace Challenge.Bls12381.ProofSupport.Fp2

private theorem canonical_zero : Canonical zero := by
  constructor <;> exact ⟨Fp.canonical_normalize 0⟩

theorem canonical_sqrtSource {a : Repr} (ha : Canonical a) :
    Canonical (sqrtSource a).root := by
  exact SqrtProgram.run_good sqrtSourceOps Fp.Canonical Canonical
    canonical_zero
    (fun _ _ hx hy => canonical_mkRepr ⟨hx⟩ ⟨hy⟩)
    (fun _ _ => Fp.canonical_addSource)
    (fun _ _ => Fp.canonical_subSource)
    (fun _ => Fp.canonical_negSource)
    (fun _ _ => Fp.canonical_mulCanonical)
    (fun _ => Fp.canonical_squareCanonical)
    (fun _ => Fp.canonical_sqrtCanonical)
    (fun _ => Fp.canonical_invCanonical)
    canonical_invTwo a ⟨ha.c0.proof, ha.c1.proof⟩

theorem sqrSource_zero : sqrSource zero = zero := by
  apply eq_of_lawful_eq (canonical_sqrSource canonical_zero) canonical_zero
  rw [toLawful_sqrSource canonical_zero, toLawful_zero_repr]
  norm_num

theorem sqrtSource_success {a : Repr} (_ha : Canonical a)
    (hsuccess : (sqrtSource a).exists_ = true) :
    sqrSource (sqrtSource a).root = a := by
  exact SqrtProgram.run_success sqrtSourceOps a
    (fun hzero => by
      rw [eq_zero_of_isZeroSource_true hzero]
      exact sqrSource_zero)
    (fun _ _ => eq_of_eqSource_true) hsuccess

theorem sqrtSource_exists_iff {a : Repr} (ha : Canonical a) :
    (sqrtSource a).exists_ = true ↔ IsSquare (toLawful a) := by
  rw [(sqrtSource_refines_lawful ha).1]
  exact lawfulSqrtRun_exists_iff

/-- Canonical decoded `(-1, 0)`, the pure-imaginary square-root regression. -/
def negativeOne : Repr :=
  mkRepr (Fp.negSource (Fp.normalize 1)) (Fp.normalize 0)

theorem canonical_negativeOne : Canonical negativeOne :=
  canonical_mkRepr
    ⟨Fp.canonical_negSource (Fp.canonical_normalize 1)⟩
    ⟨Fp.canonical_normalize 0⟩

theorem toLawful_negativeOne :
    toLawful negativeOne = (⟨-1, 0⟩ : LawfulFp2.Carrier) := by
  rw [negativeOne, toLawful_mkRepr]
  apply QuadraticAlgebra.ext
  · rw [Fp.toLawful_negSource (Fp.canonical_normalize 1)]
    change -(1 : LawfulFp2.Base) = -1
    rfl
  · simp

theorem sqrtSource_negativeOne_success :
    (sqrtSource negativeOne).exists_ = true := by
  apply (sqrtSource_exists_iff canonical_negativeOne).2
  rw [toLawful_negativeOne]
  refine ⟨(⟨0, 1⟩ : LawfulFp2.Carrier), ?_⟩
  apply QuadraticAlgebra.ext <;>
    simp

end Challenge.Bls12381.ProofSupport.Fp2
