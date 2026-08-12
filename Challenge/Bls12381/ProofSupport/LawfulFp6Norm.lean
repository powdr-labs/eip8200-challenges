import Challenge.Bls12381.ProofSupport.LawfulFp6
import Challenge.Bls12381.ProofSupport.PrimeCertificate.RootEvidence.Order3
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.RingTheory.Norm.Basic

/-! Nondegeneracy of the lawful BLS12-381 cubic-extension norm. -/

set_option warningAsError true

namespace Challenge.Bls12381.ProofSupport.LawfulFp6

open EvmSemantics.Crypto.Bls12381
open EvmSemantics.EVM


theorem two_pow_third_ne_one :
    (2 : LawfulFp2.Base) ^ ((p - 1) / 3) ≠ 1 := by
  have horder : Precompile.modPow 2 ((p - 1) / 3) p ≠ 1 := by
    simpa only [PrimeCertificate.p_eq_certifiedModulus] using
      PrimeCertificate.rootOrder3
  intro hpow
  apply horder
  apply Nat.ModEq.eq_of_lt_of_lt
  · rw [← ZMod.natCast_eq_natCast_iff]
    rw [PrimeField.natCast_modPow_eq_pow 2 ((p - 1) / 3) p
      (by norm_num [p, absU])]
    simpa using hpow
  · exact Challenge.EvmProof.ModPow.eval_lt (by norm_num [p, absU])
  · norm_num [p, absU]

theorem xi_not_cube (b : LawfulFp2.Carrier) : b ^ 3 ≠ xi := by
  intro hb
  have hnorm : QuadraticAlgebra.norm b ^ 3 = (2 : LawfulFp2.Base) := by
    rw [← map_pow, hb]
    simp [QuadraticAlgebra.norm_def, xi]
    norm_num
  have hnorm_ne : QuadraticAlgebra.norm b ≠ 0 := by
    intro hzero
    rw [hzero] at hnorm
    have htwo : (2 : LawfulFp2.Base) ≠ 0 := by
      intro h
      have hdiv : p ∣ 2 :=
        (CharP.cast_eq_zero_iff LawfulFp2.Base p 2).mp h
      norm_num [p, absU] at hdiv
    norm_num at hnorm
    exact htwo hnorm.symm
  have hfermat : QuadraticAlgebra.norm b ^ (p - 1) = 1 :=
    ZMod.pow_card_sub_one_eq_one hnorm_ne
  apply two_pow_third_ne_one
  rw [← hnorm]
  rw [← pow_mul]
  convert hfermat using 1
  norm_num [p, absU]

theorem cubic_irreducible :
    Irreducible (Polynomial.X ^ 3 - Polynomial.C xi) :=
  X_pow_sub_C_irreducible_of_prime Nat.prime_three xi_not_cube

noncomputable def cubic : Polynomial LawfulFp2.Carrier :=
  Polynomial.X ^ 3 - Polynomial.C xi

noncomputable def poly (a : Carrier) : Polynomial LawfulFp2.Carrier :=
  Polynomial.C a.c0 + Polynomial.C a.c1 * Polynomial.X +
    Polynomial.C a.c2 * Polynomial.X ^ 2

noncomputable def embed (a : Carrier) : AdjoinRoot cubic := AdjoinRoot.mk cubic (poly a)

theorem poly_ne_zero {a : Carrier} (ha : a ≠ zero) : poly a ≠ 0 := by
  intro hpoly
  apply ha
  apply Carrier.ext
  · apply_fun fun q => q.coeff 0 at hpoly
    simpa [poly, zero] using hpoly
  · apply_fun fun q => q.coeff 1 at hpoly
    simpa [poly, zero] using hpoly
  · apply_fun fun q => q.coeff 2 at hpoly
    simpa [poly, zero] using hpoly

theorem poly_natDegree_lt (a : Carrier) : (poly a).natDegree < 3 := by
  unfold poly
  calc
    _ ≤ max
        (Polynomial.C a.c0 + Polynomial.C a.c1 * Polynomial.X).natDegree
        (Polynomial.C a.c2 * Polynomial.X ^ 2).natDegree :=
      Polynomial.natDegree_add_le _ _
    _ ≤ 2 := by
      apply max_le
      · calc
          (Polynomial.C a.c0 + Polynomial.C a.c1 * Polynomial.X).natDegree ≤
              max (Polynomial.C a.c0).natDegree
                (Polynomial.C a.c1 * Polynomial.X).natDegree :=
            Polynomial.natDegree_add_le _ _
          _ ≤ 2 := by
            apply max_le
            · simp
            · calc
                (Polynomial.C a.c1 * Polynomial.X).natDegree ≤
                    (Polynomial.C a.c1).natDegree + Polynomial.X.natDegree :=
                  Polynomial.natDegree_mul_le
              _ ≤ 2 := by simp
      · calc
          (Polynomial.C a.c2 * Polynomial.X ^ 2).natDegree ≤
              (Polynomial.C a.c2).natDegree +
                (Polynomial.X ^ 2).natDegree :=
            Polynomial.natDegree_mul_le
          _ ≤ 2 := by
            calc
              (Polynomial.C a.c2).natDegree +
                    (Polynomial.X ^ 2).natDegree ≤ 0 + 2 :=
                Nat.add_le_add (by simp) (Polynomial.natDegree_X_pow_le 2)
              _ = 2 := rfl
    _ < 3 := by norm_num

theorem cubic_monic : cubic.Monic := by
  exact Polynomial.monic_X_pow_sub_C xi (by norm_num)

theorem embed_ne_zero {a : Carrier} (ha : a ≠ zero) : embed a ≠ 0 := by
  apply AdjoinRoot.mk_ne_zero_of_natDegree_lt cubic_monic (poly_ne_zero ha)
  simpa [cubic] using poly_natDegree_lt a

@[simp] theorem embed_zero : embed zero = 0 := by
  simp [embed, poly, zero]

theorem embed_mul (a b : Carrier) : embed (mul a b) = embed a * embed b := by
  simp only [embed, poly, mul, map_add, map_mul, map_pow, AdjoinRoot.mk_X,
    AdjoinRoot.mk_C]
  have hroot : AdjoinRoot.root cubic ^ 3 = AdjoinRoot.of cubic xi := by
    unfold cubic
    exact root_X_pow_sub_C_pow 3 xi
  have hroot4 : AdjoinRoot.root cubic ^ 4 =
      AdjoinRoot.of cubic xi * AdjoinRoot.root cubic := by
    calc
      _ = AdjoinRoot.root cubic ^ 3 * AdjoinRoot.root cubic := by ring
      _ = _ := by rw [hroot]
  ring_nf
  rw [hroot4, hroot]
  ring

theorem cubic_natDegree : cubic.natDegree = 3 := by simp [cubic]

noncomputable def cubicBasis :
    Module.Basis (Fin 3) LawfulFp2.Carrier (AdjoinRoot cubic) :=
  (AdjoinRoot.powerBasisAux' cubic_monic).reindex (finCongr cubic_natDegree)

theorem cubicBasis_repr_embed (a : Carrier) (i : Fin 3) :
    cubicBasis.repr (embed a) i = ![a.c0, a.c1, a.c2] i := by
  change (AdjoinRoot.powerBasisAux' cubic_monic).repr (embed a)
    ((finCongr cubic_natDegree).symm i) = _
  rw [AdjoinRoot.powerBasisAux'_repr_apply_to_fun]
  change ((AdjoinRoot.modByMonicHom cubic_monic)
    (AdjoinRoot.mk cubic (poly a))).coeff _ = _
  rw [AdjoinRoot.modByMonicHom_mk]
  rw [(Polynomial.modByMonic_eq_self_iff cubic_monic).mpr]
  · fin_cases i <;> simp [poly]
  · apply Polynomial.degree_lt_degree
    simpa [cubic] using poly_natDegree_lt a

def basisCarrier : Fin 3 → Carrier
  | 0 => { c0 := 1, c1 := 0, c2 := 0 }
  | 1 => { c0 := 0, c1 := 1, c2 := 0 }
  | 2 => { c0 := 0, c1 := 0, c2 := 1 }

theorem cubicBasis_apply (i : Fin 3) :
    cubicBasis i = embed (basisCarrier i) := by
  apply cubicBasis.repr.injective
  apply Finsupp.ext
  intro j
  rw [cubicBasis_repr_embed]
  fin_cases i <;> fin_cases j <;> simp [basisCarrier]

theorem embed_norm (a : Carrier) :
    Algebra.norm LawfulFp2.Carrier (embed a) = norm a := by
  rw [Algebra.norm_eq_matrix_det cubicBasis, Matrix.det_fin_three]
  have hmatrix : (Algebra.leftMulMatrix cubicBasis) (embed a) =
      !![a.c0, xi * a.c2, xi * a.c1;
         a.c1, a.c0, xi * a.c2;
         a.c2, a.c1, a.c0] := by
    apply Matrix.ext
    intro i j
    rw [Algebra.leftMulMatrix_eq_repr_mul, cubicBasis_apply, ← embed_mul,
      cubicBasis_repr_embed]
    fin_cases i <;> fin_cases j <;> simp [basisCarrier, mul]
  rw [hmatrix]
  simp [norm, adjugate]
  ring

theorem norm_ne_zero (a : Carrier) (ha : a ≠ zero) : norm a ≠ 0 := by
  letI : Fact (Irreducible cubic) := ⟨cubic_irreducible⟩
  have hnorm : Algebra.norm LawfulFp2.Carrier (embed a) ≠ 0 :=
    (Algebra.norm_ne_zero_iff_of_basis cubicBasis).mpr (embed_ne_zero ha)
  rwa [embed_norm] at hnorm

theorem mul_inv_cancel (a : Carrier) (ha : a ≠ zero) :
    mul a (inv a) = one :=
  mul_inv_of_norm_ne_zero a (norm_ne_zero a ha)

theorem inv_mul_cancel (a : Carrier) (ha : a ≠ zero) :
    mul (inv a) a = one :=
  inv_mul_of_norm_ne_zero a (norm_ne_zero a ha)

theorem mul_eq_zero (a b : Carrier) :
    mul a b = zero ↔ a = zero ∨ b = zero := by
  constructor
  · intro hmul
    by_cases ha : a = zero
    · exact Or.inl ha
    · right
      by_contra hb
      letI : Fact (Irreducible cubic) := ⟨cubic_irreducible⟩
      have hembed : embed a * embed b = 0 := by
        rw [← embed_mul, hmul, embed_zero]
      exact (mul_ne_zero (embed_ne_zero ha) (embed_ne_zero hb)) hembed
  · rintro (rfl | rfl) <;> simp [mul, zero]

end Challenge.Bls12381.ProofSupport.LawfulFp6
