import Challenge.Bls12381.ProofSupport.LawfulFp12
import Challenge.Bls12381.ProofSupport.LawfulFp6Norm
import Challenge.Bls12381.ProofSupport.PrimeCertificate.RootEvidence.Order2

set_option warningAsError true

/-! Nondegeneracy of the lawful BLS12-381 quadratic-over-cubic norm. -/

namespace Challenge.Bls12381.ProofSupport.LawfulFp12

open EvmSemantics.Crypto.Bls12381
open EvmSemantics.EVM

theorem two_pow_half_ne_one :
    (2 : LawfulFp2.Base) ^ ((p - 1) / 2) ≠ 1 := by
  have horder : Precompile.modPow 2 ((p - 1) / 2) p ≠ 1 := by
    simpa only [PrimeCertificate.p_eq_certifiedModulus] using
      PrimeCertificate.rootOrder2
  intro hpow
  apply horder
  apply Nat.ModEq.eq_of_lt_of_lt
  · rw [← ZMod.natCast_eq_natCast_iff]
    rw [PrimeField.natCast_modPow_eq_pow 2 ((p - 1) / 2) p
      (by norm_num [p, absU])]
    simpa using hpow
  · exact Challenge.EvmProof.ModPow.eval_lt (by norm_num [p, absU])
  · norm_num [p, absU]

theorem two_not_square (b : LawfulFp2.Base) : b * b ≠ 2 := by
  intro hb
  have hb_ne : b ≠ 0 := by
    intro hzero
    rw [hzero] at hb
    have htwo : (2 : LawfulFp2.Base) ≠ 0 := by
      intro h
      have hdiv : p ∣ 2 :=
        (CharP.cast_eq_zero_iff LawfulFp2.Base p 2).mp h
      norm_num [p, absU] at hdiv
    norm_num at hb
    exact htwo hb.symm
  have hfermat : b ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one hb_ne
  apply two_pow_half_ne_one
  rw [← hb]
  rw [show b * b = b ^ 2 by ring, ← pow_mul]
  convert hfermat using 1
  norm_num [p, absU]

theorem xi_not_square (b : LawfulFp2.Carrier) : b * b ≠ LawfulFp6.xi := by
  intro hb
  apply two_not_square (QuadraticAlgebra.norm b)
  have hnorm := congrArg QuadraticAlgebra.norm hb
  have hxi : QuadraticAlgebra.norm LawfulFp6.xi = (2 : LawfulFp2.Base) := by
    simp [QuadraticAlgebra.norm_def, LawfulFp6.xi]
    norm_num
  rw [map_mul, hxi] at hnorm
  exact hnorm

/-- The cubic generator represented in the executable triple carrier. -/
def v : LawfulFp6.Carrier := LawfulFp6.mulByV LawfulFp6.one

@[simp] theorem fp6_norm_v : LawfulFp6.norm v = LawfulFp6.xi := by
  simp [v, LawfulFp6.norm, LawfulFp6.adjugate, LawfulFp6.mulByV,
    LawfulFp6.one]

theorem embed_v : LawfulFp6.embed v = AdjoinRoot.root LawfulFp6.cubic := by
  simp [v, LawfulFp6.embed, LawfulFp6.poly, LawfulFp6.mulByV,
    LawfulFp6.one, LawfulFp6.cubic]
  exact AdjoinRoot.mk_X

theorem cubic_root_not_square (y : AdjoinRoot LawfulFp6.cubic) :
    y * y ≠ AdjoinRoot.root LawfulFp6.cubic := by
  letI : Fact (Irreducible LawfulFp6.cubic) :=
    ⟨LawfulFp6.cubic_irreducible⟩
  intro hy
  apply xi_not_square (Algebra.norm LawfulFp2.Carrier y)
  have hnorm := congrArg (Algebra.norm LawfulFp2.Carrier) hy
  rw [map_mul] at hnorm
  rw [← embed_v, LawfulFp6.embed_norm, fp6_norm_v] at hnorm
  exact hnorm

theorem norm_ne_zero (a : Carrier) (ha : a ≠ zero) :
    norm a ≠ LawfulFp6.zero := by
  intro hnorm
  have hsquare : LawfulFp6.mul a.c0 a.c0 =
      LawfulFp6.mulByV (LawfulFp6.mul a.c1 a.c1) := by
    apply LawfulFp6.Carrier.ext
    · apply sub_eq_zero.mp
      simpa [norm, LawfulFp6.sub, LawfulFp6.zero] using
        congrArg LawfulFp6.Carrier.c0 hnorm
    · apply sub_eq_zero.mp
      simpa [norm, LawfulFp6.sub, LawfulFp6.zero] using
        congrArg LawfulFp6.Carrier.c1 hnorm
    · apply sub_eq_zero.mp
      simpa [norm, LawfulFp6.sub, LawfulFp6.zero] using
        congrArg LawfulFp6.Carrier.c2 hnorm
  by_cases hc1 : a.c1 = LawfulFp6.zero
  · have hc0 : a.c0 = LawfulFp6.zero := by
      have hz : LawfulFp6.mul a.c0 a.c0 = LawfulFp6.zero := by
        simpa [hc1, LawfulFp6.mulByV, LawfulFp6.mul, LawfulFp6.zero] using hsquare
      exact (LawfulFp6.mul_eq_zero a.c0 a.c0).mp hz |>.elim id id
    apply ha
    exact Carrier.ext hc0 hc1
  · letI : Fact (Irreducible LawfulFp6.cubic) :=
      ⟨LawfulFp6.cubic_irreducible⟩
    let x := LawfulFp6.embed a.c0
    let z := LawfulFp6.embed a.c1
    have hz : z ≠ 0 := LawfulFp6.embed_ne_zero hc1
    apply cubic_root_not_square (x * z⁻¹)
    have heq : x * x = AdjoinRoot.root LawfulFp6.cubic * (z * z) := by
      rw [← LawfulFp6.embed_mul, ← LawfulFp6.embed_mul, ← embed_v,
        ← LawfulFp6.embed_mul]
      simpa [x, z, v, LawfulFp6.mul, LawfulFp6.mulByV,
        LawfulFp6.one] using congrArg LawfulFp6.embed hsquare
    calc
      (x * z⁻¹) * (x * z⁻¹) = (x * x) * (z * z)⁻¹ := by ring
      _ = (AdjoinRoot.root LawfulFp6.cubic * (z * z)) * (z * z)⁻¹ := by
        rw [heq]
      _ = AdjoinRoot.root LawfulFp6.cubic := by
        rw [mul_assoc, mul_inv_cancel₀ (mul_ne_zero hz hz), mul_one]

theorem mul_inv_cancel (a : Carrier) (ha : a ≠ zero) :
    mul a (inv a) = one :=
  mul_inv_of_norm_ne_zero a
    (LawfulFp6.norm_ne_zero (norm a) (norm_ne_zero a ha))

theorem inv_mul_cancel (a : Carrier) (ha : a ≠ zero) :
    mul (inv a) a = one :=
  inv_mul_of_norm_ne_zero a
    (LawfulFp6.norm_ne_zero (norm a) (norm_ne_zero a ha))

end Challenge.Bls12381.ProofSupport.LawfulFp12
