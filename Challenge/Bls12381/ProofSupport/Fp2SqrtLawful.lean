import Challenge.Bls12381.ProofSupport.Fp2SqrtLawfulOps

set_option warningAsError true

/-! # Lawful correctness of the Fp2 square-root algorithm -/

namespace Challenge.Bls12381.ProofSupport.Fp2

open PrimeField

private theorem lawful_two_ne_zero : (2 : LawfulFp2.Base) ≠ 0 := by
  intro h
  have hdiv : EvmSemantics.Crypto.Bls12381.p ∣ 2 :=
    (CharP.cast_eq_zero_iff LawfulFp2.Base
      EvmSemantics.Crypto.Bls12381.p 2).mp h
  norm_num [EvmSemantics.Crypto.Bls12381.p,
    EvmSemantics.Crypto.Bls12381.absU] at hdiv

theorem norm_isSquare_of_isSquare {a : LawfulFp2.Carrier}
    (ha : IsSquare a) : IsSquare (QuadraticAlgebra.norm a) := by
  rcases ha with ⟨z, rfl⟩
  refine ⟨QuadraticAlgebra.norm z, ?_⟩
  rw [map_mul]

theorem alpha_or_beta_isSquare {a : LawfulFp2.Carrier}
    (ha : IsSquare a) {t : LawfulFp2.Base}
    (ht : t ^ 2 = QuadraticAlgebra.norm a) :
    IsSquare ((a.re + t) * lawfulInvTwo) ∨
      IsSquare ((a.re - t) * lawfulInvTwo) := by
  rcases ha with ⟨z, rfl⟩
  rw [map_mul] at ht
  have htCases : t = QuadraticAlgebra.norm z ∨
      t = -QuadraticAlgebra.norm z := by
    apply (sq_eq_sq_iff_eq_or_eq_neg).mp
    simpa only [pow_two] using ht
  have htwo := lawful_two_ne_zero
  rcases htCases with htValue | htValue
  · left
    refine ⟨z.re, ?_⟩
    rw [htValue, lawfulInvTwo_eq]
    simp [QuadraticAlgebra.re_mul, QuadraticAlgebra.norm_def]
    field_simp [htwo]
    ring
  · right
    refine ⟨z.re, ?_⟩
    rw [htValue, lawfulInvTwo_eq]
    simp [QuadraticAlgebra.re_mul, QuadraticAlgebra.norm_def]
    field_simp [htwo]
    ring

private theorem double_ne_zero {x : LawfulFp2.Base} (hx : x ≠ 0) : x + x ≠ 0 := by
  rw [← two_mul]
  exact mul_ne_zero lawful_two_ne_zero hx

private theorem quotient_square_plus (a₀ a₁ t x₀ : LawfulFp2.Base)
    (ht : t ^ 2 = a₀ ^ 2 + a₁ ^ 2)
    (hx₀ : x₀ ^ 2 = (a₀ + t) * lawfulInvTwo) (hx₀ne : x₀ ≠ 0) :
    (a₁ * (x₀ + x₀)⁻¹) ^ 2 = (t - a₀) * lawfulInvTwo := by
  have hd := double_ne_zero hx₀ne
  apply mul_left_cancel₀ (pow_ne_zero 2 hd)
  calc
    (x₀ + x₀) ^ 2 * (a₁ * (x₀ + x₀)⁻¹) ^ 2 =
        a₁ ^ 2 * ((x₀ + x₀) * (x₀ + x₀)⁻¹) ^ 2 := by ring
    _ = a₁ ^ 2 := by rw [mul_inv_cancel₀ hd]; ring
    _ = (x₀ + x₀) ^ 2 * ((t - a₀) * lawfulInvTwo) := by
      rw [lawfulInvTwo_eq] at hx₀ ⊢
      field_simp [lawful_two_ne_zero] at hx₀ ⊢
      linear_combination -2 * ht + 2 * (a₀ - t) * hx₀

private theorem quotient_square_minus (a₀ a₁ t x₀ : LawfulFp2.Base)
    (ht : t ^ 2 = a₀ ^ 2 + a₁ ^ 2)
    (hx₀ : x₀ ^ 2 = (a₀ - t) * lawfulInvTwo) (hx₀ne : x₀ ≠ 0) :
    (a₁ * (x₀ + x₀)⁻¹) ^ 2 = -(t + a₀) * lawfulInvTwo := by
  have hd := double_ne_zero hx₀ne
  apply mul_left_cancel₀ (pow_ne_zero 2 hd)
  calc
    (x₀ + x₀) ^ 2 * (a₁ * (x₀ + x₀)⁻¹) ^ 2 =
        a₁ ^ 2 * ((x₀ + x₀) * (x₀ + x₀)⁻¹) ^ 2 := by ring
    _ = a₁ ^ 2 := by rw [mul_inv_cancel₀ hd]; ring
    _ = (x₀ + x₀) ^ 2 * (-(t + a₀) * lawfulInvTwo) := by
      rw [lawfulInvTwo_eq] at hx₀ ⊢
      field_simp [lawful_two_ne_zero] at hx₀ ⊢
      linear_combination -2 * ht + 2 * (t + a₀) * hx₀

theorem candidate_nonzero_plus (a₀ a₁ t x₀ : LawfulFp2.Base)
    (ht : t ^ 2 = a₀ ^ 2 + a₁ ^ 2)
    (hx₀ : x₀ ^ 2 = (a₀ + t) * lawfulInvTwo) (hx₀ne : x₀ ≠ 0) :
    let x₁ := a₁ * (x₀ + x₀)⁻¹
    (⟨x₀, x₁⟩ : LawfulFp2.Carrier) * ⟨x₀, x₁⟩ = ⟨a₀, a₁⟩ := by
  dsimp only
  apply QuadraticAlgebra.ext
  · simp only [QuadraticAlgebra.re_mul, neg_mul, one_mul]
    simp only [← pow_two]
    rw [quotient_square_plus a₀ a₁ t x₀ ht hx₀ hx₀ne, hx₀,
      lawfulInvTwo_eq]
    field_simp [lawful_two_ne_zero]
    ring
  · simp only [QuadraticAlgebra.im_mul, zero_mul, add_zero]
    rw [show x₀ * (a₁ * (x₀ + x₀)⁻¹) +
        a₁ * (x₀ + x₀)⁻¹ * x₀ =
      a₁ * ((x₀ + x₀) * (x₀ + x₀)⁻¹) by ring]
    rw [mul_inv_cancel₀ (double_ne_zero hx₀ne), mul_one]

theorem candidate_nonzero_minus (a₀ a₁ t x₀ : LawfulFp2.Base)
    (ht : t ^ 2 = a₀ ^ 2 + a₁ ^ 2)
    (hx₀ : x₀ ^ 2 = (a₀ - t) * lawfulInvTwo) (hx₀ne : x₀ ≠ 0) :
    let x₁ := a₁ * (x₀ + x₀)⁻¹
    (⟨x₀, x₁⟩ : LawfulFp2.Carrier) * ⟨x₀, x₁⟩ = ⟨a₀, a₁⟩ := by
  dsimp only
  apply QuadraticAlgebra.ext
  · simp only [QuadraticAlgebra.re_mul, neg_mul, one_mul]
    simp only [← pow_two]
    rw [quotient_square_minus a₀ a₁ t x₀ ht hx₀ hx₀ne, hx₀,
      lawfulInvTwo_eq]
    field_simp [lawful_two_ne_zero]
    ring
  · simp only [QuadraticAlgebra.im_mul, zero_mul, add_zero]
    rw [show x₀ * (a₁ * (x₀ + x₀)⁻¹) +
        a₁ * (x₀ + x₀)⁻¹ * x₀ =
      a₁ * ((x₀ + x₀) * (x₀ + x₀)⁻¹) by ring]
    rw [mul_inv_cancel₀ (double_ne_zero hx₀ne), mul_one]

theorem candidate_zero_plus (a₀ a₁ t : LawfulFp2.Base)
    (ht : t ^ 2 = a₀ ^ 2 + a₁ ^ 2) (htSquare : IsSquare t)
    (halpha : (a₀ + t) * lawfulInvTwo = 0) :
    let x₁ := lawfulSqrt (-a₀)
    (⟨0, x₁⟩ : LawfulFp2.Carrier) * ⟨0, x₁⟩ = ⟨a₀, a₁⟩ := by
  have hinvTwo : lawfulInvTwo ≠ 0 := by
    rw [lawfulInvTwo_eq]
    exact inv_ne_zero lawful_two_ne_zero
  have hat : a₀ + t = 0 := (mul_eq_zero.mp halpha).resolve_right hinvTwo
  have htValue : t = -a₀ := by linear_combination hat
  have ha₁sq : a₁ ^ 2 = 0 := by
    rw [htValue] at ht
    linear_combination -ht
  have ha₁ : a₁ = 0 := (sq_eq_zero_iff).mp ha₁sq
  have hnegSquare : IsSquare (-a₀) := by simpa [htValue] using htSquare
  have hsqrt := lawfulSqrt_square hnegSquare
  dsimp only
  generalize hx₁ : lawfulSqrt (-a₀) = x₁ at hsqrt ⊢
  apply QuadraticAlgebra.ext
  · simp only [QuadraticAlgebra.re_mul, zero_mul, neg_mul, one_mul]
    simp only [zero_add, ← pow_two]
    rw [hsqrt]
    ring
  · simp only [QuadraticAlgebra.im_mul, zero_mul, add_zero]
    rw [ha₁]
    simp only [mul_zero, zero_add]

theorem beta_root_ne_zero (a₀ t : LawfulFp2.Base)
    (htSquare : IsSquare t)
    (halphaFail : lawfulSqrt ((a₀ + t) * lawfulInvTwo) ^ 2 ≠
      (a₀ + t) * lawfulInvTwo)
    (hbetaSquare : IsSquare ((a₀ - t) * lawfulInvTwo)) :
    lawfulSqrt ((a₀ - t) * lawfulInvTwo) ≠ 0 := by
  intro hroot
  have hbeta := lawfulSqrt_square hbetaSquare
  rw [hroot, zero_pow (by norm_num)] at hbeta
  have hinvTwo : lawfulInvTwo ≠ 0 := by
    rw [lawfulInvTwo_eq]
    exact inv_ne_zero lawful_two_ne_zero
  have hat : a₀ - t = 0 :=
    (mul_eq_zero.mp hbeta.symm).resolve_right hinvTwo
  have htValue : t = a₀ := (sub_eq_zero.mp hat).symm
  have halphaValue : (a₀ + t) * lawfulInvTwo = t := by
    rw [htValue, lawfulInvTwo_eq]
    calc
      (a₀ + a₀) * (2 : LawfulFp2.Base)⁻¹ =
          a₀ * (2 * (2 : LawfulFp2.Base)⁻¹) := by ring
      _ = a₀ := by rw [mul_inv_cancel₀ lawful_two_ne_zero, mul_one]
  apply halphaFail
  apply lawfulSqrt_square
  rwa [halphaValue]

theorem lawfulSqrtRun_complete {a : LawfulFp2.Carrier} (ha : IsSquare a) :
    (SqrtProgram.run lawfulSqrtOps a).exists_ = true := by
  unfold SqrtProgram.run
  simp only [lawfulSqrtOps]
  by_cases hzero : a = 0
  · simp [hzero]
  · rw [if_neg (by simpa using hzero)]
    have hnormSquare : IsSquare (a.re ^ 2 + a.im ^ 2) := by
      simpa only [QuadraticAlgebra.norm_def, zero_mul, add_zero, neg_mul,
        one_mul, sub_neg_eq_add, pow_two] using norm_isSquare_of_isSquare ha
    generalize htDef : lawfulSqrt (a.re ^ 2 + a.im ^ 2) = t at ⊢
    have ht : t ^ 2 = a.re ^ 2 + a.im ^ 2 := by
      rw [← htDef]
      exact lawfulSqrt_square hnormSquare
    have htSquare : IsSquare t := by
      rw [← htDef]
      exact lawfulSqrt_isSquare hnormSquare
    simp only [ht, decide_true, Bool.not_true, Bool.false_eq_true, if_false]
    let alpha := (a.re + t) * lawfulInvTwo
    generalize halphaRootDef : lawfulSqrt ((a.re + t) * lawfulInvTwo) =
      alphaRoot at ⊢
    by_cases halpha : IsSquare alpha
    · have halphaRoot : alphaRoot ^ 2 = alpha := by
        rw [← halphaRootDef]
        exact lawfulSqrt_square halpha
      simp only [alpha, halphaRoot, decide_true, Bool.not_true,
        Bool.false_eq_true, if_false]
      by_cases hx₀ : alphaRoot = 0
      · simp only [hx₀, decide_true, if_true]
        have halphaZero : alpha = 0 := by rw [← halphaRoot, hx₀]; norm_num
        have hcandidate := candidate_zero_plus a.re a.im t
          (by simpa [QuadraticAlgebra.norm_def] using ht)
          htSquare (by simpa [alpha] using halphaZero)
        simp only [hcandidate, decide_true, Bool.not_true,
          Bool.false_eq_true, if_false]
      · simp only [hx₀, decide_false]
        have hcandidate := candidate_nonzero_plus a.re a.im t alphaRoot
          (by simpa [QuadraticAlgebra.norm_def] using ht)
          (by simpa [alpha] using halphaRoot) hx₀
        simp only [hcandidate, decide_true, Bool.not_true,
          Bool.false_eq_true, if_false]
    · have halphaFail : alphaRoot ^ 2 ≠ alpha := by
        intro heq
        apply halpha
        exact ⟨alphaRoot, by simpa only [pow_two] using heq.symm⟩
      simp only [alpha, halphaFail, decide_false, Bool.not_false, if_true]
      let beta := (a.re - t) * lawfulInvTwo
      have hbetaSquare : IsSquare beta := by
        rcases alpha_or_beta_isSquare (a := a) ha (t := t)
          (by simpa only [QuadraticAlgebra.norm_def, zero_mul, add_zero,
            neg_mul, one_mul, sub_neg_eq_add, pow_two] using ht) with h | h
        · exact (halpha h).elim
        · simpa [beta] using h
      generalize hbetaRootDef : lawfulSqrt ((a.re - t) * lawfulInvTwo) =
        betaRoot at ⊢
      have hbetaRoot : betaRoot ^ 2 = beta := by
        rw [← hbetaRootDef]
        exact lawfulSqrt_square hbetaSquare
      have hbetaRootNe : betaRoot ≠ 0 := by
        rw [← hbetaRootDef]
        exact beta_root_ne_zero a.re t htSquare
          (by rw [halphaRootDef]; simpa [alpha] using halphaFail)
          (by simpa [beta] using hbetaSquare)
      simp only [hbetaRootNe, decide_false]
      have hcandidate := candidate_nonzero_minus a.re a.im t betaRoot
        (by simpa [QuadraticAlgebra.norm_def] using ht)
        (by simpa [beta] using hbetaRoot) hbetaRootNe
      simp only [hcandidate, decide_true, Bool.not_true,
        Bool.false_eq_true, if_false]

theorem lawfulSqrtRun_success {a : LawfulFp2.Carrier}
    (hsuccess : (SqrtProgram.run lawfulSqrtOps a).exists_ = true) :
    (SqrtProgram.run lawfulSqrtOps a).root *
        (SqrtProgram.run lawfulSqrtOps a).root = a := by
  exact SqrtProgram.run_success lawfulSqrtOps a
    (fun hzero => by
      have haZero : a = 0 := by
        simpa only [lawfulSqrtOps, decide_eq_true_eq] using hzero
      rw [haZero]
      rfl)
    (fun x y heq => by
      simpa only [lawfulSqrtOps, decide_eq_true_eq] using heq)
    hsuccess

theorem lawfulSqrtRun_exists_iff {a : LawfulFp2.Carrier} :
    (SqrtProgram.run lawfulSqrtOps a).exists_ = true ↔ IsSquare a := by
  constructor
  · intro hsuccess
    exact ⟨(SqrtProgram.run lawfulSqrtOps a).root,
      (lawfulSqrtRun_success hsuccess).symm⟩
  · exact lawfulSqrtRun_complete

end Challenge.Bls12381.ProofSupport.Fp2
