import Challenge.Bls12381G1Add.Reference.Proofs.SourceFpInvPowDefs

set_option warningAsError true
set_option linter.unusedSimpArgs false

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics

theorem vget_set_self {D : Dialect} (V : VEnv D) (x : Ident)
    (old value : D.Value) (hget : VEnv.get V x = some old) :
    VEnv.get (VEnv.set V x value) x = some value := by
  induction V with
  | nil => simp [VEnv.get] at hget
  | cons head tail ih =>
      rcases head with ⟨y, current⟩
      by_cases hxy : y = x
      · subst y
        simp [VEnv.set, VEnv.get]
      · simp only [VEnv.set, hxy, ↓reduceIte]
        rw [show VEnv.get ((y, current) :: VEnv.set tail x value) x =
          VEnv.get (VEnv.set tail x value) x by simp [VEnv.get, hxy]]
        apply ih
        simpa [VEnv.get, hxy] using hget

theorem vget_set_other {D : Dialect} (V : VEnv D) (x y : Ident)
    (value : D.Value) (hxy : x ≠ y) :
    VEnv.get (VEnv.set V x value) y = VEnv.get V y := by
  induction V with
  | nil => rfl
  | cons head tail ih =>
      rcases head with ⟨z, current⟩
      by_cases hzx : z = x
      · subst z
        simp [VEnv.set, VEnv.get, hxy]
      · by_cases hzy : z = y
        · subst z
          simp [VEnv.set, VEnv.get, hzx]
        · simp only [VEnv.set, hzx, ↓reduceIte]
          simpa [VEnv.get, hzy] using ih

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
