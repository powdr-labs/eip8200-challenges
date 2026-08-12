import YulSemantics.BigStep

set_option warningAsError true

/-! Small list-algebra lemmas for keeping restored Yul environments opaque. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics

theorem venv_set_append_of_names_ne {D : Dialect}
    (locals outer : VEnv D) (target : String) (value : D.Value)
    (hne : ∀ binding ∈ locals, binding.1 ≠ target) :
    VEnv.set (locals ++ outer) target value =
      locals ++ VEnv.set outer target value := by
  induction locals with
  | nil => rfl
  | cons head tail ih =>
      rcases head with ⟨name, oldValue⟩
      have hhead : name ≠ target := hne (name, oldValue) (by simp)
      have htail : ∀ binding ∈ tail, binding.1 ≠ target := by
        intro binding hmem
        exact hne binding (by simp [hmem])
      simp only [List.cons_append, VEnv.set, if_neg hhead]
      exact congrArg (fun rest => (name, oldValue) :: rest) (ih htail)

theorem venv_set_length {D : Dialect} (V : VEnv D)
    (target : String) (value : D.Value) :
    (VEnv.set V target value).length = V.length := by
  induction V with
  | nil => rfl
  | cons head tail ih =>
      rw [VEnv.set]
      split <;> simp [ih]

theorem venv_get_cons_ne {D : Dialect}
    (V : VEnv D) (name target : String) (value : D.Value)
    (hne : name ≠ target) :
    VEnv.get ((name, value) :: V) target = VEnv.get V target := by
  simp [VEnv.get, hne]

theorem venv_get_append_of_names_ne {D : Dialect}
    (locals outer : VEnv D) (target : String)
    (hne : ∀ binding ∈ locals, binding.1 ≠ target) :
    VEnv.get (locals ++ outer) target = VEnv.get outer target := by
  induction locals with
  | nil => rfl
  | cons head tail ih =>
      rcases head with ⟨name, value⟩
      have hhead : name ≠ target := hne (name, value) (by simp)
      have htail : ∀ binding ∈ tail, binding.1 ≠ target := by
        intro binding hmem
        exact hne binding (by simp [hmem])
      rw [List.cons_append, venv_get_cons_ne _ _ _ _ hhead, ih htail]

theorem venv_get_set_self_of_some {D : Dialect}
    (V : VEnv D) (target : String) (oldValue value : D.Value)
    (hget : VEnv.get V target = some oldValue) :
    VEnv.get (VEnv.set V target value) target = some value := by
  induction V with
  | nil => simp [VEnv.get] at hget
  | cons head tail ih =>
      rcases head with ⟨name, headValue⟩
      by_cases hname : name = target
      · subst name
        simp [VEnv.set, VEnv.get]
      · have htail : VEnv.get tail target = some oldValue := by
          rw [← venv_get_cons_ne tail name target headValue hname]
          exact hget
        rw [VEnv.set, if_neg hname,
          venv_get_cons_ne (VEnv.set tail target value) name target
            headValue hname]
        exact ih htail

theorem venv_get_set_ne {D : Dialect}
    (V : VEnv D) (setTarget getTarget : String) (value : D.Value)
    (hne : setTarget ≠ getTarget) :
    VEnv.get (VEnv.set V setTarget value) getTarget =
      VEnv.get V getTarget := by
  induction V with
  | nil => rfl
  | cons head tail ih =>
      rcases head with ⟨name, headValue⟩
      by_cases hset : name = setTarget
      · subst name
        simp [VEnv.set, VEnv.get, hne]
      · by_cases hget : name = getTarget
        · subst name
          simp [VEnv.set, VEnv.get, hset]
        · rw [VEnv.set, if_neg hset,
            venv_get_cons_ne _ _ _ _ hget,
            venv_get_cons_ne _ _ _ _ hget]
          exact ih

theorem restore_append_of_length_eq {D : Dialect}
    (outer locals inner : VEnv D) (hlen : inner.length = outer.length) :
    restore outer (locals ++ inner) = inner := by
  simp [restore, List.length_append, hlen]

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
