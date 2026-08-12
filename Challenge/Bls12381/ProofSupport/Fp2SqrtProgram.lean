set_option warningAsError true

/-! # Parametric source program for Fp2 square roots -/

namespace Challenge.Bls12381.ProofSupport.Fp2.SqrtProgram

structure Result (Pair : Type) where
  exists_ : Bool
  root : Pair

structure Ops (Cell Pair : Type) where
  c0 : Pair → Cell
  c1 : Pair → Cell
  zero : Pair
  pair : Cell → Cell → Pair
  isZeroPair : Pair → Bool
  isZeroCell : Cell → Bool
  eqCell : Cell → Cell → Bool
  eqPair : Pair → Pair → Bool
  add : Cell → Cell → Cell
  sub : Cell → Cell → Cell
  neg : Cell → Cell
  mul : Cell → Cell → Cell
  square : Cell → Cell
  sqrt : Cell → Cell
  inv : Cell → Cell
  squarePair : Pair → Pair
  invTwo : Cell

/-- A pointwise refinement between two interpretations of the source program. -/
structure Refines {Cell₁ Pair₁ Cell₂ Pair₂ : Type}
    (src : Ops Cell₁ Pair₁) (dst : Ops Cell₂ Pair₂)
    (CellRel : Cell₁ → Cell₂ → Prop)
    (PairRel : Pair₁ → Pair₂ → Prop) : Prop where
  c0 : ∀ {a b}, PairRel a b → CellRel (src.c0 a) (dst.c0 b)
  c1 : ∀ {a b}, PairRel a b → CellRel (src.c1 a) (dst.c1 b)
  zero : PairRel src.zero dst.zero
  pair : ∀ {a₀ b₀ a₁ b₁}, CellRel a₀ b₀ → CellRel a₁ b₁ →
    PairRel (src.pair a₀ a₁) (dst.pair b₀ b₁)
  isZeroPair : ∀ {a b}, PairRel a b → src.isZeroPair a = dst.isZeroPair b
  isZeroCell : ∀ {a b}, CellRel a b → src.isZeroCell a = dst.isZeroCell b
  eqCell : ∀ {a₀ b₀ a₁ b₁}, CellRel a₀ b₀ → CellRel a₁ b₁ →
    src.eqCell a₀ a₁ = dst.eqCell b₀ b₁
  eqPair : ∀ {a₀ b₀ a₁ b₁}, PairRel a₀ b₀ → PairRel a₁ b₁ →
    src.eqPair a₀ a₁ = dst.eqPair b₀ b₁
  add : ∀ {a₀ b₀ a₁ b₁}, CellRel a₀ b₀ → CellRel a₁ b₁ →
    CellRel (src.add a₀ a₁) (dst.add b₀ b₁)
  sub : ∀ {a₀ b₀ a₁ b₁}, CellRel a₀ b₀ → CellRel a₁ b₁ →
    CellRel (src.sub a₀ a₁) (dst.sub b₀ b₁)
  neg : ∀ {a b}, CellRel a b → CellRel (src.neg a) (dst.neg b)
  mul : ∀ {a₀ b₀ a₁ b₁}, CellRel a₀ b₀ → CellRel a₁ b₁ →
    CellRel (src.mul a₀ a₁) (dst.mul b₀ b₁)
  square : ∀ {a b}, CellRel a b → CellRel (src.square a) (dst.square b)
  sqrt : ∀ {a b}, CellRel a b → CellRel (src.sqrt a) (dst.sqrt b)
  inv : ∀ {a b}, CellRel a b → CellRel (src.inv a) (dst.inv b)
  squarePair : ∀ {a b}, PairRel a b → PairRel (src.squarePair a) (dst.squarePair b)
  invTwo : CellRel src.invTwo dst.invTwo

/-- The one authoritative source program, including every branch and reuse. -/
def run {Cell Pair : Type} (ops : Ops Cell Pair) (a : Pair) : Result Pair :=
  if ops.isZeroPair a then { exists_ := true, root := ops.zero }
  else
    let norm := ops.add (ops.square (ops.c0 a)) (ops.square (ops.c1 a))
    let t := ops.sqrt norm
    if !(ops.eqCell (ops.square t) norm) then
      { exists_ := false, root := ops.zero }
    else
      let alpha := ops.mul (ops.add (ops.c0 a) t) ops.invTwo
      let alphaRoot := ops.sqrt alpha
      let x0 :=
        if !(ops.eqCell (ops.square alphaRoot) alpha) then
          let beta := ops.mul (ops.sub (ops.c0 a) t) ops.invTwo
          ops.sqrt beta
        else alphaRoot
      let x1 :=
        if ops.isZeroCell x0 then
          ops.sqrt (ops.neg (ops.c0 a))
        else
          ops.mul (ops.c1 a) (ops.inv (ops.add x0 x0))
      let root := ops.pair x0 x1
      if !(ops.eqPair (ops.squarePair root) a) then
        { exists_ := false, root := ops.zero }
      else { exists_ := true, root }

theorem run_refines {Cell₁ Pair₁ Cell₂ Pair₂ : Type}
    {src : Ops Cell₁ Pair₁} {dst : Ops Cell₂ Pair₂}
    {CellRel : Cell₁ → Cell₂ → Prop} {PairRel : Pair₁ → Pair₂ → Prop}
    (h : Refines src dst CellRel PairRel) {a : Pair₁} {b : Pair₂}
    (ha : PairRel a b) :
    (run src a).exists_ = (run dst b).exists_ ∧
      PairRel (run src a).root (run dst b).root := by
  unfold run
  rw [h.isZeroPair ha]
  split
  · exact ⟨rfl, h.zero⟩
  · dsimp only
    have hc0 := h.c0 ha
    have hc1 := h.c1 ha
    have hnorm := h.add (h.square hc0) (h.square hc1)
    have ht := h.sqrt hnorm
    rw [h.eqCell (h.square ht) hnorm]
    split
    · exact ⟨rfl, h.zero⟩
    · have halpha := h.mul (h.add hc0 ht) h.invTwo
      have halphaRoot := h.sqrt halpha
      rw [h.eqCell (h.square halphaRoot) halpha]
      split
      · have hbeta := h.mul (h.sub hc0 ht) h.invTwo
        have hx0 := h.sqrt hbeta
        rw [h.isZeroCell hx0]
        split
        · have hx1 := h.sqrt (h.neg hc0)
          have hroot := h.pair hx0 hx1
          rw [h.eqPair (h.squarePair hroot) ha]
          split
          · exact ⟨rfl, h.zero⟩
          · exact ⟨rfl, hroot⟩
        · have hx1 := h.mul hc1 (h.inv (h.add hx0 hx0))
          have hroot := h.pair hx0 hx1
          rw [h.eqPair (h.squarePair hroot) ha]
          split
          · exact ⟨rfl, h.zero⟩
          · exact ⟨rfl, hroot⟩
      · rw [h.isZeroCell halphaRoot]
        split
        · have hx1 := h.sqrt (h.neg hc0)
          have hroot := h.pair halphaRoot hx1
          rw [h.eqPair (h.squarePair hroot) ha]
          split
          · exact ⟨rfl, h.zero⟩
          · exact ⟨rfl, hroot⟩
        · have hx1 := h.mul hc1 (h.inv (h.add halphaRoot halphaRoot))
          have hroot := h.pair halphaRoot hx1
          rw [h.eqPair (h.squarePair hroot) ha]
          split
          · exact ⟨rfl, h.zero⟩
          · exact ⟨rfl, hroot⟩

theorem run_good {Cell Pair : Type} (ops : Ops Cell Pair)
    (GoodCell : Cell → Prop) (GoodPair : Pair → Prop)
    (hzero : GoodPair ops.zero)
    (hpair : ∀ x y, GoodCell x → GoodCell y → GoodPair (ops.pair x y))
    (hadd : ∀ x y, GoodCell x → GoodCell y → GoodCell (ops.add x y))
    (hsub : ∀ x y, GoodCell x → GoodCell y → GoodCell (ops.sub x y))
    (hneg : ∀ x, GoodCell x → GoodCell (ops.neg x))
    (hmul : ∀ x y, GoodCell x → GoodCell y → GoodCell (ops.mul x y))
    (hsquare : ∀ x, GoodCell x → GoodCell (ops.square x))
    (hsqrt : ∀ x, GoodCell x → GoodCell (ops.sqrt x))
    (hinv : ∀ x, GoodCell x → GoodCell (ops.inv x))
    (hinvTwo : GoodCell ops.invTwo) (a : Pair)
    (ha : GoodCell (ops.c0 a) ∧ GoodCell (ops.c1 a)) :
    GoodPair (run ops a).root := by
  unfold run
  split
  · exact hzero
  · have hnorm := hadd _ _ (hsquare _ ha.1) (hsquare _ ha.2)
    have ht := hsqrt _ hnorm
    dsimp only
    split
    · exact hzero
    · have halpha := hmul _ _ (hadd _ _ ha.1 ht) hinvTwo
      have halphaRoot := hsqrt _ halpha
      split
      · have hbeta := hmul _ _ (hsub _ _ ha.1 ht) hinvTwo
        have hx0 := hsqrt _ hbeta
        split
        · have hx1 := hsqrt _ (hneg _ ha.1)
          split
          · exact hzero
          · exact hpair _ _ hx0 hx1
        · have hx1 := hmul _ _ ha.2 (hinv _ (hadd _ _ hx0 hx0))
          split
          · exact hzero
          · exact hpair _ _ hx0 hx1
      · split
        · have hx1 := hsqrt _ (hneg _ ha.1)
          split
          · exact hzero
          · exact hpair _ _ halphaRoot hx1
        · have hx1 := hmul _ _ ha.2
            (hinv _ (hadd _ _ halphaRoot halphaRoot))
          split
          · exact hzero
          · exact hpair _ _ halphaRoot hx1

theorem run_success {Cell Pair : Type} (ops : Ops Cell Pair) (a : Pair)
    (hzero : ops.isZeroPair a = true → ops.squarePair ops.zero = a)
    (heq : ∀ x y, ops.eqPair x y = true → x = y)
    (hsuccess : (run ops a).exists_ = true) :
    ops.squarePair (run ops a).root = a := by
  generalize hrun : run ops a = result at hsuccess ⊢
  cases result with
  | mk found root =>
      dsimp only at hsuccess
      subst found
      have hfinish (candidate : Pair)
          (h : (if !(ops.eqPair (ops.squarePair candidate) a) then
              ({ exists_ := false, root := ops.zero } : Result Pair)
            else ({ exists_ := true, root := candidate } : Result Pair)) =
              ({ exists_ := true, root := root } : Result Pair)) :
          ops.squarePair root = a := by
        split at h
        · simp at h
        · have hroot := congrArg Result.root h.symm
          dsimp only at hroot
          rw [hroot]
          apply heq
          have hnot : (!(ops.eqPair (ops.squarePair candidate) a)) ≠ true := by
            assumption
          simpa using hnot
      unfold run at hrun
      split at hrun
      · have hroot : root = ops.zero := by simpa using congrArg Result.root hrun.symm
        rw [hroot]
        exact hzero (by assumption)
      · dsimp only at hrun
        split at hrun
        · simp at hrun
        · split at hrun <;> split at hrun <;> exact hfinish _ hrun

end Challenge.Bls12381.ProofSupport.Fp2.SqrtProgram
