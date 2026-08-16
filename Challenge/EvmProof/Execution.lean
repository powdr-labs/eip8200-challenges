import EvmSemantics.EVM.Equiv
import EvmSemantics.EVM.Contract
set_option warningAsError true
/-!
# Direct EVM execution proof combinators

These lemmas turn calculations with the executable `stepF` into derivations
of the relational `Step`, `Steps`, and `Eval` judgments used by challenge
statements. No compiler semantics appears here.

Straight-line bytecode blocks use `execN`/`steps_execN`. Loops use `Reaches`
and `Reaches.iterate`, with the loop invariant represented by the indexed
predicate `I`. SHA's padding, schedule, block, and round counters can each be
the index of one such invariant.
-/

namespace Challenge.EvmProof

open EvmSemantics
open EvmSemantics.EVM

/-- Execute exactly `n` applications of the deterministic EVM step function. -/
def execN : Nat → State → State
  | 0, s => s
  | n + 1, s => execN n (stepF s)

/-- Every intermediate state needed by `execN n s` has a successor. -/
def CanStepN : Nat → State → Prop
  | 0, _ => True
  | n + 1, s => ¬s.isDone ∧ CanStepN n (stepF s)

/-- A reducible `stepF` trace is a relational small-step trace. -/
theorem steps_execN {n : Nat} {s : State} (h : CanStepN n s) :
    Steps s (execN n s) := by
  induction n generalizing s with
  | zero => exact .refl _
  | succ n ih =>
      exact .trans (stepF_sound s h.1) (ih h.2)

/-- State-predicate reachability over zero or more relational EVM steps. -/
def Reaches (P Q : State → Prop) : Prop :=
  ∀ ⦃initial⦄, P initial →
    ∃ final, Steps initial final ∧ Q final

namespace Reaches

/-- View challenge reachability as the generic upstream relational contract. -/
theorem toContract {P Q : State → Prop} (h : Reaches P Q) :
    StepsContract P (fun _ final => Q final) := by
  intro initial hinitial
  exact h hinitial

/-- Specialize a generic relational contract whose postcondition ignores the
initial state to challenge reachability. -/
theorem ofContract {P Q : State → Prop}
    (h : StepsContract P (fun _ final => Q final)) : Reaches P Q := by
  intro initial hinitial
  exact h initial hinitial

theorem refl (P : State → Prop) : Reaches P P := by
  intro s hs
  exact ⟨s, .refl _, hs⟩

theorem trans {P Q R : State → Prop} (hpq : Reaches P Q) (hqr : Reaches Q R) :
    Reaches P R := by
  intro s hs
  obtain ⟨t, hst, ht⟩ := hpq hs
  obtain ⟨u, htu, hu⟩ := hqr ht
  exact ⟨u, hst.append htu, hu⟩

theorem consequence {P P' Q Q' : State → Prop}
    (hpre : ∀ s, P' s → P s) (h : Reaches P Q)
    (hpost : ∀ s, Q s → Q' s) : Reaches P' Q' := by
  intro s hs
  obtain ⟨t, hst, ht⟩ := h (hpre s hs)
  exact ⟨t, hst, hpost t ht⟩

/-- Discharge a straight-line block by reducing `execN`. -/
theorem of_execN {P Q : State → Prop} {n : Nat}
    (hcan : ∀ s, P s → CanStepN n s)
    (hpost : ∀ s, P s → Q (execN n s)) : Reaches P Q := by
  intro s hs
  exact ⟨execN n s, steps_execN (hcan s hs), hpost s hs⟩

/-- Compose `n` loop iterations. The invariant is indexed by the completed
iteration count, so bounds and intermediate SHA state remain explicit. -/
theorem iterate {I : Nat → State → Prop}
    (body : ∀ i, Reaches (I i) (I (i + 1))) :
    ∀ n, Reaches (I 0) (I n)
  | 0 => refl _
  | n + 1 => (iterate body n).trans (by simpa using body n)

/-- Compose exactly `count` iterations when the body lemma is available only
inside that bound. This is the usual shape for fixed 8-, 16-, or 64-round
loops. -/
theorem iterateBounded {I : Nat → State → Prop} (count : Nat)
    (body : ∀ i, i < count → Reaches (I i) (I (i + 1))) :
    Reaches (I 0) (I count) := by
  induction count with
  | zero => exact refl _
  | succ count ih =>
      have hprefix : Reaches (I 0) (I count) :=
        ih (fun i hi => body i (Nat.lt_succ_of_lt hi))
      exact hprefix.trans (body count (Nat.lt_succ_self _))

/-- Start the indexed loop invariant at an arbitrary counter. -/
theorem iterateFrom {I : Nat → State → Prop}
    (body : ∀ i, Reaches (I i) (I (i + 1))) :
    ∀ start count, Reaches (I start) (I (start + count))
  | _, 0 => by simpa using refl _
  | start, count + 1 => by
      have h₁ := iterateFrom body start count
      have h₂ := body (start + count)
      simpa [Nat.add_assoc] using h₁.trans h₂

end Reaches

/-- A relational trace ending in a done state yields its exact projected
big-step result. This is the final bridge used after composing blocks and
loops with `Reaches`. -/
theorem eval_of_steps {s t : State} (hsteps : Steps s t)
    (hdone : t.isDone = true) : Eval s t.toResult := by
  apply Eval.iff_steps_halted.mpr
  refine ⟨t, hsteps, ?_, ?_, rfl⟩
  · intro hrun
    simp [State.isDone, State.isHalted, State.isRunning, hrun] at hdone
  · have h := hdone
    simp only [State.isDone, Bool.and_eq_true, List.isEmpty_iff] at h
    exact h.2

/-- Close a reachability proof whose postcondition fixes a done result. -/
theorem Reaches.toEval {P : State → Prop} {result : ExecutionResult}
    (h : Reaches P (fun t => t.isDone = true ∧ t.toResult = result)) :
    ∀ ⦃s⦄, P s → Eval s result := by
  intro s hs
  exact StepsContract.toEval h.toContract s hs

/-- Reusable direct-bytecode obligation for an arbitrary input type and challenge:
from the gas-parameterized initial state, reach a done state with the expected
result at every sufficiently large gas budget. -/
def EventuallyEvaluates {Input : Type} (initial : Input → Nat → State)
    (expected : Input → ExecutionResult) : Prop :=
  ∀ input, ∃ g₀, ∀ g, g₀ ≤ g →
    Reaches (fun s => s = initial input g)
      (fun t => t.isDone = true ∧ t.toResult = expected input)

/-- Soundness of the generic direct-bytecode obligation. -/
theorem EventuallyEvaluates.sound {Input : Type} {initial : Input → Nat → State}
    {expected : Input → ExecutionResult}
    (h : EventuallyEvaluates initial expected) :
    ∀ input, ∃ g₀, ∀ g, g₀ ≤ g → Eval (initial input g) (expected input) := by
  intro input
  obtain ⟨g₀, hgas⟩ := h input
  refine ⟨g₀, fun g hg => ?_⟩
  exact (hgas g hg).toEval rfl

/-- A completed `execN` trace whose final state is done yields the exact
big-step result projected by the EVM semantics. -/
theorem eval_execN {n : Nat} {s : State}
    (hsteps : CanStepN n s) (hdone : (execN n s).isDone = true) :
    Eval s (execN n s).toResult :=
  eval_of_steps (steps_execN hsteps) hdone

end Challenge.EvmProof
