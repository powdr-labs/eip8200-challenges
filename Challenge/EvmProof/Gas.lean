import Challenge.EvmProof.Execution
import Mathlib.Order.Monotone.Basic
set_option warningAsError true
/-!
# Gas-parametric direct EVM traces

Functional bytecode proofs should not carry a growing nest of subtractions
through every symbolic state.  `GasSteps s t` records a finite trace between
two gas-erased states together with its exact cost. It guarantees the
same trace from every larger budget and records only the remaining gas at the
end. Costs compose by addition, including through input-dependent loops.
Keeping the cost as data lets efficiency proofs reuse a functional trace
instead of replaying the bytecode proof in a second relation.
-/

namespace Challenge.EvmProof

open EvmSemantics
open EvmSemantics.EVM

/-- Replace only the available gas of an EVM state. -/
def withGas (s : State) (gas : Nat) : State := { s with gasAvailable := gas }

@[simp] theorem withGas_gasAvailable (s : State) (gas : Nat) :
    (withGas s gas).gasAvailable = gas := rfl

@[simp] theorem withGas_withGas (s : State) (g h : Nat) :
    withGas (withGas s g) h = withGas s h := by
  cases s
  rfl

/-- Halting is independent of the remaining gas counter. -/
@[simp] theorem withGas_isDone (s : State) (gas : Nat) :
    (withGas s gas).isDone = s.isDone := by
  cases s
  rfl

/-- The observable execution result is independent of remaining gas. -/
@[simp] theorem withGas_toResult (s : State) (gas : Nat) :
    (withGas s gas).toResult = s.toResult := by
  cases s
  rfl

/-- A gas-parametric relational execution contract.  The postcondition sees
only the gas-erased initial/final states and the exact cost; complete endpoint
states can remain existentially hidden at composition boundaries. -/
def GasContract (pre : State → Prop)
    (post : State → State → Nat → Prop) : Prop :=
  ∀ initial, pre initial →
    ∃ final cost,
      (∀ gas, cost ≤ gas →
        Steps (withGas initial gas) (withGas final (gas - cost))) ∧
      post initial final cost

namespace GasContract

/-- The zero-step gas contract. -/
theorem refl (pre : State → Prop) :
    GasContract pre (fun initial final cost =>
      final = initial ∧ cost = 0) := by
  intro initial hinitial
  exact ⟨initial, 0, fun gas _ => by simpa using Steps.refl (withGas initial gas),
    rfl, rfl⟩

/-- Strengthen a precondition and weaken a relational gas postcondition. -/
theorem consequence {pre pre' : State → Prop}
    {post post' : State → State → Nat → Prop}
    (hpre : ∀ state, pre' state → pre state)
    (contract : GasContract pre post)
    (hpost : ∀ initial final cost, pre' initial →
      post initial final cost → post' initial final cost) :
    GasContract pre' post' := by
  intro initial hinitial
  obtain ⟨final, cost, htrace, hfinal⟩ :=
    contract initial (hpre initial hinitial)
  exact ⟨final, cost, htrace,
    hpost initial final cost hinitial hfinal⟩

/-- Sequential composition with an explicit predicate connecting the first
postcondition to the second precondition. -/
theorem trans {pre nextPre : State → Prop}
    {middle next : State → State → Nat → Prop}
    (first : GasContract pre middle)
    (second : GasContract nextPre next)
    (seam : ∀ initial state cost, pre initial →
      middle initial state cost → nextPre state) :
    GasContract pre (fun initial final cost =>
      ∃ state firstCost secondCost,
        middle initial state firstCost ∧
        next state final secondCost ∧
        cost = firstCost + secondCost) := by
  intro initial hinitial
  obtain ⟨state, firstCost, hfirst, hmiddle⟩ := first initial hinitial
  obtain ⟨final, secondCost, hsecond, hnext⟩ :=
    second state (seam initial state firstCost hinitial hmiddle)
  refine ⟨final, firstCost + secondCost, ?_, state, firstCost,
    secondCost, hmiddle, hnext, rfl⟩
  intro gas hgas
  have hfirstGas : firstCost ≤ gas := by omega
  have hsecondGas : secondCost ≤ gas - firstCost := by omega
  have hsub : gas - firstCost - secondCost =
      gas - (firstCost + secondCost) := by omega
  simpa [hsub] using
    (hfirst gas hfirstGas).append
      (hsecond (gas - firstCost) hsecondGas)

/-- Compose two gas contracts and immediately map away the intermediate
state and component costs. -/
theorem transMapped {pre nextPre : State → Prop}
    {middle next post : State → State → Nat → Prop}
    (first : GasContract pre middle)
    (second : GasContract nextPre next)
    (seam : ∀ initial state cost, pre initial →
      middle initial state cost → nextPre state)
    (mapPost : ∀ initial state final firstCost secondCost,
      pre initial → middle initial state firstCost →
      next state final secondCost →
      post initial final (firstCost + secondCost)) :
    GasContract pre post := by
  apply consequence (fun state hstate => hstate)
    (first.trans second seam)
  intro initial final cost hinitial hfinal
  obtain ⟨state, firstCost, secondCost, hmiddle, hnext, rfl⟩ := hfinal
  exact mapPost initial state final firstCost secondCost
    hinitial hmiddle hnext

/-- Retain only a selected relation on a state projection and the cost. -/
theorem project {pre : State → Prop}
    {post : State → State → Nat → Prop} {α : Type}
    (contract : GasContract pre post) (view : State → α)
    (relation : α → α → Nat → Prop)
    (hproject : ∀ initial final cost, pre initial →
      post initial final cost →
      relation (view initial) (view final) cost) :
    GasContract pre (fun initial final cost =>
      relation (view initial) (view final) cost) := by
  exact contract.consequence (fun state hstate => hstate)
    (fun initial final cost hinitial hfinal =>
      hproject initial final cost hinitial hfinal)

/-- Attach a frame fact for a projection known to be preserved. -/
theorem frame {pre : State → Prop}
    {post : State → State → Nat → Prop} {α : Type}
    (contract : GasContract pre post) (view : State → α)
    (hframe : ∀ initial final cost, pre initial →
      post initial final cost → view final = view initial) :
    GasContract pre (fun initial final cost =>
      post initial final cost ∧ Preserves view initial final) := by
  exact contract.consequence (fun state hstate => hstate)
    (fun initial final cost hinitial hfinal =>
      ⟨hfinal, hframe initial final cost hinitial hfinal⟩)

/-- Turn exact-cost relational contracts ending in the expected done result
into the challenge's eventual-evaluation obligation. -/
theorem toEventuallyEvaluates {Input : Type}
    (initial : Input → State) (expected : Input → ExecutionResult)
    (post : Input → State → State → Nat → Prop)
    (contract : ∀ input,
      GasContract (fun state => state = initial input) (post input))
    (hdone : ∀ input final cost,
      post input (initial input) final cost → final.isDone = true)
    (hresult : ∀ input final cost,
      post input (initial input) final cost →
        final.toResult = expected input) :
    EventuallyEvaluates
      (fun input gas => withGas (initial input) gas) expected := by
  intro input
  obtain ⟨final, cost, htrace, hpost⟩ :=
    contract input (initial input) rfl
  refine ⟨cost, fun gas hgas state hstate => ?_⟩
  subst state
  refine ⟨withGas final (gas - cost), htrace gas hgas, ?_, ?_⟩
  · change final.isDone = true
    exact hdone input final cost hpost
  · change final.toResult = expected input
    exact hresult input final cost hpost

end GasContract

/-- A direct EVM trace uniform in all sufficiently large initial gas budgets.
The endpoints describe every field except gas; `withGas` supplies the actual
initial and final counters. The cost is proof-relevant so a later theorem may
state a concrete schedule without duplicating the functional execution. -/
structure GasSteps (s t : State) where
  cost : Nat
  trace : ∀ gas : Nat, cost ≤ gas →
    Steps (withGas s gas) (withGas t (gas - cost))

namespace GasSteps

/-- Hide an exact gas trace behind a relational singleton contract. -/
theorem toContract {s t : State} (trace : GasSteps s t) :
    GasContract (fun initial => initial = s)
      (fun _ final cost => final = t ∧ cost = trace.cost) := by
  intro initial hinitial
  subst initial
  exact ⟨t, trace.cost, trace.trace, rfl, rfl⟩

/-- Hide an exact gas trace while exposing only a caller-selected
postcondition. -/
theorem toContractWhere {s t : State} (trace : GasSteps s t)
    (post : State → State → Nat → Prop)
    (hpost : post s t trace.cost) :
    GasContract (fun initial => initial = s) post := by
  intro initial hinitial
  subst initial
  exact ⟨t, trace.cost, trace.trace, hpost⟩

def refl (s : State) : GasSteps s s := by
  refine ⟨0, fun gas _ => ?_⟩
  simpa using Steps.refl (withGas s gas)

def one {s t : State} (cost : Nat)
    (h : ∀ gas, cost ≤ gas →
      Step (withGas s gas) (withGas t (gas - cost))) :
    GasSteps s t := by
  refine ⟨cost, fun gas hgas => ?_⟩
  exact .trans (h gas hgas) (.refl _)

def trans {s t u : State} (hst : GasSteps s t) (htu : GasSteps t u) :
    GasSteps s u := by
  obtain ⟨c₁, h₁⟩ := hst
  obtain ⟨c₂, h₂⟩ := htu
  refine ⟨c₁ + c₂, fun gas hgas => ?_⟩
  have hc₁ : c₁ ≤ gas := by omega
  have hc₂ : c₂ ≤ gas - c₁ := by omega
  have hsub : gas - c₁ - c₂ = gas - (c₁ + c₂) := by omega
  simpa [hsub] using (h₁ gas hc₁).append (h₂ (gas - c₁) hc₂)

def iterate {I : Nat → State}
    (body : ∀ i, GasSteps (I i) (I (i + 1))) :
    ∀ n, GasSteps (I 0) (I n)
  | 0 => refl _
  | n + 1 => (iterate body n).trans (by simpa using body n)

def iterateBounded {I : Nat → State} :
    (count : Nat) →
    (∀ i, i < count → GasSteps (I i) (I (i + 1))) →
    GasSteps (I 0) (I count)
  | 0, _ => refl _
  | count + 1, body =>
      (iterateBounded count
        (fun i hi => body i (Nat.lt_succ_of_lt hi))).trans
        (body count (Nat.lt_succ_self count))

@[simp] theorem refl_cost (s : State) : (refl s).cost = 0 := rfl

@[simp] theorem one_cost {s t : State} (cost : Nat)
    (h : ∀ gas, cost ≤ gas →
      Step (withGas s gas) (withGas t (gas - cost))) :
    (one cost h).cost = cost := rfl

/-- Change only the indexed endpoints of a trace along explicit state
equalities. Unlike an implicit `Eq.mpr` introduced by `simpa`, this wrapper's
cost projection is definitionally transparent. -/
def cast {s t s' t' : State} (g : GasSteps s t)
    (hs : s = s') (ht : t = t') : GasSteps s' t' := by
  refine ⟨g.cost, ?_⟩
  subst s'
  subst t'
  exact g.trace

@[simp] theorem cast_cost {s t s' t' : State} (g : GasSteps s t)
    (hs : s = s') (ht : t = t') :
    (cast g hs ht).cost = g.cost := rfl

@[simp] theorem trans_cost {s t u : State}
    (hst : GasSteps s t) (htu : GasSteps t u) :
    (trans hst htu).cost = hst.cost + htu.cost := rfl

@[simp] theorem iterate_zero_cost {I : Nat → State}
    (body : ∀ i, GasSteps (I i) (I (i + 1))) :
    (iterate body 0).cost = 0 := rfl

@[simp] theorem iterate_succ_cost {I : Nat → State}
    (body : ∀ i, GasSteps (I i) (I (i + 1))) (n : Nat) :
    (iterate body (n + 1)).cost = (iterate body n).cost + (body n).cost := rfl

@[simp] theorem iterateBounded_zero_cost {I : Nat → State}
    (body : ∀ i, i < 0 → GasSteps (I i) (I (i + 1))) :
    (iterateBounded 0 body).cost = 0 := rfl

@[simp] theorem iterateBounded_succ_cost {I : Nat → State} (count : Nat)
    (body : ∀ i, i < count + 1 → GasSteps (I i) (I (i + 1))) :
    (iterateBounded (count + 1) body).cost =
      (iterateBounded count
        (fun i hi => body i (Nat.lt_succ_of_lt hi))).cost +
        (body count (Nat.lt_succ_self count)).cost := rfl

theorem iterateBounded_cost_of_const {I : Nat → State} (count cost : Nat)
    (body : ∀ i, i < count → GasSteps (I i) (I (i + 1)))
    (hcost : ∀ i (hi : i < count), (body i hi).cost = cost) :
    (iterateBounded count body).cost = count * cost := by
  induction count with
  | zero =>
      rw [iterateBounded_zero_cost]
      simp
  | succ count ih =>
      rw [iterateBounded_succ_cost]
      rw [ih (body := fun i hi => body i (Nat.lt_succ_of_lt hi))]
      · rw [hcost count (Nat.lt_succ_self count)]
        simp [Nat.succ_mul]
      · intro i hi
        exact hcost i (Nat.lt_succ_of_lt hi)

/-- Telescope an exact per-iteration cost equation against a state potential.
This form avoids separately proving monotonicity when the instruction meter
already states each charge as `base + nextPotential - currentPotential`. -/
theorem iterateBounded_cost_potential_eq {I : Nat → State}
    (count base : Nat) (potential : Nat → Nat)
    (body : ∀ i, i < count → GasSteps (I i) (I (i + 1)))
    (hcost : ∀ i (hi : i < count),
      (body i hi).cost + potential i = base + potential (i + 1)) :
    (iterateBounded count body).cost + potential 0 =
      count * base + potential count := by
  induction count with
  | zero => simp
  | succ count ih =>
      rw [iterateBounded_succ_cost]
      have hprefix := ih
        (body := fun i hi => body i (Nat.lt_succ_of_lt hi))
        (hcost := fun i hi => hcost i (Nat.lt_succ_of_lt hi))
      have hlast := hcost count (Nat.lt_succ_self count)
      rw [Nat.succ_mul]
      omega

/-- Sum a loop whose body has a fixed instruction cost plus the increase of a
monotone potential (typically the EVM memory high-water cost). -/
theorem iterateBounded_cost_of_potential {I : Nat → State}
    (count base : Nat) (potential : Nat → Nat)
    (body : ∀ i, i < count → GasSteps (I i) (I (i + 1)))
    (hcost : ∀ i (hi : i < count),
      (body i hi).cost = base + (potential (i + 1) - potential i))
    (hmono : Monotone potential) :
    (iterateBounded count body).cost =
      count * base + (potential count - potential 0) := by
  induction count with
  | zero =>
      rw [iterateBounded_zero_cost]
      simp
  | succ count ih =>
      rw [iterateBounded_succ_cost]
      rw [ih
        (body := fun i hi => body i (Nat.lt_succ_of_lt hi))
        (hcost := fun i hi => hcost i (Nat.lt_succ_of_lt hi))]
      rw [hcost count (Nat.lt_succ_self count)]
      have hzero : potential 0 ≤ potential count := hmono (Nat.zero_le count)
      have hstep : potential count ≤ potential (count + 1) :=
        hmono (Nat.le_succ count)
      simp only [Nat.succ_mul]
      omega

/-- Forget the explicit final gas counter and expose the ordinary predicate
reachability used by `DirectProof`. -/
theorem toReaches {s t : State} (h : GasSteps s t) :
    ∃ cost, ∀ gas, cost ≤ gas →
      Reaches (fun u => u = withGas s gas)
        (fun u => ∃ remaining, u = withGas t remaining) := by
  refine ⟨h.cost, fun gas hgas u hu => ?_⟩
  subst u
  exact ⟨_, h.trace gas hgas, gas - h.cost, rfl⟩

/-- Turn a family of gas-parametric traces to exact halted states into the
reusable `EventuallyEvaluates` obligation. Both `isDone` and
`toResult` ignore the available-gas field, so callers only need to identify
the gas-erased final state once. -/
theorem toEventuallyEvaluates {Input : Type}
    (initial final : Input → State) (expected : Input → ExecutionResult)
    (hsteps : ∀ input, GasSteps (initial input) (final input))
    (hdone : ∀ input, (final input).isDone = true)
    (hresult : ∀ input, (final input).toResult = expected input) :
    EventuallyEvaluates
      (fun input gas => withGas (initial input) gas) expected := by
  apply GasContract.toEventuallyEvaluates initial expected
    (fun input _ state cost =>
      state = final input ∧ cost = (hsteps input).cost)
    (fun input => (hsteps input).toContract)
  · intro input state _ hpost
    rw [hpost.1]
    exact hdone input
  · intro input state _ hpost
    rw [hpost.1]
    exact hresult input

end GasSteps

end Challenge.EvmProof
