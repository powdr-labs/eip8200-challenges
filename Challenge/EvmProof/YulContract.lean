import YulSemantics.BigStep

set_option warningAsError true

/-!
# Relational contracts for complete Yul runs

This source-only layer packages a `YulSemantics.Run` behind pre- and
postconditions.  The postcondition observes an existential final state; callers
therefore need not name or unfold a concrete state-construction expression.

Gas is deliberately absent.  The Yul EVM dialect state is gas-free, and gas
enters at the compiler-to-EVM refinement boundary.
-/

namespace Challenge.EvmProof

open YulSemantics

/-- A Hoare-style contract for a complete Yul block.

For every initial state satisfying `pre`, the block has a big-step execution
whose environment, final state, and outcome satisfy `post`. -/
def YulRunContract (D : Dialect) [DecidableEq D.Value]
    (program : Block D.Op) (pre : D.State → Prop)
    (post : D.State → VEnv D → D.State → Outcome → Prop) : Prop :=
  ∀ initial, pre initial →
    ∃ finalEnv final outcome,
      Run D program initial finalEnv final outcome ∧
        post initial finalEnv final outcome

namespace YulRunContract

/-- Strengthen a precondition and weaken a postcondition without reopening the
source execution proof. -/
theorem consequence {D : Dialect} [DecidableEq D.Value]
    {program : Block D.Op} {pre pre' : D.State → Prop}
    {post post' : D.State → VEnv D → D.State → Outcome → Prop}
    (contract : YulRunContract D program pre post)
    (hpre : ∀ initial, pre' initial → pre initial)
    (hpost : ∀ initial finalEnv final outcome,
      pre' initial → post initial finalEnv final outcome →
        post' initial finalEnv final outcome) :
    YulRunContract D program pre' post' := by
  intro initial hinitial
  obtain ⟨finalEnv, final, outcome, run, result⟩ :=
    contract initial (hpre initial hinitial)
  exact ⟨finalEnv, final, outcome, run,
    hpost initial finalEnv final outcome hinitial result⟩

end YulRunContract
end Challenge.EvmProof
