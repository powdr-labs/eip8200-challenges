import Challenge.Sha256.Spec

set_option warningAsError true

/-!
# Context-independent strengthening

The minimal specification uses one fixed fresh EVM state. This optional goal
makes independence from irrelevant caller and world state explicit.
-/

namespace Challenge.Sha256

open EvmSemantics.EVM

/-- The context-generalized statement: the same conclusion from any machine
state that is at the fresh entry point for `code`, while allowing the world,
caller, call value, address, and storage to vary. This is not an arbitrary
mid-execution state: the PC, stacks, memory, halt status, fork, and code still
satisfy the listed entry conditions. -/
def CorrectInAnyContext (code : ByteArray) : Prop :=
  ∀ (s : State), s.executionEnv.code = code → s.pc = 0 → s.stack = [] →
    s.callStack = [] → s.halt = .Running → s.memory = .empty →
    s.activeWords = 0 → s.executionEnv.fork = .Osaka →
    Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork s.executionEnv.codeAddr = false →
    CalldataFits s.executionEnv.calldata →
    ∃ g₀ : Nat, ∀ g : Nat, g₀ ≤ g →
      Eval { s with gasAvailable := g } (.returned (spec s.executionEnv.calldata))

end Challenge.Sha256
