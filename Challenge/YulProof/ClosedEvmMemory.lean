import Challenge.YulProof.ClosedEvm

set_option warningAsError true

/-! # Relational memory-operation lemmas for the closed EVM dialect -/

namespace Challenge.YulProof.ClosedEvm

open YulSemantics YulSemantics.EVM

@[simp] theorem touchMemory_memory (st : EvmState) (offset size : Nat) :
    (touchMemory st offset size).memory = st.memory := by
  rfl

/-- Evaluating `mload(offset)` reads one word and records the corresponding
memory touch. -/
theorem eval_mload (funs : FunEnv dialect) (V : VEnv dialect)
    (st : EvmState) (offset : Nat) (hoffset : offset < 2 ^ 256) :
    EvalExpr dialect funs V st (.builtin .mload [.lit (.number offset)])
      (.vals [loadWord st.memory offset] (touchMemory st offset 32)) := by
  refine Step.builtinOk (D := dialect)
    (Step.argsCons Step.argsNil Step.lit) ?_
  exact (exec_lawful _ _ _ _).mpr (by
    simp [exec, builtinFn, stepOp, EVM.litValue]
    have hoffset' : offset <
        115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
      norm_num at hoffset ⊢
      exact hoffset
    rw [Nat.mod_eq_of_lt hoffset']
    exact ⟨rfl, rfl⟩)

end Challenge.YulProof.ClosedEvm
