import Challenge.YulProof.ClosedEvm

set_option warningAsError true

/-! # Relational memory-operation lemmas for the closed EVM dialect -/

namespace Challenge.YulProof.ClosedEvm

open YulSemantics YulSemantics.EVM

@[simp] theorem touchMemory_memory (st : EvmState) (offset size : Nat) :
    (touchMemory st offset size).memory = st.memory := by
  rfl

@[simp] theorem touchMemory_activeWords (st : EvmState) (offset size : Nat) :
    (touchMemory st offset size).activeWords = BitVec.ofNat 256
      (activeWordsAfter st.activeWords.toNat offset size) := by
  rfl

@[simp] theorem touchMemory_storage (st : EvmState) (offset size : Nat) :
    (touchMemory st offset size).storage = st.storage := by
  rfl

@[simp] theorem touchMemory_transient (st : EvmState) (offset size : Nat) :
    (touchMemory st offset size).transient = st.transient := by
  rfl

@[simp] theorem touchMemory_env (st : EvmState) (offset size : Nat) :
    (touchMemory st offset size).env = st.env := by
  rfl

@[simp] theorem touchMemory_returndata (st : EvmState) (offset size : Nat) :
    (touchMemory st offset size).returndata = st.returndata := by
  rfl

@[simp] theorem touchMemory_logs (st : EvmState) (offset size : Nat) :
    (touchMemory st offset size).logs = st.logs := by
  rfl

@[simp] theorem touchMemory_selfdestructs (st : EvmState)
    (offset size : Nat) :
    (touchMemory st offset size).selfdestructs = st.selfdestructs := by
  rfl

/-- State update performed by the closed EVM dialect's `return` builtin. -/
def returnState (st : EvmState) (offset size : Nat) : EvmState :=
  { touchMemory st offset size with
    halted := some (.ret, readBytes st.memory offset size) }

@[simp] theorem returnState_halted (st : EvmState) (offset size : Nat) :
    (returnState st offset size).halted =
      some (.ret, readBytes st.memory offset size) := by
  rfl

@[simp] theorem returnState_memory (st : EvmState) (offset size : Nat) :
    (returnState st offset size).memory = st.memory := by
  change (touchMemory st offset size).memory = st.memory
  exact touchMemory_memory st offset size

@[simp] theorem returnState_activeWords (st : EvmState) (offset size : Nat) :
    (returnState st offset size).activeWords = BitVec.ofNat 256
      (activeWordsAfter st.activeWords.toNat offset size) := by
  change (touchMemory st offset size).activeWords = _
  exact touchMemory_activeWords st offset size

@[simp] theorem returnState_storage (st : EvmState) (offset size : Nat) :
    (returnState st offset size).storage = st.storage := by
  change (touchMemory st offset size).storage = st.storage
  exact touchMemory_storage st offset size

@[simp] theorem returnState_transient (st : EvmState) (offset size : Nat) :
    (returnState st offset size).transient = st.transient := by
  change (touchMemory st offset size).transient = st.transient
  exact touchMemory_transient st offset size

@[simp] theorem returnState_env (st : EvmState) (offset size : Nat) :
    (returnState st offset size).env = st.env := by
  change (touchMemory st offset size).env = st.env
  exact touchMemory_env st offset size

@[simp] theorem returnState_returndata (st : EvmState) (offset size : Nat) :
    (returnState st offset size).returndata = st.returndata := by
  change (touchMemory st offset size).returndata = st.returndata
  exact touchMemory_returndata st offset size

@[simp] theorem returnState_logs (st : EvmState) (offset size : Nat) :
    (returnState st offset size).logs = st.logs := by
  change (touchMemory st offset size).logs = st.logs
  exact touchMemory_logs st offset size

@[simp] theorem returnState_selfdestructs (st : EvmState)
    (offset size : Nat) :
    (returnState st offset size).selfdestructs = st.selfdestructs := by
  change (touchMemory st offset size).selfdestructs = st.selfdestructs
  exact touchMemory_selfdestructs st offset size

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
