import Challenge.YulProof.ClosedEvmDialect
import YulEvmCompiler.ContractCorrectness

set_option warningAsError true

/-!
# Closed executable EVM dialect for source-Yul proofs

This module packages the compiler's no-calls, no-creates, gas-free EVM dialect
as an executable semantics.  It is shared by challenge proofs whose Yul only
uses local EVM operations.
-/

namespace Challenge.YulProof.ClosedEvm

open YulSemantics.EVM
  (EvmState Op evmWithExternal ExternalCalls ExternalCreates ExternalGas)
open YulEvmCompiler

/-- The closed external model used by local source programs. -/
@[reducible] def model : ExternalModel :=
  { calls := ExternalCalls.none, creates := ExternalCreates.none, gas := ExternalGas.none }

/-- Executable builtins for the closed dialect.  Static-context violations are
resolved locally; unavailable external effects and `gas()` remain absent. -/
def builtinFn (op : Op) (args : List YulSemantics.EVM.U256) (st : EvmState) :
    Option (YulSemantics.BuiltinResult YulSemantics.EVM.U256 EvmState) :=
  match op with
  | .call => match args with
      | [_, _, value, _, _, _, _] =>
          if st.env.static ∧ value ≠ 0 then
            some (YulSemantics.BuiltinResult.halt
              { st with halted := some (.staticViolation, []) })
          else none
      | _ => none
  | .callcode | .delegatecall | .staticcall => none
  | .create => match args with
      | [_, _, _] =>
          if st.env.static then
            some (YulSemantics.BuiltinResult.halt
              { st with halted := some (.staticViolation, []) })
          else none
      | _ => none
  | .create2 => match args with
      | [_, _, _, _] =>
          if st.env.static then
            some (YulSemantics.BuiltinResult.halt
              { st with halted := some (.staticViolation, []) })
          else none
      | _ => none
  | .gas => none
  | _ => YulSemantics.EVM.stepOp op args st

/-- Executable presentation of `dialect`. -/
@[reducible] def exec : YulSemantics.ExecDialect :=
  { toDialect := dialect, builtinFn := builtinFn }

theorem exec_lawful : exec.Lawful := by
  intro op args st result
  cases op <;>
    simp [exec, dialect, evmWithExternal, builtinFn,
      YulSemantics.EVM.builtinWithExternal, YulSemantics.EVM.externalCall,
      YulSemantics.EVM.externalCreate, ExternalCalls.none, ExternalCreates.none,
      ExternalGas.none, YulSemantics.EVM.stepOp]
  all_goals
    rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, _ | ⟨f, _ | ⟨g, args⟩⟩⟩⟩⟩⟩⟩ <;>
      simp <;> try split <;> simp_all
  all_goals
    intros
    constructor <;> intro h <;> exact h.symm

/-- The closed external model has no realizability obligations. -/
theorem externalsRealized : ExternalsRealized model :=
  ⟨CallsRealized.none, CreatesRealized.none, GasCallsRealized.noneOracle _⟩

end Challenge.YulProof.ClosedEvm
