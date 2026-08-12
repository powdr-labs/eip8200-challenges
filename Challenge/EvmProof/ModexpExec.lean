import Challenge.EvmProof.ExecSound
import Challenge.EvmProof.ModexpCalls
import YulSemantics.Adequacy

set_option warningAsError true

/-!
# Executable source semantics for successful MODEXP calls

The open-world Yul dialect is relational and therefore has no interpreter.
For proof-friendly programs whose only external effect is a successful Osaka
MODEXP call, this module supplies a deterministic sub-dialect.  Every step of
the sub-dialect is admitted by `successfulModexpCalls`; it does not strengthen
or otherwise replace the open-world semantics used by compiler correctness.
-/

namespace Challenge.EvmProof

open EvmSemantics EvmSemantics.EVM
open YulSemantics YulSemantics.EVM

private def modexpResponse (st : EvmState) (output : ByteArray) : CallResponse :=
  { success := true
    returndata := output.toList
    world := CallWorld.ofState st }

/-- Deterministic evaluator for local EVM operations and successful Osaka
MODEXP `staticcall`s.  Unsupported or unsuccessful external operations are
stuck, exactly as expected for a deterministic sub-dialect. -/
def modexpBuiltinFn (op : Op) (args : List U256) (st : EvmState) :
    Option (BuiltinResult U256 EvmState) :=
  match op, args with
  | .staticcall, [gas, target, inputOffset, inputSize, outputOffset, outputSize] =>
      if target = BitVec.ofNat 256 5 then
        let input := readBytes st.memory inputOffset.toNat inputSize.toNat
        match Precompile.runModexp .Osaka ⟨input.toArray⟩ gas.toNat with
        | .success output _ =>
            let response := modexpResponse st output
            some (.ok [response.flag]
              (finishCall .staticcall st response inputOffset.toNat inputSize.toNat
                outputOffset.toNat outputSize.toNat))
        | .outOfGas => none
      else none
  | .gas, _ | .call, _ | .callcode, _ | .delegatecall, _
  | .staticcall, _ | .create, _ | .create2, _ => none
  | _, _ => stepOp op args st

/-- Executable graph dialect used only to obtain checked source derivations. -/
@[reducible] def modexpExec : ExecDialect :=
  { toDialect := EVM.evmWithExternal successfulModexpCalls ExternalCreates.none
    builtinFn := modexpBuiltinFn }

set_option linter.unnecessarySimpa false in
/-- Every computed builtin result is admitted by the open relational dialect. -/
theorem modexpBuiltinFn_sound {op args st result}
    (h : modexpBuiltinFn op args st = some result) :
    (EVM.evmWithExternal successfulModexpCalls ExternalCreates.none).Builtin
      op args st result := by
  change builtinWithExternal successfulModexpCalls ExternalCreates.none
    op args st result
  cases op <;> try {
    change stepOp _ args st = some result
    simpa only [modexpBuiltinFn] using h }
  case staticcall =>
    rcases args with _ | ⟨gas, _ | ⟨target, _ | ⟨inputOffset, _ |
      ⟨inputSize, _ | ⟨outputOffset, _ | ⟨outputSize, rest⟩⟩⟩⟩⟩⟩
    all_goals try { simp [modexpBuiltinFn] at h }
    cases rest with
    | cons _ _ => simp [modexpBuiltinFn] at h
    | nil =>
      simp only [modexpBuiltinFn] at h
      split at h
      next htarget =>
        split at h
        next output gasUsed hrun =>
          injection h with hresult
          subst result
          simp only [builtinWithExternal]
          refine ⟨modexpResponse st output, ?_, rfl⟩
          exact ⟨rfl, htarget, rfl, output, gasUsed, hrun, rfl, rfl, rfl⟩
        next => contradiction
      next => contradiction
  all_goals simp [modexpBuiltinFn] at h

/-- Interpreter success for the deterministic MODEXP evaluator is sound for
the open successful-MODEXP source relation used by the compiler proof. -/
theorem modexpExec_run_sound {fuel program st0 V' st' outcome}
    (h : Interp.run modexpExec fuel program st0 = .ok (V', st', outcome)) :
    Run modexpExec.toDialect program st0 V' st' outcome :=
  Interp.run_sound_of (fun _ _ _ _ hbuiltin =>
    modexpBuiltinFn_sound hbuiltin) h

end Challenge.EvmProof
