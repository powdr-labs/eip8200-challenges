import Challenge.Blake2f.ProofSupport.InitialState
import YulEvmCompiler.Correctness
set_option warningAsError true

/-!
# Reusable verified-Yul reduction for BLAKE2f submissions

This module packages the compiler theorem around the complete EIP-152
successful-or-exceptional interface. A submission only needs a source-level
execution proof and the standard initial-state abstraction.
-/

namespace Challenge.Blake2f.ProofSupport.Yul

open EvmSemantics
open EvmSemantics.EVM
open YulSemantics (Block Run VEnv)
open YulSemantics.EVM (EvmState Op evmWithExternal ExternalCalls ExternalCreates)
open YulEvmCompiler

@[reducible] def localModel : ExternalModel :=
  { calls := ExternalCalls.none, creates := ExternalCreates.none }

abbrev localDialect := evmWithExternal ExternalCalls.none ExternalCreates.none

@[simp] theorem mkCode_dataToList (bytes : ByteArray) :
    mkCode bytes.data.toList = bytes := by
  apply ByteArray.ext
  exact Array.toArray_toList

/-- Target behavior at the byte-list interface of Yul semantics. -/
def expectedHalt (calldata : List UInt8) : YulSemantics.EVM.HaltKind × List UInt8 :=
  let input := mkCode calldata
  if validInput input then (.ret, (spec input).data.toList) else (.invalid, [])

/-- A fresh source state represents every gas instantiation of the fixed EVM
frame. `StateMatch` itself is gas-independent. -/
def AbstractsInitialState (code : ByteArray) : Prop :=
  ∀ calldata : ByteArray, ∃ yst : EvmState,
    (∀ gas : Nat, StateMatch yst (initialState code calldata gas)) ∧
    yst.memory = (fun _ => 0) ∧
    mkCode yst.env.calldata = calldata ∧
    yst.halted = none

/-- Complete source-level obligation, including malformed-input `invalid()`. -/
def ComputesBehavior (program : Block Op) : Prop :=
  ∀ yst : EvmState, yst.memory = (fun _ => 0) → yst.halted = none →
    ∃ (V : VEnv localDialect) (yst' : EvmState),
      Run localDialect program yst V yst' .halt ∧
      yst'.halted = some (expectedHalt yst.env.calldata)

theorem initialState_frameOK {code calldata : ByteArray} {gas : Nat}
    (hsize : code.size < 2 ^ 256) :
    FrameOK code (initialState code calldata gas) where
  hcode := rfl
  codeSmall := hsize
  fork := rfl
  noPrecompile := deployAddress_not_precompile
  callStack := rfl
  running := rfl

/-- Verified compilation transports the complete Yul behavior to the public
raw-bytecode challenge predicate. -/
theorem correct_of_computesBehavior {program : Block Op} {instructions : List Instr}
    (hcompile : compile program = some instructions)
    (hsize : (assemble instructions).size < 2 ^ 256)
    (habstract : AbstractsInitialState (assemble instructions))
    (hbehavior : ComputesBehavior program) :
    Correct (assemble instructions) := by
  intro calldata _hfit
  obtain ⟨yst, hmatch, hmemory, hcalldata, hhalted⟩ := habstract calldata
  obtain ⟨V, yst', hrun, hresult⟩ := hbehavior yst hmemory hhalted
  obtain ⟨cost, compiled⟩ :=
    compile_correct_eval (model := localModel) ExternalsRealized.none hcompile hrun
  refine ⟨cost, fun gas hgas => ?_⟩
  obtain ⟨-, hhalt⟩ := compiled
    (initialState (assemble instructions) calldata gas)
    (initialState_frameOK hsize) (hmatch gas)
    (initialState_pc _ _ _) (initialState_stack _ _ _)
    (by rw [initialState_gas]; exact hgas)
  obtain ⟨halt, yulHalt, heval⟩ := hhalt rfl
  rw [hresult] at yulHalt
  cases yulHalt
  refine ⟨resultOf (expectedHalt yst.env.calldata), heval, ?_⟩
  unfold expectedHalt
  rw [hcalldata]
  by_cases hvalid : validInput calldata = true
  · simp [Matches, hvalid, resultOf]
  · simp [Matches, hvalid, resultOf]

end Challenge.Blake2f.ProofSupport.Yul
