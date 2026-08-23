import Challenge.Modexp.ProofSupport.InitialState
import Challenge.Modexp.YulSpec
import Challenge.YulProof.ClosedEvm
import YulEvmCompiler.ContractCorrectness

set_option warningAsError true

/-!
# From a MODEXP Yul obligation to the bytecode challenge

For a program accepted by the verified compiler, a proof of the public
`Challenge.Modexp.Yul.Correct` predicate transports to the bytecode challenge
once the source and target initial states are related.
-/

namespace Challenge.Modexp

open EvmSemantics
open EvmSemantics.EVM
open YulSemantics (Block RunContract)
open YulSemantics.EVM (EvmState Op)
open YulEvmCompiler
open Challenge.YulProof.ClosedEvm

/-- Backwards-compatible name for the public Yul result function. New
candidate-facing statements should use `Challenge.Modexp.Yul.result`. -/
abbrev resultBytes := Yul.result

/-- A fresh source state with matching calldata represents the fixed target
initial state for every gas budget. -/
def AbstractsInitialState (code : ByteArray) : Prop :=
  ∀ calldata : ByteArray, ∃ yst : EvmState,
    (∀ g : Nat, StateMatch yst (initialState code calldata g)) ∧
    yst.memory = (fun _ => 0) ∧
    yst.env.calldata = calldata.toList ∧
    (∀ k, yst.env.immutable k = 0) ∧
    yst.halted = none

/-- Backwards-compatible name for the public source-level challenge. New
candidate proofs should state `Challenge.Modexp.Yul.Correct program`. -/
abbrev ComputesResult := Yul.Correct

theorem initialState_frameOK {code calldata : ByteArray} {gas : Nat}
    (hsize : code.size < 2 ^ 256) : FrameOK code (initialState code calldata gas) where
  hcode := rfl
  codeSmall := hsize
  fork := rfl
  noPrecompile := deployAddress_not_precompile
  callStack := rfl
  running := rfl

/-- The verified compiler transports a complete source-Yul MODEXP proof to
the bytecode challenge. -/
theorem correct_of_computesResult {prog : Block Op} {is : List Instr}
    (hcomp : compile prog = some is)
    (hsize : (assemble is).size < 2 ^ 256)
    (habs : AbstractsInitialState (assemble is))
    (hyul : Yul.Correct prog) :
    Correct (assemble is) := by
  intro calldata hvalid
  obtain ⟨yst, hmatch, hmem, hcd, himm, hhalted⟩ := habs calldata
  obtain ⟨V, yst', outcome, ⟨houtcome, hres⟩, b, H⟩ :=
    compile_runContract_eval (model := model) externalsRealized hcomp hyul
      ⟨hmem, hhalted, calldata, hcd, hvalid⟩ (fun key => (himm _).symm)
  subst outcome
  refine ⟨b, fun g hg => ?_⟩
  obtain ⟨-, hhalt⟩ :=
    H (initialState (assemble is) calldata g) (initialState_frameOK hsize) (hmatch g)
      (initialState_pc _ _ _) (initialState_stack _ _ _) (by rw [initialState_gas]; exact hg)
  obtain ⟨hk, hyk, heval⟩ := hhalt rfl
  rw [hres] at hyk
  cases hyk
  simpa [resultOf, hcd, spec, mkCode_toList] using heval

end Challenge.Modexp
