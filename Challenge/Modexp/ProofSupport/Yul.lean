import Challenge.Modexp.ProofSupport.InitialState
import Challenge.YulProof.ClosedEvm
import YulEvmCompiler.ContractCorrectness

set_option warningAsError true

/-!
# From a MODEXP Yul obligation to the bytecode challenge

For a program accepted by the verified compiler, it is enough to prove that
the source returns the MODEXP specification from a fresh local EVM state and
that this state abstracts the challenge's fixed target state.
-/

namespace Challenge.Modexp

open EvmSemantics
open EvmSemantics.EVM
open YulSemantics (Block RunContract)
open YulSemantics.EVM (EvmState Op)
open YulEvmCompiler
open Challenge.YulProof.ClosedEvm

/-- The MODEXP result at the byte-list view used by Yul semantics. -/
def resultBytes (calldata : List UInt8) : List UInt8 :=
  (spec (mkCode calldata)).toList

/-- A fresh source state with matching calldata represents the fixed target
initial state for every gas budget. -/
def AbstractsInitialState (code : ByteArray) : Prop :=
  ∀ calldata : ByteArray, ∃ yst : EvmState,
    (∀ g : Nat, StateMatch yst (initialState code calldata g)) ∧
    yst.memory = (fun _ => 0) ∧
    yst.env.calldata = calldata.toList ∧
    (∀ k, yst.env.immutable k = 0) ∧
    yst.halted = none

/-- From fresh memory and valid MODEXP calldata, the source program returns
exactly the successful precompile result. -/
def ComputesResult (prog : Block Op) : Prop :=
  RunContract (D := dialect) prog
    (fun yst => yst.memory = (fun _ => 0) ∧ yst.halted = none ∧
      ∃ input : ByteArray, yst.env.calldata = input.toList ∧ ValidInput input)
    (fun yst _ yst' outcome => outcome = .halt ∧
      yst'.halted = some (.ret, resultBytes yst.env.calldata))

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
    (hyul : ComputesResult prog) :
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
  simpa [resultOf, resultBytes, hcd, mkCode_toList, spec] using heval

end Challenge.Modexp
