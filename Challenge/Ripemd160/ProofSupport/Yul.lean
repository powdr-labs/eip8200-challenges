import Challenge.Ripemd160.ProofSupport.InitialState
import YulEvmCompiler.Correctness

set_option warningAsError true

/-!
# From a Yul-level obligation to the challenge statement

For any program accepted by the verified compiler, the bytecode challenge can
be discharged by proving two source-level facts: that the Yul program returns
the RIPEMD-160 precompile result, and that a fresh Yul state abstracts the fixed
EVM initial state.
-/

namespace Challenge.Ripemd160

open EvmSemantics
open EvmSemantics.EVM
open YulSemantics (Block Run VEnv)
open YulSemantics.EVM (EvmState Op evmWithExternal ExternalCalls ExternalCreates)
open YulEvmCompiler

/-- The RIPEMD-160 precompile result at the byte-list view used by Yul
semantics. -/
def digestOf (calldata : List UInt8) : List UInt8 :=
  (spec (mkCode calldata)).toList

/-- The reference implementation neither calls contracts nor creates them. -/
@[reducible] def localModel : ExternalModel :=
  { calls := ExternalCalls.none, creates := ExternalCreates.none }

/-- The gas-free source dialect used by the functional obligation. -/
abbrev localDialect := evmWithExternal ExternalCalls.none ExternalCreates.none

/-- A target initial state is represented by a fresh Yul state carrying the
same calldata. `StateMatch` is gas-independent, so one source state suffices
for every target gas budget. -/
def AbstractsInitialState (code : ByteArray) : Prop :=
  ∀ calldata : ByteArray, ∃ yst : EvmState,
    (∀ g : Nat, StateMatch yst (initialState code calldata g)) ∧
    yst.memory = (fun _ => 0) ∧
    yst.env.calldata = calldata.toList ∧
    yst.env.immutable = (fun _ => 0) ∧
    yst.halted = none

/-- From any fresh source state, the program returns the 32-byte, left-padded
Ethereum RIPEMD-160 precompile result for its calldata. -/
def ComputesDigest (prog : Block Op) : Prop :=
  ∀ yst : EvmState, yst.memory = (fun _ => 0) → yst.halted = none →
    ∃ (V : VEnv localDialect) (yst' : EvmState),
      Run localDialect prog yst V yst' .halt ∧
        yst'.halted = some (.ret, digestOf yst.env.calldata)

/-- The challenge's fixed initial state meets the verified compiler theorem's
target-side frame conditions. -/
theorem initialState_frameOK {code calldata : ByteArray} {gas : Nat}
    (hsize : code.size < 2 ^ 256) : FrameOK code (initialState code calldata gas) where
  hcode := rfl
  codeSmall := hsize
  fork := rfl
  noPrecompile := deployAddress_not_precompile
  callStack := rfl
  running := rfl

/-- A source-level digest proof, together with the verified compiler theorem,
implies the bytecode challenge statement. -/
theorem correct_of_computesDigest {prog : Block Op} {is : List Instr}
    (hcomp : compile prog = some is)
    (hsize : (assemble is).size < 2 ^ 256)
    (habs : AbstractsInitialState (assemble is))
    (hyul : ComputesDigest prog) :
    Correct (assemble is) := by
  intro calldata _hfit
  obtain ⟨yst, hmatch, hmem, hcd, himmutable, hhalted⟩ := habs calldata
  obtain ⟨V, yst', hrun, hres⟩ := hyul yst hmem hhalted
  obtain ⟨b, H⟩ :=
    compile_correct_eval (model := localModel) ExternalsRealized.none hcomp
      (by intro key; rw [himmutable]; rfl) hrun
  refine ⟨b, fun g hg => ?_⟩
  obtain ⟨-, hhalt⟩ :=
    H (initialState (assemble is) calldata g) (initialState_frameOK hsize) (hmatch g)
      (initialState_pc _ _ _) (initialState_stack _ _ _) (by rw [initialState_gas]; exact hg)
  obtain ⟨hk, hyk, heval⟩ := hhalt rfl
  rw [hres] at hyk
  cases hyk
  simpa [resultOf, digestOf, hcd, mkCode_toList, spec] using heval

end Challenge.Ripemd160
