import Challenge.Ripemd160.ProofSupport.InitialState
import Challenge.Ripemd160.YulSpec
import Challenge.YulProof.ClosedEvm
import YulEvmCompiler.ContractCorrectness

set_option warningAsError true

/-!
# From a Yul-level obligation to the challenge statement

For any program accepted by the verified compiler, a proof of the public
`Challenge.Ripemd160.Yul.Correct` predicate transports to the bytecode
challenge once the source and target initial states are related.
-/

namespace Challenge.Ripemd160

open EvmSemantics
open EvmSemantics.EVM
open YulSemantics (Block RunContract VEnv)
open YulSemantics.EVM (EvmState Op)
open YulEvmCompiler

/-- Compatibility names for the shared closed EVM source semantics. -/
abbrev localModel := Challenge.YulProof.ClosedEvm.model
abbrev localDialect := Challenge.YulProof.ClosedEvm.dialect
abbrev localBuiltinFn := Challenge.YulProof.ClosedEvm.builtinFn
abbrev localExec := Challenge.YulProof.ClosedEvm.exec
theorem localExec_lawful : localExec.Lawful :=
  Challenge.YulProof.ClosedEvm.exec_lawful
theorem localExternalsRealized : ExternalsRealized localModel :=
  Challenge.YulProof.ClosedEvm.externalsRealized

/-- Backwards-compatible name for the public Yul result function. New
candidate-facing statements should use `Challenge.Ripemd160.Yul.result`. -/
abbrev digestOf := Yul.result

/-- A target initial state is represented by a fresh Yul state carrying the
same calldata. `StateMatch` is gas-independent, so one source state suffices
for every target gas budget. -/
def AbstractsInitialState (code : ByteArray) : Prop :=
  ∀ calldata : ByteArray, ∃ yst : EvmState,
    (∀ g : Nat, StateMatch yst (initialState code calldata g)) ∧
    yst.memory = (fun _ => 0) ∧
    yst.env.calldata = calldata.toList ∧
    (∀ k, yst.env.immutable k = 0) ∧
    yst.halted = none

/-- Backwards-compatible name for the public source-level challenge. New
candidate proofs should state `Challenge.Ripemd160.Yul.Correct program`. -/
abbrev ComputesDigest := Yul.Correct

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
    (hyul : Yul.Correct prog) :
    Correct (assemble is) := by
  intro calldata hfit
  obtain ⟨yst, hmatch, hmem, hcd, himm, hhalted⟩ := habs calldata
  obtain ⟨V, yst', outcome, ⟨houtcome, hres⟩, b, H⟩ :=
    compile_runContract_eval (model := localModel) localExternalsRealized hcomp hyul
      ⟨hmem, hhalted, calldata, hcd, hfit⟩ (fun key => (himm _).symm)
  subst outcome
  refine ⟨b, fun g hg => ?_⟩
  obtain ⟨-, hhalt⟩ :=
    H (initialState (assemble is) calldata g) (initialState_frameOK hsize) (hmatch g)
      (initialState_pc _ _ _) (initialState_stack _ _ _) (by rw [initialState_gas]; exact hg)
  obtain ⟨hk, hyk, heval⟩ := hhalt rfl
  rw [hres] at hyk
  cases hyk
  simpa [resultOf, hcd, spec, mkCode_toList] using heval

end Challenge.Ripemd160
