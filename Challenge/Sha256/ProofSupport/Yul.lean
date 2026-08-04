import Challenge.Sha256.ProofSupport.InitialState
import YulEvmCompiler.Correctness
set_option warningAsError true
/-!
# From a Yul-level obligation to the challenge statement

The point of a verified compiler in a challenge like this one: **nobody has
to reason about bytecode.** This module proves that for any program our
compiler accepts, `Challenge.Sha256.Correct` of the emitted bytecode follows
from two facts about the *Yul source* alone —

* `ComputesDigest prog` — the Yul program, run from a fresh state, halts by
  returning the digest of its calldata;
* `AbstractsInitialState code` — the fixed EVM initial state is matched by some
  yul-semantics state with the same calldata and empty memory (pure
  plumbing: build the source-level state from the target one).

Everything between those and executable bytecode — code generation, the
labeled-assembly layer, the calling convention, byte layout, gas, decoding —
is already proved in this repository and is consumed here as
`compile_correct_eval`.

Both hypotheses are ordinary `Prop`s, so this module carries no unfinished
proof of its own; what is open is *inhabiting* them, which is the challenge.
-/

namespace Challenge.Sha256

open EvmSemantics
open EvmSemantics.EVM
open YulSemantics (Block Run VEnv)
open YulSemantics.EVM (EvmState Op evmWithExternal ExternalCalls ExternalCreates)
open YulEvmCompiler

/-- The SHA specification at the byte-list view used by Yul semantics. -/
def digestOf (calldata : List UInt8) : List UInt8 :=
  (spec (mkCode calldata)).toList

/-- The closed-world model: the reference implementation makes no external
calls and creates no contracts, so the open-world relations are empty and
`ExternalsRealized.none` discharges the compiler theorem's side condition. -/
@[reducible] def localModel : ExternalModel :=
  { calls := ExternalCalls.none, creates := ExternalCreates.none }

/-- The gas-free source dialect the obligation is stated against. -/
abbrev localDialect := evmWithExternal ExternalCalls.none ExternalCreates.none

/-- Every fixed initial state for `code` is matched by a yul-semantics state
that has the same calldata, empty memory, and has
not halted. One state serves every gas level, because `StateMatch` does not
mention gas. -/
def AbstractsInitialState (code : ByteArray) : Prop :=
  ∀ calldata : ByteArray, ∃ yst : EvmState,
    (∀ g : Nat, StateMatch yst (initialState code calldata g)) ∧
    yst.memory = (fun _ => 0) ∧
    yst.env.calldata = calldata.toList ∧
    yst.env.immutable = (fun _ => 0) ∧
    yst.halted = none

/-- From any fresh yul-semantics state, `prog` halts via `return` with exactly
the SHA-256 digest of the state's calldata. This is the functional premise for
the optional verified-Yul reduction. -/
def ComputesDigest (prog : Block Op) : Prop :=
  ∀ yst : EvmState, yst.memory = (fun _ => 0) → yst.halted = none →
    ∃ (V : VEnv localDialect) (yst' : EvmState),
      Run localDialect prog yst V yst' .halt ∧
        yst'.halted = some (.ret, digestOf yst.env.calldata)

/-- The fixed initial state satisfies the compiler theorem's target-side
conditions. This belongs to the Yul reduction, not the challenge spec. -/
theorem initialState_frameOK {code calldata : ByteArray} {gas : Nat}
    (hsize : code.size < 2 ^ 256) : FrameOK code (initialState code calldata gas) where
  hcode := rfl
  codeSmall := hsize
  fork := rfl
  noPrecompile := deployAddress_not_precompile
  callStack := rfl
  running := rfl

/-- **The reduction.** A compiler-accepted Yul program that computes the
digest yields bytecode satisfying the challenge statement. No step of this
proof mentions an opcode: the bytecode-level work is `compile_correct_eval`.

`hsize` is the trivial code-size side condition (`FrameOK.codeSmall`); for a
concrete submission it is `by decide` on the emitted length. -/
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

end Challenge.Sha256
