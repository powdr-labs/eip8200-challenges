import Challenge.Ripemd160.ProofSupport.InitialState
import YulEvmCompiler.Correctness
import YulEvmCompiler.Optimizer.Spec.EvmBackend

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

/-- Result-level corollary of the abstracted backend contract, for a source run
that halts: the emitted bytecode `Eval`s to the `ExecutionResult` the recorded
Yul halt denotes.

This is the halt branch of the library's `compile_correct_eval`, restated over
`Optimizer.EvmBackend.Correct` instead of the classic backend's
`compile_correct`.  The derivation is the library's, verbatim: it only ever uses
the `Steps`/`HaltedMatch` conclusion that every `EvmBackend` supplies, never
anything specific to `YulEvmCompiler.compile`. -/
theorem backend_correct_eval_halt (B : Optimizer.EvmBackend)
    {prog : Block Op} {is : List Instr} {imm : String → YulSemantics.EVM.U256}
    (hcomp : B.compile prog imm = some is)
    {yst0 : EvmState} {V' : VEnv localDialect} {yst' : EvmState}
    (himm : ∀ key,
      imm key = yst0.env.immutable (YulSemantics.EVM.litValue (.string key)))
    (hrun : Run localDialect prog yst0 V' yst' .halt) :
    ∃ b : Nat, ∀ s0 : State,
      FrameOK (assemble is) s0 → StateMatch yst0 s0 →
      s0.pc = UInt256.ofNat 0 → s0.stack = [] → b ≤ s0.gasAvailable →
      ∃ hk, yst'.halted = some hk ∧ Eval s0 (resultOf hk) := by
  obtain ⟨b, H⟩ := B.correct localModel ExternalsRealized.none hcomp himm hrun
  refine ⟨b, fun s0 hf hm hpc hstk hgas => ?_⟩
  obtain ⟨s', hsteps, hcs', -, hres⟩ := H s0 hf hm hpc hstk hgas
  rcases hres with ⟨hcontra, -⟩ | ⟨-, hhm⟩
  · exact absurd hcontra (by simp)
  obtain ⟨hk, hyst, hhmatch⟩ := hhm
  refine ⟨hk, hyst, ?_⟩
  have hdone : s'.halt ≠ .Running ∧ s'.toResult = resultOf hk := by
    rcases hk with ⟨kind, payload⟩
    cases kind with
    | stop =>
      have hhalt : s'.halt = .Success := hhmatch
      exact ⟨by rw [hhalt]; simp, by
        rw [State.toResult_success s' hhalt]; rfl⟩
    | ret =>
      obtain ⟨hhalt, hpl⟩ := hhmatch
      have hpl' : s'.hReturn.toList = payload := hpl
      refine ⟨by rw [hhalt]; simp, ?_⟩
      rw [State.toResult_returned s' hhalt]
      show ExecutionResult.returned s'.hReturn = .returned (mkCode payload)
      rw [← hpl', mkCode_toList]
    | revert =>
      obtain ⟨hhalt, hpl⟩ := hhmatch
      have hpl' : s'.hReturn.toList = payload := hpl
      refine ⟨by rw [hhalt]; simp, ?_⟩
      rw [State.toResult_reverted s' hhalt]
      show ExecutionResult.reverted s'.hReturn = .reverted (mkCode payload)
      rw [← hpl', mkCode_toList]
    | invalid =>
      have hhalt : s'.halt = .Exception .InvalidInstruction := hhmatch
      exact ⟨by rw [hhalt]; simp, by
        rw [State.toResult_exception s' _ hhalt]; rfl⟩
    | invalidMemoryAccess =>
      have hhalt : s'.halt = .Exception .InvalidMemoryAccess := hhmatch
      exact ⟨by rw [hhalt]; simp, by
        rw [State.toResult_exception s' _ hhalt]; rfl⟩
    | staticViolation =>
      have hhalt : s'.halt = .Exception .StaticModeViolation := hhmatch
      exact ⟨by rw [hhalt]; simp, by
        rw [State.toResult_exception s' _ hhalt]; rfl⟩
    | selfdestruct =>
      obtain ⟨hhalt, -⟩ := hhmatch
      exact ⟨by rw [hhalt]; simp, by
        rw [State.toResult_success s' hhalt]; rfl⟩
  rw [← hdone.2]
  exact Eval.iff_steps_halted.mpr ⟨s', hsteps, hdone.1, hcs', rfl⟩

/-- A source-level digest proof, together with **any** verified backend's
correctness theorem, implies the bytecode challenge statement.

The backend is a parameter because `YulParser.compileSource` — the entry point
that generates the frozen artifact — keeps both the classic and the SSA-CFG
candidate and emits whichever its static cost proxy prefers.  For this
reference source the SSA backend wins, so the frozen bytes are the ones
`SsaCfg.evmBackend` accepts, and the route has to be discharged against that
backend's correctness theorem rather than `compile_correct`. -/
theorem correct_of_computesDigest_of_backend (B : Optimizer.EvmBackend)
    {prog : Block Op} {is : List Instr}
    (hcomp : B.compile prog unpatchedImmutables = some is)
    (hsize : (assemble is).size < 2 ^ 256)
    (habs : AbstractsInitialState (assemble is))
    (hyul : ComputesDigest prog) :
    Correct (assemble is) := by
  intro calldata _hfit
  obtain ⟨yst, hmatch, hmem, hcd, himmutable, hhalted⟩ := habs calldata
  obtain ⟨V, yst', hrun, hres⟩ := hyul yst hmem hhalted
  obtain ⟨b, H⟩ :=
    backend_correct_eval_halt B hcomp
      (by intro key; rw [himmutable]; rfl) hrun
  refine ⟨b, fun g hg => ?_⟩
  obtain ⟨hk, hyk, heval⟩ :=
    H (initialState (assemble is) calldata g) (initialState_frameOK hsize) (hmatch g)
      (initialState_pc _ _ _) (initialState_stack _ _ _) (by rw [initialState_gas]; exact hg)
  rw [hres] at hyk
  cases hyk
  simpa [resultOf, digestOf, hcd, mkCode_toList, spec] using heval

/-- The classic backend's instance of `correct_of_computesDigest_of_backend`. -/
theorem correct_of_computesDigest {prog : Block Op} {is : List Instr}
    (hcomp : compile prog = some is)
    (hsize : (assemble is).size < 2 ^ 256)
    (habs : AbstractsInitialState (assemble is))
    (hyul : ComputesDigest prog) :
    Correct (assemble is) :=
  correct_of_computesDigest_of_backend Optimizer.EvmBackend.classic hcomp hsize habs hyul

end Challenge.Ripemd160
