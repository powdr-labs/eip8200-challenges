import Challenge.Ripemd160.ProofSupport.InitialState
import YulEvmCompiler.ContractCorrectness

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
open YulSemantics (Block RunContract VEnv)
open YulSemantics.EVM
  (EvmState Op evmWithExternal ExternalCalls ExternalCreates ExternalGas)
open YulEvmCompiler

/-- The RIPEMD-160 precompile result at the byte-list view used by Yul
semantics. -/
def digestOf (calldata : List UInt8) : List UInt8 :=
  (spec (mkCode calldata)).toList

/-- The reference implementation neither calls contracts nor creates them. -/
@[reducible] def localModel : ExternalModel :=
  { calls := ExternalCalls.none, creates := ExternalCreates.none, gas := ExternalGas.none }

/-- The gas-free source dialect used by the functional obligation. -/
abbrev localDialect := evmWithExternal ExternalCalls.none ExternalCreates.none
  YulSemantics.EVM.ExternalGas.none

/-- Executable built-in function for the fully closed compiler source dialect. The only
non-`stepOp` results that remain possible are the deterministic static-context violations imposed
before an unavailable call or creation is consulted. -/
def localBuiltinFn (op : Op) (args : List YulSemantics.EVM.U256) (st : EvmState) :
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

/-- Executable presentation of the fully closed compiler source dialect. -/
@[reducible] def localExec : YulSemantics.ExecDialect :=
  { toDialect := localDialect, builtinFn := localBuiltinFn }

/-- The closed presentation is lawful: calls, creations, and `gas()` are impossible on both sides,
while every local operation is exactly `stepOp`. -/
theorem localExec_lawful : localExec.Lawful := by
  intro op args st result
  cases op <;>
    simp [localExec, localDialect, evmWithExternal,
      localBuiltinFn,
      YulSemantics.EVM.builtinWithExternal, YulSemantics.EVM.externalCall,
      YulSemantics.EVM.externalCreate, ExternalCalls.none, ExternalCreates.none,
      ExternalGas.none, YulSemantics.EVM.stepOp]
  all_goals
    rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, _ | ⟨f, _ | ⟨g, args⟩⟩⟩⟩⟩⟩⟩ <;>
      simp <;> try split <;> simp_all
  all_goals
    intros
    constructor <;> intro h <;> exact h.symm

/-- The fully closed external model has no realizability obligations. -/
theorem localExternalsRealized : ExternalsRealized localModel :=
  ⟨CallsRealized.none, CreatesRealized.none, GasCallsRealized.noneOracle _⟩

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

/-- From any fresh source state with realizable calldata, the program returns the 32-byte,
left-padded Ethereum RIPEMD-160 precompile result. This proof-facing contract deliberately retains
only the halt observation, not the constructed final memory or variable environment. -/
def ComputesDigest (prog : Block Op) : Prop :=
  RunContract (D := localDialect) prog
    (fun yst => yst.memory = (fun _ => 0) ∧ yst.halted = none ∧
      ∃ input : ByteArray, yst.env.calldata = input.toList ∧ CalldataFits input)
    (fun yst _ yst' outcome => outcome = .halt ∧
      yst'.halted = some (.ret, digestOf yst.env.calldata))

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
  simpa [resultOf, digestOf, hcd, mkCode_toList, spec] using heval

end Challenge.Ripemd160
