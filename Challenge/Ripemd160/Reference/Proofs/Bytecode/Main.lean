import Challenge.Ripemd160.Reference.Proofs.Bytecode.Execution
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
/-!
# Direct execution of the RIPEMD-160 main-body initialization

The compiler emits 27 consecutive `PUSH; PUSH; MSTORE` triples.  A located
path certifies those exact instructions against the frozen artifact; it also
handles the two `PUSH0` values without a special semantic assumption.
-/

namespace Challenge.Ripemd160.Reference.Proofs.Bytecode.Main

open EvmSemantics
open EvmSemantics.EVM

private def wfOp {op : Operation}
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op)
    (hplain : YulEvmCompiler.plainOp op)
    (havailable : op.availableInFork .Osaka = true) :
    Challenge.EvmProof.Stepper.WellFormed .Osaka (.op op) :=
  ⟨hopcode, hplain, havailable⟩

/-- Exact state transformer for one initialization store. -/
def applyInitStore (s : State) (w : Artifact.InitStore) : State :=
  { s with
    pc := UInt256.ofNat (Artifact.instructionPC (w.index + 3))
    stack := []
    memory := MachineState.writeBytes s.memory
      (Data.Bytes.natToBytesPadded w.value.toNat 32) w.offset.toNat
    activeWords := s.activeWordsAfterUInt256 w.offset.toNat 32 }

private theorem valueFits (w : Artifact.InitStore)
    (hw : w ∈ Artifact.initStores) :
    w.value.toNat < 256 ^ w.valueWidth.val := by
  simp only [Artifact.initStores, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

private theorem offsetFits (w : Artifact.InitStore)
    (hw : w ∈ Artifact.initStores) :
    w.offset.toNat < 256 ^ w.offsetWidth.val := by
  simp only [Artifact.initStores, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

private theorem pushAvailable (width : Fin 33) :
    (Operation.Push ⟨width⟩).availableInFork .Osaka = true := by
  change (if width.val = 0 then decide (.Osaka ≥ Fork.Shanghai) else true) = true
  by_cases h : width.val = 0
  · rw [if_pos h]
    decide
  · rw [if_neg h]

@[simp] private theorem pushZeroWord :
    (⟨0⟩ : UInt256) = UInt256.ofNat 0 := rfl

@[simp] private theorem toNatZero : (0 : UInt256).toNat = 0 := rfl

/-- The three certified instruction locations for one table/state store. -/
def locatedInitStore (w : Artifact.InitStore) (hw : w ∈ Artifact.initStores) :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  let hv := Artifact.initStore_valid w hw
  [⟨w.index, .push w.valueWidth w.value, hv.1,
      ⟨valueFits w hw, pushAvailable w.valueWidth⟩⟩,
   ⟨w.index + 1, .push w.offsetWidth w.offset, hv.2.2.1,
      ⟨offsetFits w hw, pushAvailable w.offsetWidth⟩⟩,
   ⟨w.index + 2, .op .MSTORE, hv.2.2.2.2.1,
      wfOp (by decide) trivial rfl⟩]

def initializedState (input : ByteArray) : State :=
  Artifact.initStores.foldl applyInitStore (Execution.mainStart input)

@[simp] theorem initializedState_pc (input : ByteArray) :
    (initializedState input).pc = UInt256.ofNat (Artifact.instructionPC 764) := by
  rfl

@[simp] theorem initializedState_stack (input : ByteArray) :
    (initializedState input).stack = [] := by rfl

@[simp] theorem initializedState_halt (input : ByteArray) :
    (initializedState input).halt = .Running := by rfl

@[simp] theorem initializedState_fork (input : ByteArray) :
    (initializedState input).fork = .Osaka := by rfl

@[simp] theorem initializedState_code (input : ByteArray) :
    (initializedState input).executionEnv.code = referenceBytecode := by rfl

@[simp] theorem initializedState_codeAddr (input : ByteArray) :
    (initializedState input).executionEnv.codeAddr = deployAddress := by rfl

theorem run_initStore (s : State) (w : Artifact.InitStore)
    (hw : w ∈ Artifact.initStores)
    (hpc : s.pc = UInt256.ofNat (Artifact.instructionPC w.index))
    (hstack : s.stack = [])
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock (locatedInitStore w hw) s =
      some (applyInitStore s w) := by
  simp only [Artifact.initStores, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp (config := { maxSteps := 200000 })
      [locatedInitStore, applyInitStore, hpc, hstack, hrun,
        Artifact.instructionPC,
        Challenge.EvmProof.Stepper.runLocatedBlock,
        Challenge.EvmProof.Stepper.runLocated,
        Challenge.EvmProof.Stepper.runInstr,
        State.activeWordsAfterUInt256, pushZeroWord,
        Challenge.EvmProof.Word.word_toNat_ofNat]

def gasSteps_initStore (s : State) (w : Artifact.InitStore)
    (hw : w ∈ Artifact.initStores)
    (hpc : s.pc = UInt256.ofNat (Artifact.instructionPC w.index))
    (hstack : s.stack = [])
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps s (applyInitStore s w) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka (locatedInitStore w hw)
  · simpa [Artifact.referenceArtifact] using hcode
  · exact hfork
  · exact run_initStore s w hw hpc hstack hrun
  · exact hrun
  · exact hnp

def InitChain : List Artifact.InitStore → Prop
  | [] | [_] => True
  | a :: b :: rest => b.index = a.index + 3 ∧ InitChain (b :: rest)

def gasSteps_initStores (s : State) :
    (ws : List Artifact.InitStore) →
    (∀ w, w ∈ ws → w ∈ Artifact.initStores) →
    InitChain ws →
    (∀ w, ws.head? = some w →
      s.pc = UInt256.ofNat (Artifact.instructionPC w.index)) →
    s.stack = [] →
    s.executionEnv.code = referenceBytecode →
    s.fork = .Osaka →
    s.halt = .Running →
    Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false →
    Challenge.EvmProof.GasSteps s (ws.foldl applyInitStore s)
  | [], _, _, _, _, _, _, _, _ => Challenge.EvmProof.GasSteps.refl s
  | [w], hmem, _, hpc, hstack, hcode, hfork, hrun, hnp => by
      have hw : w ∈ Artifact.initStores := hmem w (by simp)
      have hpcw : s.pc = UInt256.ofNat (Artifact.instructionPC w.index) :=
        hpc w (by simp)
      have gone := gasSteps_initStore s w hw hpcw hstack hcode hfork hrun hnp
      exact Challenge.EvmProof.GasSteps.cast gone rfl (by simp)
  | w :: next :: rest, hmem, hchain, hpc, hstack, hcode, hfork, hrun, hnp => by
      have hw : w ∈ Artifact.initStores := hmem w (by simp)
      have hpcw : s.pc = UInt256.ofNat (Artifact.instructionPC w.index) :=
        hpc w (by simp)
      have gone := gasSteps_initStore s w hw hpcw hstack hcode hfork hrun hnp
      have hnext : next.index = w.index + 3 := hchain.1
      have htail : InitChain (next :: rest) := hchain.2
      have grest := gasSteps_initStores (applyInitStore s w) (next :: rest)
        (fun x hx => hmem x (List.mem_cons_of_mem w hx)) htail
        (fun x hx => by
          simp only [List.head?_cons, Option.some.injEq] at hx
          subst x
          simp [applyInitStore, hnext])
        (by simp [applyInitStore])
        (by simpa [applyInitStore] using hcode)
        (by simpa [applyInitStore] using hfork)
        (by simpa [applyInitStore] using hrun)
        (by simpa [applyInitStore] using hnp)
      exact Challenge.EvmProof.GasSteps.cast (gone.trans grest) rfl
        (by simp [List.foldl])

def gasSteps_bodyInitialization (input : ByteArray) :
    Challenge.EvmProof.GasSteps (Execution.mainStart input)
      (initializedState input) := by
  have body := gasSteps_initStores (Execution.mainStart input)
    Artifact.initStores (fun _ h => h)
    (by norm_num [InitChain, Artifact.initStores])
    (by
      intro w hw
      simp only [Artifact.initStores, List.head?_cons, Option.some.injEq] at hw
      subst w
      rfl)
    (by simp [Execution.mainStart, Execution.atPC, initialState])
    (by simp [Execution.mainStart, Execution.atPC, initialState])
    (by simp [Execution.mainStart, Execution.atPC, initialState])
    (by simp [Execution.mainStart, Execution.atPC, initialState])
    (by simp [Execution.mainStart, Execution.atPC, initialState,
      deployAddress_not_precompile])
  exact Challenge.EvmProof.GasSteps.cast body rfl
    (by simp [initializedState])

def gasSteps_initialize (input : ByteArray) :
    Challenge.EvmProof.GasSteps (initialState referenceBytecode input 0)
      (initializedState input) :=
  (Execution.gasSteps_entry input).trans (gasSteps_bodyInitialization input)

end Challenge.Ripemd160.Reference.Proofs.Bytecode.Main
