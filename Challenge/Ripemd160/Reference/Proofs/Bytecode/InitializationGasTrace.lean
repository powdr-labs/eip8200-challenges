import Challenge.EvmProof.Meter
import Challenge.Ripemd160.Reference.Proofs.Bytecode.Main

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Challenge.Ripemd160.Reference.Proofs.Bytecode.InitializationGasTrace

open Challenge.Ripemd160
open EvmSemantics EvmSemantics.EVM

private theorem entry_start_cost (input : ByteArray) :
    (Execution.gasSteps_start input).cost = 11 := by rfl
private theorem entry_1b_cost (input : ByteArray) :
    (Execution.gasSteps_1b input).cost = 12 := by rfl
private theorem entry_2e_cost (input : ByteArray) :
    (Execution.gasSteps_2e input).cost = 12 := by rfl
private theorem entry_46_cost (input : ByteArray) :
    (Execution.gasSteps_46 input).cost = 12 := by rfl
private theorem entry_5a_cost (input : ByteArray) :
    (Execution.gasSteps_5a input).cost = 12 := by rfl
private theorem entry_73_cost (input : ByteArray) :
    (Execution.gasSteps_73 input).cost = 12 := by rfl
private theorem entry_8e_cost (input : ByteArray) :
    (Execution.gasSteps_8e input).cost = 12 := by rfl
private theorem entry_10f_cost (input : ByteArray) :
    (Execution.gasSteps_10f input).cost = 12 := by rfl
private theorem entry_1b2_cost (input : ByteArray) :
    (Execution.gasSteps_1b2 input).cost = 12 := by rfl
private theorem entry_1db_cost (input : ByteArray) :
    (Execution.gasSteps_1db input).cost = 12 := by rfl
private theorem entry_231_cost (input : ByteArray) :
    (Execution.gasSteps_231 input).cost = 12 := by rfl
private theorem entry_268_cost (input : ByteArray) :
    (Execution.gasSteps_268 input).cost = 12 := by rfl
private theorem entry_3c1_cost (input : ByteArray) :
    (Execution.gasSteps_3c1 input).cost = 12 := by rfl
private theorem entry_3ee_cost (input : ByteArray) :
    (Execution.gasSteps_3ee input).cost = 1 := by rfl

theorem entry_cost (input : ByteArray) :
    (Execution.gasSteps_entry input).cost = 156 := by
  unfold Execution.gasSteps_entry
  simp only [Challenge.EvmProof.GasSteps.trans_cost]
  rw [entry_start_cost input, entry_1b_cost input, entry_2e_cost input,
    entry_46_cost input, entry_5a_cost input, entry_73_cost input,
    entry_8e_cost input, entry_10f_cost input, entry_1b2_cost input,
    entry_1db_cost input, entry_231_cost input, entry_268_cost input,
    entry_3c1_cost input, entry_3ee_cost input]

private def initStoreWork (w : Artifact.InitStore) : Nat :=
  Challenge.EvmProof.Meter.instrStaticCost .Osaka
      (.push w.valueWidth w.value) +
    Challenge.EvmProof.Meter.instrStaticCost .Osaka
      (.push w.offsetWidth w.offset) +
    Challenge.EvmProof.Meter.instrStaticCost .Osaka (.op .MSTORE)

private theorem initStore_cost_potential (s : State) (w : Artifact.InitStore)
    (hw : w ∈ Artifact.initStores)
    (hpc : s.pc = UInt256.ofNat (Artifact.instructionPC w.index))
    (hstack : s.stack = [])
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    (Main.gasSteps_initStore s w hw hpc hstack hcode hfork hrun hnp).cost +
        MachineState.memCost s.activeWords.toNat =
      initStoreWork w +
        MachineState.memCost (Main.applyInitStore s w).activeWords.toNat := by
  change Challenge.EvmProof.Stepper.runLocatedBlockCost
      (Main.locatedInitStore w hw) s + MachineState.memCost s.activeWords.toNat = _
  rw [Challenge.EvmProof.Meter.runLocatedBlock_cost_static_potential
    (Main.locatedInitStore w hw)
    (Main.run_initStore s w hw hpc hstack hrun) hfork]
  · simp [Challenge.EvmProof.Meter.runLocatedBlockStaticCost,
      Challenge.EvmProof.Meter.instrStaticCost, Main.locatedInitStore,
      initStoreWork]
    omega
  · intro located hmem q hq
    simp [Main.locatedInitStore] at hmem
    rcases hmem with rfl | rfl | rfl <;>
      simp [Challenge.EvmProof.Meter.instrCostWithoutMemory,
        Challenge.EvmProof.Meter.instrStaticCost, hq]

private theorem initStores_cost_potential (s : State)
    (ws : List Artifact.InitStore)
    (hmem : ∀ w, w ∈ ws → w ∈ Artifact.initStores)
    (hchain : Main.InitChain ws)
    (hpc : ∀ w, ws.head? = some w →
      s.pc = UInt256.ofNat (Artifact.instructionPC w.index))
    (hstack : s.stack = [])
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    (Main.gasSteps_initStores s ws hmem hchain hpc hstack hcode hfork hrun hnp).cost +
        MachineState.memCost s.activeWords.toNat =
      (ws.map initStoreWork).sum +
        MachineState.memCost (ws.foldl Main.applyInitStore s).activeWords.toNat := by
  induction ws generalizing s with
  | nil => simp [Main.gasSteps_initStores]
  | cons w tail ih =>
      cases tail with
      | nil =>
          have hw : w ∈ Artifact.initStores := hmem w (by simp)
          have hpcw : s.pc = UInt256.ofNat (Artifact.instructionPC w.index) :=
            hpc w (by simp)
          have hone := initStore_cost_potential s w hw hpcw hstack hcode hfork
            hrun hnp
          simpa [Main.gasSteps_initStores] using hone
      | cons next rest =>
          have hw : w ∈ Artifact.initStores := hmem w (by simp)
          have hpcw : s.pc = UInt256.ofNat (Artifact.instructionPC w.index) :=
            hpc w (by simp)
          have hnext : next.index = w.index + 3 := hchain.1
          have htail : Main.InitChain (next :: rest) := hchain.2
          have hfirst := initStore_cost_potential s w hw hpcw hstack hcode hfork
            hrun hnp
          have hrest := ih (s := Main.applyInitStore s w)
            (fun x hx => hmem x (List.mem_cons_of_mem w hx)) htail
            (fun x hx => by
              simp only [List.head?_cons, Option.some.injEq] at hx
              subst x
              simp [Main.applyInitStore, hnext])
            (by simp [Main.applyInitStore])
            (by simpa [Main.applyInitStore] using hcode)
            (by simpa [Main.applyInitStore] using hfork)
            (by simpa [Main.applyInitStore] using hrun)
            (by simpa [Main.applyInitStore] using hnp)
          simp only [List.map_cons, List.sum_cons, List.foldl_cons] at hrest
          simp only [Main.gasSteps_initStores,
            Challenge.EvmProof.GasSteps.cast_cost,
            Challenge.EvmProof.GasSteps.trans_cost, List.map_cons,
            List.sum_cons, List.foldl_cons]
          omega

theorem bodyInitialization_cost_potential (input : ByteArray) :
    (Main.gasSteps_bodyInitialization input).cost +
        MachineState.memCost (Execution.mainStart input).activeWords.toNat =
      241 + MachineState.memCost (Main.initializedState input).activeWords.toNat := by
  have h := initStores_cost_potential (Execution.mainStart input)
    Artifact.initStores (fun _ hw => hw)
    (by norm_num [Main.InitChain, Artifact.initStores])
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
  have hwork : (Artifact.initStores.map initStoreWork).sum = 241 := by
    norm_num [Artifact.initStores, initStoreWork,
      Challenge.EvmProof.Meter.instrStaticCost, Gas.baseCost]
  rw [hwork] at h
  unfold Main.gasSteps_bodyInitialization
  rw [Challenge.EvmProof.GasSteps.cast_cost]
  change _ = 241 + MachineState.memCost
    (Artifact.initStores.foldl Main.applyInitStore
      (Execution.mainStart input)).activeWords.toNat
  convert h using 1

theorem initialize_cost_of_active (input : ByteArray)
    (hactive : (Main.initializedState input).activeWords.toNat = 59) :
    (Main.gasSteps_initialize input).cost = 580 := by
  have hbody := bodyInitialization_cost_potential input
  rw [hactive] at hbody
  norm_num [MachineState.memCost, Execution.mainStart, Execution.atPC,
    initialState] at hbody
  unfold Main.gasSteps_initialize
  rw [Challenge.EvmProof.GasSteps.trans_cost, entry_cost input]
  omega

end Challenge.Ripemd160.Reference.Proofs.Bytecode.InitializationGasTrace
