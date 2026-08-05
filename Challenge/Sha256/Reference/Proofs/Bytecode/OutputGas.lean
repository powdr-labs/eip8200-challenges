import Challenge.EvmProof.Meter
import Challenge.Sha256.Reference.Proofs.Bytecode.Output

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Challenge.Sha256.Reference.Proofs.Bytecode.OutputGas

open Challenge.Sha256
open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler

private def osakaBaseCost : Instr → Nat
  | .push width _ => Gas.baseCost .Osaka (.Push ⟨width⟩)
  | .op op => Gas.baseCost .Osaka op

private def pathBaseCost {artifact : Challenge.EvmProof.ProgramArtifact}
    (path : List (Challenge.EvmProof.Stepper.Located artifact .Osaka)) : Nat :=
  (path.map (fun located => osakaBaseCost located.instruction)).sum


private def CopyFree : Instr → Prop
  | .op .CALLDATACOPY => False
  | .op .MCOPY => False
  | _ => True

private theorem noMemoryCost_eq_base (instruction : Instr) (s : State)
    (hfork : s.fork = .Osaka) (hfree : CopyFree instruction) :
    Challenge.EvmProof.Meter.instrCostWithoutMemory instruction s =
      osakaBaseCost instruction := by
  cases instruction with
  | push width value => simp [Challenge.EvmProof.Meter.instrCostWithoutMemory,
      osakaBaseCost, hfork]
  | op op =>
      cases op with
      | StopArith op => cases op <;> simp [Challenge.EvmProof.Meter.instrCostWithoutMemory,
          osakaBaseCost, hfork]
      | CompBit op => cases op <;> simp [Challenge.EvmProof.Meter.instrCostWithoutMemory,
          osakaBaseCost, hfork]
      | Keccak op => cases op; simp [Challenge.EvmProof.Meter.instrCostWithoutMemory,
          osakaBaseCost, hfork]
      | Env op => cases op <;> simp [CopyFree,
          Challenge.EvmProof.Meter.instrCostWithoutMemory,
          osakaBaseCost, hfork] at hfree ⊢
      | Block op => cases op <;> simp [Challenge.EvmProof.Meter.instrCostWithoutMemory,
          osakaBaseCost, hfork]
      | StackMemFlow op => cases op <;> simp [CopyFree,
          Challenge.EvmProof.Meter.instrCostWithoutMemory,
          osakaBaseCost, hfork] at hfree ⊢
      | Push op => cases op; simp [Challenge.EvmProof.Meter.instrCostWithoutMemory,
          osakaBaseCost, hfork]
      | Dup op => cases op; simp [Challenge.EvmProof.Meter.instrCostWithoutMemory,
          osakaBaseCost, hfork]
      | Swap op => cases op; simp [Challenge.EvmProof.Meter.instrCostWithoutMemory,
          osakaBaseCost, hfork]
      | DupN op => cases op; simp [Challenge.EvmProof.Meter.instrCostWithoutMemory,
          osakaBaseCost, hfork]
      | SwapN op => cases op; simp [Challenge.EvmProof.Meter.instrCostWithoutMemory,
          osakaBaseCost, hfork]
      | Exchange op => cases op; simp [Challenge.EvmProof.Meter.instrCostWithoutMemory,
          osakaBaseCost, hfork]
      | Log op => cases op; simp [Challenge.EvmProof.Meter.instrCostWithoutMemory,
          osakaBaseCost, hfork]
      | System op => cases op <;> simp [Challenge.EvmProof.Meter.instrCostWithoutMemory,
          osakaBaseCost, hfork]

private theorem blockWork_eq_base
    {artifact : Challenge.EvmProof.ProgramArtifact}
    (path : List (Challenge.EvmProof.Stepper.Located artifact .Osaka))
    {s t : State}
    (hresult : Challenge.EvmProof.Stepper.runLocatedBlock path s = some t)
    (hfork : s.fork = .Osaka)
    (hfree : ∀ located ∈ path, CopyFree located.instruction) :
    Challenge.EvmProof.Meter.runLocatedBlockCostWithoutMemory path s =
      pathBaseCost path := by
  induction path generalizing s t with
  | nil => rfl
  | cons located rest ih =>
      have hhead := hfree located (by simp)
      cases rest with
      | nil =>
          change Challenge.EvmProof.Meter.instrCostWithoutMemory
              located.instruction s = pathBaseCost [located]
          rw [noMemoryCost_eq_base located.instruction s hfork hhead]
          rfl
      | cons nextLocated tail =>
          change Challenge.EvmProof.Meter.instrCostWithoutMemory
              located.instruction s +
              (match Challenge.EvmProof.Stepper.runLocated located s with
              | some next =>
                  match next.halt with
                  | .Running =>
                      Challenge.EvmProof.Meter.runLocatedBlockCostWithoutMemory
                        (nextLocated :: tail) next
                  | _ => 0
              | none => 0) = pathBaseCost (located :: nextLocated :: tail)
          rw [noMemoryCost_eq_base located.instruction s hfork hhead]
          cases hnext : Challenge.EvmProof.Stepper.runLocated located s with
          | none =>
              simp [Challenge.EvmProof.Stepper.runLocatedBlock, hnext] at hresult
          | some next =>
              cases hrun : next.halt with
              | Running =>
                  simp [Challenge.EvmProof.Stepper.runLocatedBlock, hnext, hrun]
                    at hresult
                  have henv := Challenge.EvmProof.Stepper.runLocated_executionEnv hnext
                  have hnextFork : next.fork = .Osaka := by
                    change next.executionEnv.fork = .Osaka
                    rw [henv]
                    exact hfork
                  simp only [hrun]
                  rw [ih hresult hnextFork (by
                    intro item hmem
                    exact hfree item (by simp [hmem]))]
                  simp [pathBaseCost]
              | Success =>
                  simp [Challenge.EvmProof.Stepper.runLocatedBlock, hnext, hrun]
                    at hresult
              | Returned =>
                  simp [Challenge.EvmProof.Stepper.runLocatedBlock, hnext, hrun]
                    at hresult
              | Reverted =>
                  simp [Challenge.EvmProof.Stepper.runLocatedBlock, hnext, hrun]
                    at hresult
              | Exception error =>
                  simp [Challenge.EvmProof.Stepper.runLocatedBlock, hnext, hrun]
                    at hresult

private theorem blockCost_potential_base
    {artifact : Challenge.EvmProof.ProgramArtifact}
    (path : List (Challenge.EvmProof.Stepper.Located artifact .Osaka))
    {s t : State}
    (hresult : Challenge.EvmProof.Stepper.runLocatedBlock path s = some t)
    (hfork : s.fork = .Osaka)
    (hfree : ∀ located ∈ path, CopyFree located.instruction) :
    Challenge.EvmProof.Stepper.runLocatedBlockCost path s +
        MachineState.memCost s.activeWords.toNat =
      pathBaseCost path +
        MachineState.memCost t.activeWords.toNat := by
  rw [Challenge.EvmProof.Meter.runLocatedBlock_cost_potential path hresult,
    blockWork_eq_base path hresult hfork hfree]


private theorem activeWordsAfter_eq_of_end_le (curr offset size : Nat)
    (hend : offset + size ≤ curr * 32) :
    MachineState.activeWordsAfter curr offset size = curr := by
  unfold MachineState.activeWordsAfter
  split
  · rfl
  · apply Nat.max_eq_left
    have hcurr : 0 < curr := by omega
    have hdiv : (offset + size - 1) / 32 < curr := by
      rw [Nat.div_lt_iff_lt_mul (by omega)]
      omega
    omega

private theorem ofNat_toNat (w : UInt256) : UInt256.ofNat w.toNat = w := by
  cases w with
  | mk val => simp [UInt256.ofNat, UInt256.toNat, UInt256.size]

private theorem activeWordsAfterUInt256_eq (s : State) (offset size : Nat)
    (hend : offset + size ≤ s.activeWords.toNat * 32) :
    s.activeWordsAfterUInt256 offset size = s.activeWords := by
  rw [State.activeWordsAfterUInt256,
    activeWordsAfter_eq_of_end_le _ _ _ hend, ofNat_toNat]


/-! The output block is one straight run now, so the per-path base costs and the
ten cost-potential theorems that chained them are gone.  `pathBaseCost` of the
whole block is 125. -/

private theorem output_base : pathBaseCost Output.outputPath = 125 := by rfl

private theorem output_copyFree :
    ∀ located ∈ Output.outputPath, CopyFree located.instruction := by
  intro located hlocated
  simp only [Output.outputPath, List.mem_cons, List.not_mem_nil, or_false]
    at hlocated
  rcases hlocated with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    trivial

theorem gasSteps_output_cost_potential (s : State)
    (counter padded : UInt256) (rest : List UInt256) (hcap : rest.length < 1016)
    (hcode : (Output.outputEntry s counter padded rest).executionEnv.code =
      referenceBytecode)
    (hfork : (Output.outputEntry s counter padded rest).fork = .Osaka)
    (hrun : s.halt = .Running)
    (hhalt : (Output.outputEntry s counter padded rest).halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig
      (Output.outputEntry s counter padded rest).executionEnv.precompileConfig
      (Output.outputEntry s counter padded rest).executionEnv.fork
      (Output.outputEntry s counter padded rest).executionEnv.codeAddr = false) :
    (Output.gasSteps_output s counter padded rest hcap hcode hfork hrun hhalt
          hnp).cost +
        MachineState.memCost s.activeWords.toNat =
      125 + MachineState.memCost (Output.outputResult s rest).activeWords.toNat := by
  have h := blockCost_potential_base Output.outputPath
    (Output.run_output s counter padded rest hcap hrun) hfork output_copyFree
  rw [output_base] at h
  simpa [Output.gasSteps_output,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost,
    Output.outputEntry] using h

/-- Every slot the block touches lies below `0x220`, so once memory is already 17
words wide the block expands nothing. -/
theorem outputResult_activeWords_of_ge (s : State) (rest : List UInt256)
    (haw : 17 ≤ s.activeWords.toNat) :
    (Output.outputResult s rest).activeWords = s.activeWords := by
  have step : ∀ (q : State) (o : Nat), q.activeWords = s.activeWords →
      o + 32 ≤ 544 → q.activeWordsAfterUInt256 o 32 = s.activeWords := by
    intro q o hq hle
    rw [activeWordsAfterUInt256_eq q o 32 (by rw [hq]; omega), hq]
  have h7 : (Output.afterLoad s 7).activeWords = s.activeWords :=
    step s (Output.hOffset 7) rfl (by simp [Output.hOffset])
  have h6 : (Output.afterLoad (Output.afterLoad s 7) 6).activeWords =
      s.activeWords :=
    step _ (Output.hOffset 6) h7 (by simp [Output.hOffset])
  have h5 : (Output.afterLoad (Output.afterLoad (Output.afterLoad s 7) 6)
      5).activeWords = s.activeWords :=
    step _ (Output.hOffset 5) h6 (by simp [Output.hOffset])
  have h4 : (Output.afterLoad (Output.afterLoad (Output.afterLoad
      (Output.afterLoad s 7) 6) 5) 4).activeWords = s.activeWords :=
    step _ (Output.hOffset 4) h5 (by simp [Output.hOffset])
  have h3 : (Output.afterLoad (Output.afterLoad (Output.afterLoad
      (Output.afterLoad (Output.afterLoad s 7) 6) 5) 4) 3).activeWords =
      s.activeWords :=
    step _ (Output.hOffset 3) h4 (by simp [Output.hOffset])
  have h2 : (Output.afterLoad (Output.afterLoad (Output.afterLoad
      (Output.afterLoad (Output.afterLoad (Output.afterLoad s 7) 6) 5) 4) 3)
      2).activeWords = s.activeWords :=
    step _ (Output.hOffset 2) h3 (by simp [Output.hOffset])
  have h1 : (Output.afterLoad (Output.afterLoad (Output.afterLoad
      (Output.afterLoad (Output.afterLoad (Output.afterLoad (Output.afterLoad
      s 7) 6) 5) 4) 3) 2) 1).activeWords = s.activeWords :=
    step _ (Output.hOffset 1) h2 (by simp [Output.hOffset])
  have hloads : (Output.afterLoads s).activeWords = s.activeWords := by
    change (Output.afterLoad _ 0).activeWords = s.activeWords
    exact step _ (Output.hOffset 0) h1 (by simp [Output.hOffset])
  have hstore : (Output.afterStore s).activeWords = s.activeWords := by
    change (Output.afterLoads s).activeWordsAfterUInt256 0 32 = s.activeWords
    exact step _ 0 hloads (by omega)
  change Output.outputActiveWords s = s.activeWords
  change (Output.afterStore s).activeWordsAfterUInt256 0 32 = s.activeWords
  exact step _ 0 hstore (by omega)

theorem gasSteps_output_cost_of_activeWords_ge (s : State)
    (counter padded : UInt256) (rest : List UInt256) (hcap : rest.length < 1016)
    (hcode : (Output.outputEntry s counter padded rest).executionEnv.code =
      referenceBytecode)
    (hfork : (Output.outputEntry s counter padded rest).fork = .Osaka)
    (hrun : s.halt = .Running)
    (hhalt : (Output.outputEntry s counter padded rest).halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig
      (Output.outputEntry s counter padded rest).executionEnv.precompileConfig
      (Output.outputEntry s counter padded rest).executionEnv.fork
      (Output.outputEntry s counter padded rest).executionEnv.codeAddr = false)
    (haw : 17 ≤ s.activeWords.toNat) :
    (Output.gasSteps_output s counter padded rest hcap hcode hfork hrun hhalt
      hnp).cost = 125 := by
  have hpotential := gasSteps_output_cost_potential s counter padded rest hcap
    hcode hfork hrun hhalt hnp
  rw [outputResult_activeWords_of_ge s rest haw] at hpotential
  omega

end Challenge.Sha256.Reference.Proofs.Bytecode.OutputGas
