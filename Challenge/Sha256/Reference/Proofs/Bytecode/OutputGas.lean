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

private theorem start_base : pathBaseCost Output.startPath = 22 := by rfl
private theorem hAt_base : pathBaseCost Accessors.hAtPath = 37 := by rfl
private theorem setup6_base : pathBaseCost Output.setup6Path = 20 := by rfl
private theorem setup5_base : pathBaseCost Output.setup5Path = 29 := by rfl
private theorem setup4_base : pathBaseCost Output.setup4Path = 26 := by rfl
private theorem setup3_base : pathBaseCost Output.setup3Path = 32 := by rfl
private theorem setup2_base : pathBaseCost Output.setup2Path = 26 := by rfl
private theorem setup1_base : pathBaseCost Output.setup1Path = 29 := by rfl
private theorem setup0_base : pathBaseCost Output.setup0Path = 25 := by rfl
private theorem finish_base : pathBaseCost Output.finishPath = 26 := by rfl

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

theorem hAt_cost_potential (s : State) (index output returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1018)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hvalid : Decode.isValidJumpDest referenceBytecode returnDest.toNat = true) :
    (Accessors.gasSteps_hAt s index output returnDest rest hcap hcode hfork
      hrun hnp hvalid).cost + MachineState.memCost s.activeWords.toNat =
      37 + MachineState.memCost
        (Accessors.loadReturned s 288 index returnDest rest).activeWords.toNat := by
  have hresult := Accessors.run_load Accessors.hAtPath s 318 288
    index output returnDest rest (Or.inr ⟨rfl, rfl, rfl⟩) hcap hcode hrun hvalid
  have hmeter := blockCost_potential_base Accessors.hAtPath hresult hfork
    (by simp [Accessors.hAtPath, CopyFree])
  rw [hAt_base] at hmeter
  unfold Accessors.gasSteps_hAt
  simp only [Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost]
  simpa [Accessors.loadEntry, pathBaseCost] using hmeter

theorem start_cost_potential (s : State) (offset : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1019)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlockCost Output.startPath
        (Output.outputEntry s offset rest) + MachineState.memCost s.activeWords.toNat =
      22 + MachineState.memCost
        (Accessors.loadEntry s 318 (UInt256.ofNat 7) ⟨0⟩
          (UInt256.ofNat 1413) rest).activeWords.toNat := by
  have hresult := Output.run_start s offset rest hcap hcode hrun
  have hmeter := blockCost_potential_base Output.startPath hresult hfork
    (by simp [Output.startPath, CopyFree])
  rw [start_base] at hmeter
  simpa [Output.outputEntry, Accessors.loadEntry, pathBaseCost] using hmeter

private theorem setup6_cost_potential (s : State) (h7 : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1018)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlockCost Output.setup6Path
        { s with pc := UInt256.ofNat 1413, stack := h7 :: rest } +
        MachineState.memCost s.activeWords.toNat =
      20 + MachineState.memCost
        (Accessors.loadEntry s 318 (UInt256.ofNat 6) ⟨0⟩
          (UInt256.ofNat 1424) (h7 :: rest)).activeWords.toNat := by
  have hresult := Output.run_setup6 s h7 rest hcap hcode hrun
  have hmeter := blockCost_potential_base Output.setup6Path hresult hfork
    (by simp [Output.setup6Path, CopyFree])
  rw [setup6_base] at hmeter
  simpa [Accessors.loadEntry, pathBaseCost] using hmeter

private theorem setup5_cost_potential (s : State) (h6 h7 : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1017)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlockCost Output.setup5Path
        { s with pc := UInt256.ofNat 1424, stack := h6 :: h7 :: rest } +
        MachineState.memCost s.activeWords.toNat =
      29 + MachineState.memCost
        (Accessors.loadEntry s 318 (UInt256.ofNat 5) ⟨0⟩
          (UInt256.ofNat 1439)
          (UInt256.lor (UInt256.shiftLeft h6 (UInt256.ofNat 32)) h7 :: rest)
        ).activeWords.toNat := by
  have hresult := Output.run_setup5 s h6 h7 rest hcap hcode hrun
  have hmeter := blockCost_potential_base Output.setup5Path hresult hfork
    (by simp [Output.setup5Path, CopyFree])
  rw [setup5_base] at hmeter
  simpa [Accessors.loadEntry, pathBaseCost] using hmeter

private theorem setup4_cost_potential (s : State) (h5 packed67 : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1017)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlockCost Output.setup4Path
        { s with pc := UInt256.ofNat 1439, stack := h5 :: packed67 :: rest } +
        MachineState.memCost s.activeWords.toNat =
      26 + MachineState.memCost
        (Accessors.loadEntry s 318 (UInt256.ofNat 4) ⟨0⟩
          (UInt256.ofNat 1453)
          (UInt256.shiftLeft h5 (UInt256.ofNat 64) :: packed67 :: rest)
        ).activeWords.toNat := by
  have hresult := Output.run_setup4 s h5 packed67 rest hcap hcode hrun
  have hmeter := blockCost_potential_base Output.setup4Path hresult hfork
    (by simp [Output.setup4Path, CopyFree])
  rw [setup4_base] at hmeter
  simpa [Accessors.loadEntry, pathBaseCost] using hmeter

private theorem setup3_cost_potential (s : State)
    (h4 shifted5 packed67 : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1016)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running) :
    let packed := UInt256.lor
      (UInt256.lor (UInt256.shiftLeft h4 (UInt256.ofNat 96)) shifted5) packed67
    Challenge.EvmProof.Stepper.runLocatedBlockCost Output.setup3Path
        ({ s with
          pc := UInt256.ofNat 1453
          stack := h4 :: shifted5 :: packed67 :: rest }) +
        MachineState.memCost s.activeWords.toNat =
      32 + MachineState.memCost
        (Accessors.loadEntry s 318 (UInt256.ofNat 3) ⟨0⟩
          (UInt256.ofNat 1469) (packed :: rest)).activeWords.toNat := by
  dsimp only
  have hresult := Output.run_setup3 s h4 shifted5 packed67 rest hcap hcode hrun
  have hmeter := blockCost_potential_base Output.setup3Path hresult hfork
    (by simp [Output.setup3Path, CopyFree])
  rw [setup3_base] at hmeter
  simpa [Accessors.loadEntry, pathBaseCost] using hmeter

private theorem setup2_cost_potential (s : State) (h3 packedLow : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1017)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlockCost Output.setup2Path
        { s with pc := UInt256.ofNat 1469, stack := h3 :: packedLow :: rest } +
        MachineState.memCost s.activeWords.toNat =
      26 + MachineState.memCost
        (Accessors.loadEntry s 318 (UInt256.ofNat 2) ⟨0⟩
          (UInt256.ofNat 1483)
          (UInt256.shiftLeft h3 (UInt256.ofNat 128) :: packedLow :: rest)
        ).activeWords.toNat := by
  have hresult := Output.run_setup2 s h3 packedLow rest hcap hcode hrun
  have hmeter := blockCost_potential_base Output.setup2Path hresult hfork
    (by simp [Output.setup2Path, CopyFree])
  rw [setup2_base] at hmeter
  simpa [Accessors.loadEntry, pathBaseCost] using hmeter

private theorem setup1_cost_potential (s : State)
    (h2 shifted3 packedLow : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1016)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running) :
    let packed := UInt256.lor
      (UInt256.shiftLeft h2 (UInt256.ofNat 160)) shifted3
    Challenge.EvmProof.Stepper.runLocatedBlockCost Output.setup1Path
        ({ s with
          pc := UInt256.ofNat 1483
          stack := h2 :: shifted3 :: packedLow :: rest }) +
        MachineState.memCost s.activeWords.toNat =
      29 + MachineState.memCost
        (Accessors.loadEntry s 318 (UInt256.ofNat 1) ⟨0⟩
          (UInt256.ofNat 1498) (packed :: packedLow :: rest)).activeWords.toNat := by
  dsimp only
  have hresult := Output.run_setup1 s h2 shifted3 packedLow rest hcap hcode hrun
  have hmeter := blockCost_potential_base Output.setup1Path hresult hfork
    (by simp [Output.setup1Path, CopyFree])
  rw [setup1_base] at hmeter
  simpa [Accessors.loadEntry, pathBaseCost] using hmeter

private theorem setup0_cost_potential (s : State)
    (h1 packed23 packedLow : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1016)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlockCost Output.setup0Path
        ({ s with
          pc := UInt256.ofNat 1498
          stack := h1 :: packed23 :: packedLow :: rest }) +
        MachineState.memCost s.activeWords.toNat =
      25 + MachineState.memCost
        (Accessors.loadEntry s 318 ⟨0⟩ ⟨0⟩ (UInt256.ofNat 1511)
          (UInt256.shiftLeft h1 (UInt256.ofNat 192) :: packed23 :: packedLow :: rest)
        ).activeWords.toNat := by
  have hresult := Output.run_setup0 s h1 packed23 packedLow rest hcap hcode hrun
  have hmeter := blockCost_potential_base Output.setup0Path hresult hfork
    (by simp [Output.setup0Path, CopyFree])
  rw [setup0_base] at hmeter
  simpa [Accessors.loadEntry, pathBaseCost] using hmeter

private theorem finish_cost_potential (s : State)
    (h0 shifted1 packed23 packedLow : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1019)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running) :
    let word := UInt256.lor
      (UInt256.lor (UInt256.lor
        (UInt256.shiftLeft h0 (UInt256.ofNat 224)) shifted1) packed23) packedLow
    let bytes := Data.Bytes.natToBytesPadded word.toNat 32
    let storedMemory := MachineState.writeBytes s.memory bytes 0
    let stored := { s with
      pc := UInt256.ofNat 1520
      stack := rest
      memory := storedMemory
      activeWords := s.activeWordsAfterUInt256 0 32 }
    Challenge.EvmProof.Stepper.runLocatedBlockCost Output.finishPath
        ({ s with
          pc := UInt256.ofNat 1511
          stack := h0 :: shifted1 :: packed23 :: packedLow :: rest }) +
        MachineState.memCost s.activeWords.toNat =
      26 + MachineState.memCost
        ({ stored with
          pc := UInt256.ofNat 1523
          halt := .Returned
          hReturn := bytes
          stack := rest
          activeWords := stored.activeWordsAfterUInt256 0 32 } : State).activeWords.toNat := by
  dsimp only
  have hresult := Output.run_finish s h0 shifted1 packed23 packedLow rest hcap
    hcode hrun
  have hmeter := blockCost_potential_base Output.finishPath hresult hfork
    (by simp [Output.finishPath, CopyFree])
  rw [finish_base] at hmeter
  simpa [pathBaseCost] using hmeter

set_option linter.unusedSimpArgs false in
theorem gasSteps_output_cost_potential (s : State) (offset : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1010)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    (Output.gasSteps_output s offset rest hcap hcode hfork hrun hnp).cost +
        MachineState.memCost s.activeWords.toNat =
      531 + MachineState.memCost (Output.outputResult s rest).activeWords.toNat := by
  let q7 := Output.afterH7 s rest
  let q6 := Output.afterH6 s rest
  let q5 := Output.afterH5 s rest
  let q4 := Output.afterH4 s rest
  let q3 := Output.afterH3 s rest
  let q2 := Output.afterH2 s rest
  let q1 := Output.afterH1 s rest
  let q0 := Output.afterH0 s rest
  have valid1413 : Decode.isValidJumpDest referenceBytecode 1413 = true := by decide
  have valid1424 : Decode.isValidJumpDest referenceBytecode 1424 = true := by decide
  have valid1439 : Decode.isValidJumpDest referenceBytecode 1439 = true := by decide
  have valid1453 : Decode.isValidJumpDest referenceBytecode 1453 = true := by decide
  have valid1469 : Decode.isValidJumpDest referenceBytecode 1469 = true := by decide
  have valid1483 : Decode.isValidJumpDest referenceBytecode 1483 = true := by decide
  have valid1498 : Decode.isValidJumpDest referenceBytecode 1498 = true := by decide
  have valid1511 : Decode.isValidJumpDest referenceBytecode 1511 = true := by decide
  have hStart := start_cost_potential s offset rest (by omega) hcode hfork hrun
  have hH7 := hAt_cost_potential s (UInt256.ofNat 7) ⟨0⟩
    (UInt256.ofNat 1413) rest (by omega) hcode hfork hrun hnp valid1413
  have q7code : q7.executionEnv.code = referenceBytecode := by
    simp [q7, Output.afterH7, Accessors.loadReturned, hcode]
  have q7fork : q7.fork = .Osaka := by
    change q7.executionEnv.fork = .Osaka
    simp [q7, Output.afterH7, Accessors.loadReturned, hfork]
  have q7run : q7.halt = .Running := by
    simp [q7, Output.afterH7, Accessors.loadReturned, hrun]
  have q7np : Precompile.isPrecompileWithConfig q7.executionEnv.precompileConfig q7.executionEnv.fork
      q7.executionEnv.codeAddr = false := by
    simpa [q7, Output.afterH7, Accessors.loadReturned] using hnp
  have hSetup6 := setup6_cost_potential q7 (Output.hWord s 7) rest
    (by omega) q7code q7fork q7run
  have hH6 := hAt_cost_potential q7 (UInt256.ofNat 6) ⟨0⟩
    (UInt256.ofNat 1424) (Output.hWord s 7 :: rest) (by simp; omega)
    q7code q7fork q7run q7np valid1424
  have q6code : q6.executionEnv.code = referenceBytecode := by
    simp [q6, Output.afterH6, q7, Output.afterH7, Accessors.loadReturned, hcode]
  have q6fork : q6.fork = .Osaka := by
    change q6.executionEnv.fork = .Osaka
    simp [q6, Output.afterH6, q7, Output.afterH7, Accessors.loadReturned, hfork]
  have q6run : q6.halt = .Running := by
    simp [q6, Output.afterH6, q7, Output.afterH7, Accessors.loadReturned, hrun]
  have q6np : Precompile.isPrecompileWithConfig q6.executionEnv.precompileConfig q6.executionEnv.fork
      q6.executionEnv.codeAddr = false := by
    simpa [q6, Output.afterH6, q7, Output.afterH7, Accessors.loadReturned] using hnp
  have hSetup5 := setup5_cost_potential q6 (Output.hWord s 6) (Output.hWord s 7)
    rest (by omega) q6code q6fork q6run
  have hH5 := hAt_cost_potential q6 (UInt256.ofNat 5) ⟨0⟩
    (UInt256.ofNat 1439) (Output.pair67 s :: rest) (by simp; omega)
    q6code q6fork q6run q6np valid1439
  have q5code : q5.executionEnv.code = referenceBytecode := by
    simp [q5, Output.afterH5, q6, Output.afterH6, q7, Output.afterH7,
      Accessors.loadReturned, hcode]
  have q5fork : q5.fork = .Osaka := by
    change q5.executionEnv.fork = .Osaka
    simp [q5, Output.afterH5, q6, Output.afterH6, q7, Output.afterH7,
      Accessors.loadReturned, hfork]
  have q5run : q5.halt = .Running := by
    simp [q5, Output.afterH5, q6, Output.afterH6, q7, Output.afterH7,
      Accessors.loadReturned, hrun]
  have q5np : Precompile.isPrecompileWithConfig q5.executionEnv.precompileConfig q5.executionEnv.fork
      q5.executionEnv.codeAddr = false := by
    simpa [q5, Output.afterH5, q6, Output.afterH6, q7, Output.afterH7,
      Accessors.loadReturned] using hnp
  have hSetup4 := setup4_cost_potential q5 (Output.hWord s 5) (Output.pair67 s)
    rest (by omega) q5code q5fork q5run
  have hH4 := hAt_cost_potential q5 (UInt256.ofNat 4) ⟨0⟩
    (UInt256.ofNat 1453) (Output.shifted5 s :: Output.pair67 s :: rest)
    (by simp; omega) q5code q5fork q5run q5np valid1453
  have q4code : q4.executionEnv.code = referenceBytecode := by
    simp [q4, Output.afterH4, q5, Output.afterH5, q6, Output.afterH6,
      q7, Output.afterH7, Accessors.loadReturned, hcode]
  have q4fork : q4.fork = .Osaka := by
    change q4.executionEnv.fork = .Osaka
    simp [q4, Output.afterH4, q5, Output.afterH5, q6, Output.afterH6,
      q7, Output.afterH7, Accessors.loadReturned, hfork]
  have q4run : q4.halt = .Running := by
    simp [q4, Output.afterH4, q5, Output.afterH5, q6, Output.afterH6,
      q7, Output.afterH7, Accessors.loadReturned, hrun]
  have q4np : Precompile.isPrecompileWithConfig q4.executionEnv.precompileConfig q4.executionEnv.fork
      q4.executionEnv.codeAddr = false := by
    simpa [q4, Output.afterH4, q5, Output.afterH5, q6, Output.afterH6,
      q7, Output.afterH7, Accessors.loadReturned] using hnp
  have hSetup3 := setup3_cost_potential q4 (Output.hWord s 4)
    (Output.shifted5 s) (Output.pair67 s) rest (by omega) q4code q4fork q4run
  have hH3 := hAt_cost_potential q4 (UInt256.ofNat 3) ⟨0⟩
    (UInt256.ofNat 1469) (Output.lowHalf s :: rest) (by simp; omega)
    q4code q4fork q4run q4np valid1469
  have q3code : q3.executionEnv.code = referenceBytecode := by
    simp [q3, Output.afterH3, q4, Output.afterH4, q5, Output.afterH5,
      q6, Output.afterH6, q7, Output.afterH7, Accessors.loadReturned, hcode]
  have q3fork : q3.fork = .Osaka := by
    change q3.executionEnv.fork = .Osaka
    simp [q3, Output.afterH3, q4, Output.afterH4, q5, Output.afterH5,
      q6, Output.afterH6, q7, Output.afterH7, Accessors.loadReturned, hfork]
  have q3run : q3.halt = .Running := by
    simp [q3, Output.afterH3, q4, Output.afterH4, q5, Output.afterH5,
      q6, Output.afterH6, q7, Output.afterH7, Accessors.loadReturned, hrun]
  have q3np : Precompile.isPrecompileWithConfig q3.executionEnv.precompileConfig q3.executionEnv.fork
      q3.executionEnv.codeAddr = false := by
    simpa [q3, Output.afterH3, q4, Output.afterH4, q5, Output.afterH5,
      q6, Output.afterH6, q7, Output.afterH7, Accessors.loadReturned] using hnp
  have hSetup2 := setup2_cost_potential q3 (Output.hWord s 3) (Output.lowHalf s)
    rest (by omega) q3code q3fork q3run
  have hH2 := hAt_cost_potential q3 (UInt256.ofNat 2) ⟨0⟩
    (UInt256.ofNat 1483) (Output.shifted3 s :: Output.lowHalf s :: rest)
    (by simp; omega) q3code q3fork q3run q3np valid1483
  have q2code : q2.executionEnv.code = referenceBytecode := by
    simp [q2, Output.afterH2, q3, Output.afterH3, q4, Output.afterH4,
      q5, Output.afterH5, q6, Output.afterH6, q7, Output.afterH7,
      Accessors.loadReturned, hcode]
  have q2fork : q2.fork = .Osaka := by
    change q2.executionEnv.fork = .Osaka
    simp [q2, Output.afterH2, q3, Output.afterH3, q4, Output.afterH4,
      q5, Output.afterH5, q6, Output.afterH6, q7, Output.afterH7,
      Accessors.loadReturned, hfork]
  have q2run : q2.halt = .Running := by
    simp [q2, Output.afterH2, q3, Output.afterH3, q4, Output.afterH4,
      q5, Output.afterH5, q6, Output.afterH6, q7, Output.afterH7,
      Accessors.loadReturned, hrun]
  have q2np : Precompile.isPrecompileWithConfig q2.executionEnv.precompileConfig q2.executionEnv.fork
      q2.executionEnv.codeAddr = false := by
    simpa [q2, Output.afterH2, q3, Output.afterH3, q4, Output.afterH4,
      q5, Output.afterH5, q6, Output.afterH6, q7, Output.afterH7,
      Accessors.loadReturned] using hnp
  have hSetup1 := setup1_cost_potential q2 (Output.hWord s 2)
    (Output.shifted3 s) (Output.lowHalf s) rest (by omega) q2code q2fork q2run
  have hH1 := hAt_cost_potential q2 (UInt256.ofNat 1) ⟨0⟩
    (UInt256.ofNat 1498) (Output.pair23 s :: Output.lowHalf s :: rest)
    (by simp; omega) q2code q2fork q2run q2np valid1498
  have q1code : q1.executionEnv.code = referenceBytecode := by
    simp [q1, Output.afterH1, q2, Output.afterH2, q3, Output.afterH3,
      q4, Output.afterH4, q5, Output.afterH5, q6, Output.afterH6,
      q7, Output.afterH7, Accessors.loadReturned, hcode]
  have q1fork : q1.fork = .Osaka := by
    change q1.executionEnv.fork = .Osaka
    simp [q1, Output.afterH1, q2, Output.afterH2, q3, Output.afterH3,
      q4, Output.afterH4, q5, Output.afterH5, q6, Output.afterH6,
      q7, Output.afterH7, Accessors.loadReturned, hfork]
  have q1run : q1.halt = .Running := by
    simp [q1, Output.afterH1, q2, Output.afterH2, q3, Output.afterH3,
      q4, Output.afterH4, q5, Output.afterH5, q6, Output.afterH6,
      q7, Output.afterH7, Accessors.loadReturned, hrun]
  have q1np : Precompile.isPrecompileWithConfig q1.executionEnv.precompileConfig q1.executionEnv.fork
      q1.executionEnv.codeAddr = false := by
    simpa [q1, Output.afterH1, q2, Output.afterH2, q3, Output.afterH3,
      q4, Output.afterH4, q5, Output.afterH5, q6, Output.afterH6,
      q7, Output.afterH7, Accessors.loadReturned] using hnp
  have hSetup0 := setup0_cost_potential q1 (Output.hWord s 1)
    (Output.pair23 s) (Output.lowHalf s) rest (by omega) q1code q1fork q1run
  have hH0 := hAt_cost_potential q1 (UInt256.ofNat 0) ⟨0⟩
    (UInt256.ofNat 1511)
    (Output.shifted1 s :: Output.pair23 s :: Output.lowHalf s :: rest)
    (by simp; omega) q1code q1fork q1run q1np valid1511
  have q0code : q0.executionEnv.code = referenceBytecode := by
    simp [q0, Output.afterH0, q1, Output.afterH1, q2, Output.afterH2,
      q3, Output.afterH3, q4, Output.afterH4, q5, Output.afterH5,
      q6, Output.afterH6, q7, Output.afterH7, Accessors.loadReturned, hcode]
  have q0fork : q0.fork = .Osaka := by
    change q0.executionEnv.fork = .Osaka
    simp [q0, Output.afterH0, q1, Output.afterH1, q2, Output.afterH2,
      q3, Output.afterH3, q4, Output.afterH4, q5, Output.afterH5,
      q6, Output.afterH6, q7, Output.afterH7, Accessors.loadReturned, hfork]
  have q0run : q0.halt = .Running := by
    simp [q0, Output.afterH0, q1, Output.afterH1, q2, Output.afterH2,
      q3, Output.afterH3, q4, Output.afterH4, q5, Output.afterH5,
      q6, Output.afterH6, q7, Output.afterH7, Accessors.loadReturned, hrun]
  have hFinish := finish_cost_potential q0 (Output.hWord s 0)
    (Output.shifted1 s) (Output.pair23 s) (Output.lowHalf s) rest
    (by omega) q0code q0fork q0run
  have hStart' :
      Challenge.EvmProof.Stepper.runLocatedBlockCost Output.startPath
          (Output.outputEntry s offset rest) = 22 := by
    simpa [Accessors.loadEntry] using hStart
  have hH7' :
      (Accessors.gasSteps_hAt s (UInt256.ofNat 7) ⟨0⟩
          (UInt256.ofNat 1413) rest (by omega) hcode hfork hrun hnp
          valid1413).cost + MachineState.memCost s.activeWords.toNat =
        37 + MachineState.memCost q7.activeWords.toNat := by
    simpa [q7, Output.afterH7] using hH7
  have hSetup6' :
      Challenge.EvmProof.Stepper.runLocatedBlockCost Output.setup6Path q7 = 20 := by
    simpa [q7, Output.afterH7, Output.hWord, Accessors.loadReturned,
      Accessors.loadEntry]
      using hSetup6
  have hH6' :
      (Accessors.gasSteps_hAt q7 (UInt256.ofNat 6) ⟨0⟩
          (UInt256.ofNat 1424) (Output.hWord s 7 :: rest) (by simp; omega)
          q7code q7fork q7run q7np valid1424).cost +
          MachineState.memCost q7.activeWords.toNat =
        37 + MachineState.memCost q6.activeWords.toNat := by
    simpa [q6, Output.afterH6, q7] using hH6
  have hSetup5' :
      Challenge.EvmProof.Stepper.runLocatedBlockCost Output.setup5Path q6 = 29 := by
    simpa [q6, Output.afterH6, q7, Output.afterH7, Output.hWord,
      Output.pair67, Accessors.loadReturned, Accessors.loadEntry] using hSetup5
  have hH5' :
      (Accessors.gasSteps_hAt q6 (UInt256.ofNat 5) ⟨0⟩
          (UInt256.ofNat 1439) (Output.pair67 s :: rest) (by simp; omega)
          q6code q6fork q6run q6np valid1439).cost +
          MachineState.memCost q6.activeWords.toNat =
        37 + MachineState.memCost q5.activeWords.toNat := by
    simpa [q5, Output.afterH5, q6] using hH5
  have hSetup4' :
      Challenge.EvmProof.Stepper.runLocatedBlockCost Output.setup4Path q5 = 26 := by
    simpa [q5, Output.afterH5, q6, Output.afterH6, q7, Output.afterH7,
      Output.hWord, Output.pair67, Output.shifted5, Accessors.loadReturned,
      Accessors.loadEntry] using hSetup4
  have hH4' :
      (Accessors.gasSteps_hAt q5 (UInt256.ofNat 4) ⟨0⟩
          (UInt256.ofNat 1453) (Output.shifted5 s :: Output.pair67 s :: rest)
          (by simp; omega) q5code q5fork q5run q5np valid1453).cost +
          MachineState.memCost q5.activeWords.toNat =
        37 + MachineState.memCost q4.activeWords.toNat := by
    simpa [q4, Output.afterH4, q5] using hH4
  have hSetup3' :
      Challenge.EvmProof.Stepper.runLocatedBlockCost Output.setup3Path q4 = 32 := by
    dsimp at hSetup3
    simpa [q4, Output.afterH4, q5, Output.afterH5, q6, Output.afterH6,
      q7, Output.afterH7, Output.hWord, Output.shifted5, Output.pair67,
      Output.pair45, Output.lowHalf, Accessors.loadReturned,
      Accessors.loadEntry] using hSetup3
  have hH3' :
      (Accessors.gasSteps_hAt q4 (UInt256.ofNat 3) ⟨0⟩
          (UInt256.ofNat 1469) (Output.lowHalf s :: rest) (by simp; omega)
          q4code q4fork q4run q4np valid1469).cost +
          MachineState.memCost q4.activeWords.toNat =
        37 + MachineState.memCost q3.activeWords.toNat := by
    simpa [q3, Output.afterH3, q4] using hH3
  have hSetup2' :
      Challenge.EvmProof.Stepper.runLocatedBlockCost Output.setup2Path q3 = 26 := by
    simpa [q3, Output.afterH3, q4, Output.afterH4, q5, Output.afterH5,
      q6, Output.afterH6, q7, Output.afterH7, Output.hWord,
      Output.shifted3, Output.lowHalf, Accessors.loadReturned,
      Accessors.loadEntry] using hSetup2
  have hH2' :
      (Accessors.gasSteps_hAt q3 (UInt256.ofNat 2) ⟨0⟩
          (UInt256.ofNat 1483) (Output.shifted3 s :: Output.lowHalf s :: rest)
          (by simp; omega) q3code q3fork q3run q3np valid1483).cost +
          MachineState.memCost q3.activeWords.toNat =
        37 + MachineState.memCost q2.activeWords.toNat := by
    simpa [q2, Output.afterH2, q3] using hH2
  have hSetup1' :
      Challenge.EvmProof.Stepper.runLocatedBlockCost Output.setup1Path q2 = 29 := by
    dsimp at hSetup1
    simpa [q2, Output.afterH2, q3, Output.afterH3, q4, Output.afterH4,
      q5, Output.afterH5, q6, Output.afterH6, q7, Output.afterH7,
      Output.hWord, Output.shifted3, Output.pair23, Output.lowHalf,
      Accessors.loadReturned, Accessors.loadEntry] using hSetup1
  have hH1' :
      (Accessors.gasSteps_hAt q2 (UInt256.ofNat 1) ⟨0⟩
          (UInt256.ofNat 1498) (Output.pair23 s :: Output.lowHalf s :: rest)
          (by simp; omega) q2code q2fork q2run q2np valid1498).cost +
          MachineState.memCost q2.activeWords.toNat =
        37 + MachineState.memCost q1.activeWords.toNat := by
    simpa [q1, Output.afterH1, q2] using hH1
  have hSetup0' :
      Challenge.EvmProof.Stepper.runLocatedBlockCost Output.setup0Path q1 = 25 := by
    simpa [q1, Output.afterH1, q2, Output.afterH2, q3, Output.afterH3,
      q4, Output.afterH4, q5, Output.afterH5, q6, Output.afterH6,
      q7, Output.afterH7, Output.hWord, Output.shifted1, Output.pair23,
      Output.lowHalf, Accessors.loadReturned, Accessors.loadEntry] using hSetup0
  have hH0' :
      (Accessors.gasSteps_hAt q1 (UInt256.ofNat 0) ⟨0⟩
          (UInt256.ofNat 1511)
          (Output.shifted1 s :: Output.pair23 s :: Output.lowHalf s :: rest)
          (by simp; omega) q1code q1fork q1run q1np valid1511).cost +
          MachineState.memCost q1.activeWords.toNat =
        37 + MachineState.memCost q0.activeWords.toNat := by
    simpa [q0, Output.afterH0, q1] using hH0
  have hFinish' :
      Challenge.EvmProof.Stepper.runLocatedBlockCost Output.finishPath q0 +
          MachineState.memCost q0.activeWords.toNat =
        26 + MachineState.memCost (Output.outputResult s rest).activeWords.toNat := by
    dsimp at hFinish
    simpa [q0, Output.outputResult, Output.afterH0, q1, Output.afterH1,
      q2, Output.afterH2, q3, Output.afterH3, q4, Output.afterH4,
      q5, Output.afterH5, q6, Output.afterH6, q7, Output.afterH7,
      Output.hWord, Output.shifted1, Output.pair23, Output.lowHalf,
      Output.digestWord, Output.digestBytes, Accessors.loadReturned] using hFinish
  unfold Output.gasSteps_output
  simp only [Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.GasSteps.cast_cost,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost]
  dsimp only [q7, q6, q5, q4, q3, q2, q1, q0] at *
  omega

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

theorem outputResult_activeWords_of_ge (s : State) (rest : List UInt256)
    (haw : 17 ≤ s.activeWords.toNat) :
    (Output.outputResult s rest).activeWords = s.activeWords := by
  have h7 : (Output.afterH7 s rest).activeWords = s.activeWords := by
    change s.activeWordsAfterUInt256
      (Accessors.slotOffset 288 (UInt256.ofNat 7)) 32 = s.activeWords
    apply activeWordsAfterUInt256_eq
    have : Accessors.slotOffset 288 (UInt256.ofNat 7) = 512 := by decide
    rw [this]
    omega
  have h6 : (Output.afterH6 s rest).activeWords = s.activeWords := by
    change (Output.afterH7 s rest).activeWordsAfterUInt256
      (Accessors.slotOffset 288 (UInt256.ofNat 6)) 32 = s.activeWords
    apply Eq.trans (activeWordsAfterUInt256_eq _ _ _ (by
      rw [h7]
      have : Accessors.slotOffset 288 (UInt256.ofNat 6) = 480 := by decide
      rw [this]
      omega)) h7
  have h5 : (Output.afterH5 s rest).activeWords = s.activeWords := by
    change (Output.afterH6 s rest).activeWordsAfterUInt256
      (Accessors.slotOffset 288 (UInt256.ofNat 5)) 32 = s.activeWords
    apply Eq.trans (activeWordsAfterUInt256_eq _ _ _ (by
      rw [h6]
      have : Accessors.slotOffset 288 (UInt256.ofNat 5) = 448 := by decide
      rw [this]
      omega)) h6
  have h4 : (Output.afterH4 s rest).activeWords = s.activeWords := by
    change (Output.afterH5 s rest).activeWordsAfterUInt256
      (Accessors.slotOffset 288 (UInt256.ofNat 4)) 32 = s.activeWords
    apply Eq.trans (activeWordsAfterUInt256_eq _ _ _ (by
      rw [h5]
      have : Accessors.slotOffset 288 (UInt256.ofNat 4) = 416 := by decide
      rw [this]
      omega)) h5
  have h3 : (Output.afterH3 s rest).activeWords = s.activeWords := by
    change (Output.afterH4 s rest).activeWordsAfterUInt256
      (Accessors.slotOffset 288 (UInt256.ofNat 3)) 32 = s.activeWords
    apply Eq.trans (activeWordsAfterUInt256_eq _ _ _ (by
      rw [h4]
      have : Accessors.slotOffset 288 (UInt256.ofNat 3) = 384 := by decide
      rw [this]
      omega)) h4
  have h2 : (Output.afterH2 s rest).activeWords = s.activeWords := by
    change (Output.afterH3 s rest).activeWordsAfterUInt256
      (Accessors.slotOffset 288 (UInt256.ofNat 2)) 32 = s.activeWords
    apply Eq.trans (activeWordsAfterUInt256_eq _ _ _ (by
      rw [h3]
      have : Accessors.slotOffset 288 (UInt256.ofNat 2) = 352 := by decide
      rw [this]
      omega)) h3
  have h1 : (Output.afterH1 s rest).activeWords = s.activeWords := by
    change (Output.afterH2 s rest).activeWordsAfterUInt256
      (Accessors.slotOffset 288 (UInt256.ofNat 1)) 32 = s.activeWords
    apply Eq.trans (activeWordsAfterUInt256_eq _ _ _ (by
      rw [h2]
      have : Accessors.slotOffset 288 (UInt256.ofNat 1) = 320 := by decide
      rw [this]
      omega)) h2
  have h0 : (Output.afterH0 s rest).activeWords = s.activeWords := by
    change (Output.afterH1 s rest).activeWordsAfterUInt256
      (Accessors.slotOffset 288 (UInt256.ofNat 0)) 32 = s.activeWords
    apply Eq.trans (activeWordsAfterUInt256_eq _ _ _ (by
      rw [h1]
      have : Accessors.slotOffset 288 (UInt256.ofNat 0) = 288 := by decide
      rw [this]
      omega)) h1
  let loaded := Output.afterH0 s rest
  let stored := { loaded with
    pc := UInt256.ofNat 1520
    stack := rest
    memory := MachineState.writeBytes loaded.memory (Output.digestBytes s) 0
    activeWords := loaded.activeWordsAfterUInt256 0 32 }
  have hloaded : loaded.activeWords = s.activeWords := h0
  have hstored : stored.activeWords = s.activeWords := by
    change loaded.activeWordsAfterUInt256 0 32 = s.activeWords
    apply Eq.trans (activeWordsAfterUInt256_eq _ _ _ (by rw [hloaded]; omega))
      hloaded
  change stored.activeWordsAfterUInt256 0 32 = s.activeWords
  apply Eq.trans (activeWordsAfterUInt256_eq _ _ _ (by rw [hstored]; omega))
    hstored

theorem gasSteps_output_cost_of_activeWords_ge (s : State) (offset : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1010)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (haw : 17 ≤ s.activeWords.toNat) :
    (Output.gasSteps_output s offset rest hcap hcode hfork hrun hnp).cost = 531 := by
  have hpotential := gasSteps_output_cost_potential s offset rest hcap hcode
    hfork hrun hnp
  rw [outputResult_activeWords_of_ge s rest haw] at hpotential
  omega

end Challenge.Sha256.Reference.Proofs.Bytecode.OutputGas
