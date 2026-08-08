import Challenge.EvmProof.Meter
import Challenge.Sha256.Reference.Proofs.Bytecode.BigSigma

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Challenge.Sha256.Reference.Proofs.Bytecode.ArithmeticGas

open Challenge.Sha256
open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler

private def CopyFree : Instr → Prop
  | .op .CALLDATACOPY => False
  | .op .MCOPY => False
  | _ => True

private theorem instrCostWithoutMemory_eq_static (instruction : Instr) (s : State)
    (hfork : s.fork = .Osaka) (hfree : CopyFree instruction) :
    Challenge.EvmProof.Meter.instrCostWithoutMemory instruction s =
      Challenge.EvmProof.Meter.instrStaticCost .Osaka instruction := by
  cases instruction with
  | push width value => simp [Challenge.EvmProof.Meter.instrCostWithoutMemory,
      Challenge.EvmProof.Meter.instrStaticCost, hfork]
  | op op =>
      cases op with
      | StopArith op => cases op <;> simp [Challenge.EvmProof.Meter.instrCostWithoutMemory,
          Challenge.EvmProof.Meter.instrStaticCost, hfork]
      | CompBit op => cases op <;> simp [Challenge.EvmProof.Meter.instrCostWithoutMemory,
          Challenge.EvmProof.Meter.instrStaticCost, hfork]
      | Keccak op => cases op; simp [Challenge.EvmProof.Meter.instrCostWithoutMemory,
          Challenge.EvmProof.Meter.instrStaticCost, hfork]
      | Env op => cases op <;> simp [CopyFree,
          Challenge.EvmProof.Meter.instrCostWithoutMemory,
          Challenge.EvmProof.Meter.instrStaticCost, hfork] at hfree ⊢
      | Block op => cases op <;> simp [Challenge.EvmProof.Meter.instrCostWithoutMemory,
          Challenge.EvmProof.Meter.instrStaticCost, hfork]
      | StackMemFlow op => cases op <;> simp [CopyFree,
          Challenge.EvmProof.Meter.instrCostWithoutMemory,
          Challenge.EvmProof.Meter.instrStaticCost, hfork] at hfree ⊢
      | Push op => cases op; simp [Challenge.EvmProof.Meter.instrCostWithoutMemory,
          Challenge.EvmProof.Meter.instrStaticCost, hfork]
      | Dup op => cases op; simp [Challenge.EvmProof.Meter.instrCostWithoutMemory,
          Challenge.EvmProof.Meter.instrStaticCost, hfork]
      | Swap op => cases op; simp [Challenge.EvmProof.Meter.instrCostWithoutMemory,
          Challenge.EvmProof.Meter.instrStaticCost, hfork]
      | DupN op => cases op; simp [Challenge.EvmProof.Meter.instrCostWithoutMemory,
          Challenge.EvmProof.Meter.instrStaticCost, hfork]
      | SwapN op => cases op; simp [Challenge.EvmProof.Meter.instrCostWithoutMemory,
          Challenge.EvmProof.Meter.instrStaticCost, hfork]
      | Exchange op => cases op; simp [Challenge.EvmProof.Meter.instrCostWithoutMemory,
          Challenge.EvmProof.Meter.instrStaticCost, hfork]
      | Log op => cases op; simp [Challenge.EvmProof.Meter.instrCostWithoutMemory,
          Challenge.EvmProof.Meter.instrStaticCost, hfork]
      | System op => cases op <;> simp [Challenge.EvmProof.Meter.instrCostWithoutMemory,
          Challenge.EvmProof.Meter.instrStaticCost, hfork]

private theorem block_cost_potential
    {artifact : Challenge.EvmProof.ProgramArtifact}
    (path : List (Challenge.EvmProof.Stepper.Located artifact .Osaka))
    {s t : State}
    (hresult : Challenge.EvmProof.Stepper.runLocatedBlock path s = some t)
    (hfork : s.fork = .Osaka)
    (hfree : ∀ located ∈ path, CopyFree located.instruction) :
    Challenge.EvmProof.Stepper.runLocatedBlockCost path s +
        MachineState.memCost s.activeWords.toNat =
      Challenge.EvmProof.Meter.runLocatedBlockStaticCost path +
        MachineState.memCost t.activeWords.toNat := by
  apply Challenge.EvmProof.Meter.runLocatedBlock_cost_static_potential
    path hresult hfork
  intro located hmem q hq
  exact instrCostWithoutMemory_eq_static located.instruction q hq
    (hfree located hmem)

private theorem block_cost_of_activeWords_eq
    {artifact : Challenge.EvmProof.ProgramArtifact}
    (path : List (Challenge.EvmProof.Stepper.Located artifact .Osaka))
    {s t : State}
    (hresult : Challenge.EvmProof.Stepper.runLocatedBlock path s = some t)
    (hfork : s.fork = .Osaka)
    (hfree : ∀ located ∈ path, CopyFree located.instruction)
    (hwords : t.activeWords = s.activeWords) :
    Challenge.EvmProof.Stepper.runLocatedBlockCost path s =
      Challenge.EvmProof.Meter.runLocatedBlockStaticCost path := by
  have hpotential := block_cost_potential path hresult hfork hfree
  rw [hwords] at hpotential
  omega

private theorem rotr_static :
    Challenge.EvmProof.Meter.runLocatedBlockStaticCost Functions.rotrPath = 54 := by
  rfl

theorem gasSteps_rotr_cost_potential (s : State) (x : UInt256) (n : Nat)
    (output returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1016) (hn : n ≤ 32)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hvalid : Decode.isValidJumpDest referenceBytecode returnDest.toNat = true) :
    (Functions.gasSteps_rotr s x n output returnDest rest hcap hn hcode hfork
      hrun hnp hvalid).cost + MachineState.memCost s.activeWords.toNat =
      54 + MachineState.memCost
        (Functions.unaryReturned s (Word.evmRotr32 x n)
          returnDest rest).activeWords.toNat := by
  have hresult := Functions.run_rotr s x n output returnDest rest hcap hn
    hcode hrun hvalid
  have hmeter := block_cost_potential Functions.rotrPath hresult hfork
    (by simp [Functions.rotrPath, CopyFree])
  rw [rotr_static] at hmeter
  unfold Functions.gasSteps_rotr
  simp only [Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost]
  simpa [Functions.rotrEntry] using hmeter

theorem gasSteps_rotr_cost (s : State) (x : UInt256) (n : Nat)
    (output returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1016) (hn : n ≤ 32)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hvalid : Decode.isValidJumpDest referenceBytecode returnDest.toNat = true) :
    (Functions.gasSteps_rotr s x n output returnDest rest hcap hn hcode hfork
      hrun hnp hvalid).cost = 54 := by
  have hpotential := gasSteps_rotr_cost_potential s x n output returnDest rest
    hcap hn hcode hfork hrun hnp hvalid
  simp [Functions.unaryReturned] at hpotential
  exact hpotential

private theorem ch_static :
    Challenge.EvmProof.Meter.runLocatedBlockStaticCost Functions.chPath = 47 := by
  rfl

theorem gasSteps_ch_cost_potential (s : State) (x y z output returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1016)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hvalid : Decode.isValidJumpDest referenceBytecode returnDest.toNat = true) :
    (Functions.gasSteps_ch s x y z output returnDest rest hcap hcode hfork
      hrun hnp hvalid).cost + MachineState.memCost s.activeWords.toNat =
      47 + MachineState.memCost
        (Functions.unaryReturned s (Word.evmCh x y z) returnDest rest).activeWords.toNat := by
  have hresult := Functions.run_ch s x y z output returnDest rest hcap hcode
    hrun hvalid
  have hmeter := block_cost_potential Functions.chPath hresult hfork
    (by simp [Functions.chPath, CopyFree])
  rw [ch_static] at hmeter
  unfold Functions.gasSteps_ch
  simp only [Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost]
  simpa [Functions.ternaryEntry] using hmeter

private theorem maj_static :
    Challenge.EvmProof.Meter.runLocatedBlockStaticCost Functions.majPath = 56 := by
  rfl

theorem gasSteps_maj_cost_potential (s : State) (x y z output returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1015)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hvalid : Decode.isValidJumpDest referenceBytecode returnDest.toNat = true) :
    (Functions.gasSteps_maj s x y z output returnDest rest hcap hcode hfork
      hrun hnp hvalid).cost + MachineState.memCost s.activeWords.toNat =
      56 + MachineState.memCost
        (Functions.unaryReturned s (Word.evmMaj x y z) returnDest rest).activeWords.toNat := by
  have hresult := Functions.run_maj s x y z output returnDest rest hcap hcode
    hrun hvalid
  have hmeter := block_cost_potential Functions.majPath hresult hfork
    (by simp [Functions.majPath, CopyFree])
  rw [maj_static] at hmeter
  unfold Functions.gasSteps_maj
  simp only [Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost]
  simpa [Functions.ternaryEntry] using hmeter

private theorem ssig0_setup_static :
    Challenge.EvmProof.Meter.runLocatedBlockStaticCost Functions.ssig0SetupPath = 32 := by
  rfl

private theorem ssig0_middle_static :
    Challenge.EvmProof.Meter.runLocatedBlockStaticCost Functions.ssig0MiddlePath = 23 := by
  rfl

private theorem ssig0_finish_static :
    Challenge.EvmProof.Meter.runLocatedBlockStaticCost Functions.ssig0FinishPath = 25 := by
  rfl

theorem gasSteps_ssig0_cost_potential (s : State) (x output returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1011)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hvalid : Decode.isValidJumpDest referenceBytecode returnDest.toNat = true) :
    (Functions.gasSteps_ssig0 s x output returnDest rest hcap hcode hfork
      hrun hnp hvalid).cost + MachineState.memCost s.activeWords.toNat =
      188 + MachineState.memCost
        (Functions.unaryReturned s (Word.evmSmallSigma0 x) returnDest rest).activeWords.toNat := by
  have setupResult := Functions.run_ssig0Setup s x output returnDest rest
    (by omega) hcode hrun
  have setupCost := block_cost_of_activeWords_eq Functions.ssig0SetupPath
    setupResult hfork (by simp [Functions.ssig0SetupPath, CopyFree]) (by rfl)
  rw [ssig0_setup_static] at setupCost
  have firstCost := gasSteps_rotr_cost s x 18 0 (UInt256.ofNat 48)
    (UInt256.shiftRight x (UInt256.ofNat 3) :: x :: output :: returnDest :: rest)
    (by simp; omega) (by decide) hcode hfork hrun hnp (by decide)
  have middleResult := Functions.run_ssig0Middle s x output returnDest rest
    (by omega) hcode hrun
  have middleCost := block_cost_of_activeWords_eq Functions.ssig0MiddlePath
    middleResult hfork (by simp [Functions.ssig0MiddlePath, CopyFree]) (by rfl)
  rw [ssig0_middle_static] at middleCost
  have secondCost := gasSteps_rotr_cost s x 7 0 (UInt256.ofNat 60)
    (Word.evmRotr32 x 18 :: UInt256.shiftRight x (UInt256.ofNat 3) ::
      x :: output :: returnDest :: rest)
    (by simp; omega) (by decide) hcode hfork hrun hnp (by decide)
  have finishResult := Functions.run_ssig0Finish s x output returnDest rest
    (by omega) hcode hrun hvalid
  have finishCost := block_cost_of_activeWords_eq Functions.ssig0FinishPath
    finishResult hfork (by simp [Functions.ssig0FinishPath, CopyFree]) (by rfl)
  rw [ssig0_finish_static] at finishCost
  unfold Functions.gasSteps_ssig0
  simp only [Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost]
  simp only [Functions.unaryReturned] at ⊢
  omega

private theorem ssig1_setup_static :
    Challenge.EvmProof.Meter.runLocatedBlockStaticCost Functions.ssig1SetupPath = 32 := by
  rfl

private theorem ssig1_middle_static :
    Challenge.EvmProof.Meter.runLocatedBlockStaticCost Functions.ssig1MiddlePath = 23 := by
  rfl

private theorem ssig1_finish_static :
    Challenge.EvmProof.Meter.runLocatedBlockStaticCost Functions.ssig1FinishPath = 25 := by
  rfl

theorem gasSteps_ssig1_cost_potential (s : State) (x output returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1011)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hvalid : Decode.isValidJumpDest referenceBytecode returnDest.toNat = true) :
    (Functions.gasSteps_ssig1 s x output returnDest rest hcap hcode hfork
      hrun hnp hvalid).cost + MachineState.memCost s.activeWords.toNat =
      188 + MachineState.memCost
        (Functions.unaryReturned s (Word.evmSmallSigma1 x) returnDest rest).activeWords.toNat := by
  have setupResult := Functions.run_ssig1Setup s x output returnDest rest
    (by omega) hcode hrun
  have setupCost := block_cost_of_activeWords_eq Functions.ssig1SetupPath
    setupResult hfork (by simp [Functions.ssig1SetupPath, CopyFree]) (by rfl)
  rw [ssig1_setup_static] at setupCost
  have firstCost := gasSteps_rotr_cost s x 19 0 (UInt256.ofNat 89)
    (UInt256.shiftRight x (UInt256.ofNat 10) :: x :: output :: returnDest :: rest)
    (by simp; omega) (by decide) hcode hfork hrun hnp (by decide)
  have middleResult := Functions.run_ssig1Middle s x output returnDest rest
    (by omega) hcode hrun
  have middleCost := block_cost_of_activeWords_eq Functions.ssig1MiddlePath
    middleResult hfork (by simp [Functions.ssig1MiddlePath, CopyFree]) (by rfl)
  rw [ssig1_middle_static] at middleCost
  have secondCost := gasSteps_rotr_cost s x 17 0 (UInt256.ofNat 101)
    (Word.evmRotr32 x 19 :: UInt256.shiftRight x (UInt256.ofNat 10) ::
      x :: output :: returnDest :: rest)
    (by simp; omega) (by decide) hcode hfork hrun hnp (by decide)
  have finishResult := Functions.run_ssig1Finish s x output returnDest rest
    (by omega) hcode hrun hvalid
  have finishCost := block_cost_of_activeWords_eq Functions.ssig1FinishPath
    finishResult hfork (by simp [Functions.ssig1FinishPath, CopyFree]) (by rfl)
  rw [ssig1_finish_static] at finishCost
  unfold Functions.gasSteps_ssig1
  simp only [Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost]
  simp only [Functions.unaryReturned] at ⊢
  omega

private theorem bigSigma0_setup_static :
    Challenge.EvmProof.Meter.runLocatedBlockStaticCost BigSigma.bigSigma0SetupPath = 23 := by
  rfl

private theorem bigSigma0_middle1_static :
    Challenge.EvmProof.Meter.runLocatedBlockStaticCost BigSigma.bigSigma0Middle1Path = 23 := by
  rfl

private theorem bigSigma0_middle2_static :
    Challenge.EvmProof.Meter.runLocatedBlockStaticCost BigSigma.bigSigma0Middle2Path = 23 := by
  rfl

private theorem bigSigma0_finish_static :
    Challenge.EvmProof.Meter.runLocatedBlockStaticCost BigSigma.bigSigma0FinishPath = 25 := by
  rfl

theorem gasSteps_bigSigma0_cost_potential (s : State)
    (x output returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1011)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hvalid : Decode.isValidJumpDest referenceBytecode returnDest.toNat = true) :
    (BigSigma.gasSteps_bigSigma0 s x output returnDest rest hcap hcode hfork
      hrun hnp hvalid).cost + MachineState.memCost s.activeWords.toNat =
      256 + MachineState.memCost
        (Functions.unaryReturned s (Word.evmBigSigma0 x) returnDest rest).activeWords.toNat := by
  have setupResult := BigSigma.run_setup BigSigma.bigSigma0SetupPath s 114 22 126
    x output returnDest rest (Or.inl ⟨rfl, rfl, rfl, rfl⟩) (by omega)
    hcode hrun
  have setupCost := block_cost_of_activeWords_eq BigSigma.bigSigma0SetupPath
    setupResult hfork (by simp [BigSigma.bigSigma0SetupPath, CopyFree]) (by rfl)
  rw [bigSigma0_setup_static] at setupCost
  have firstCost := gasSteps_rotr_cost s x 22 0 (UInt256.ofNat 126)
    (x :: output :: returnDest :: rest) (by simp; omega) (by decide)
    hcode hfork hrun hnp (by decide)
  have middle1Result := BigSigma.run_middle1 BigSigma.bigSigma0Middle1Path
    s 22 13 138 x output returnDest rest (Or.inl ⟨rfl, rfl, rfl, rfl⟩)
    (by omega) hcode hrun
  have middle1Cost := block_cost_of_activeWords_eq BigSigma.bigSigma0Middle1Path
    middle1Result hfork (by simp [BigSigma.bigSigma0Middle1Path, CopyFree])
      (by rfl)
  rw [bigSigma0_middle1_static] at middle1Cost
  simp at middle1Cost
  have secondCost := gasSteps_rotr_cost s x 13 0 (UInt256.ofNat 138)
    (Word.evmRotr32 x 22 :: x :: output :: returnDest :: rest)
    (by simp; omega) (by decide) hcode hfork hrun hnp (by decide)
  have middle2Result := BigSigma.run_middle2 BigSigma.bigSigma0Middle2Path
    s 22 13 2 150 138 x output returnDest rest
    (Or.inl ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩) (by omega) hcode hrun
  have middle2Cost := block_cost_of_activeWords_eq BigSigma.bigSigma0Middle2Path
    middle2Result hfork (by simp [BigSigma.bigSigma0Middle2Path, CopyFree])
      (by rfl)
  rw [bigSigma0_middle2_static] at middle2Cost
  have thirdCost := gasSteps_rotr_cost s x 2 0 (UInt256.ofNat 150)
    (Word.evmRotr32 x 13 :: Word.evmRotr32 x 22 ::
      x :: output :: returnDest :: rest)
    (by simp; omega) (by decide) hcode hfork hrun hnp (by decide)
  have finishResult := BigSigma.run_finish BigSigma.bigSigma0FinishPath
    s 22 13 2 150 (Word.evmBigSigma0 x) x output returnDest rest
    (Or.inl ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩) (by omega) hcode hrun hvalid
  have finishCost := block_cost_of_activeWords_eq BigSigma.bigSigma0FinishPath
    finishResult hfork (by simp [BigSigma.bigSigma0FinishPath, CopyFree]) (by rfl)
  rw [bigSigma0_finish_static] at finishCost
  unfold BigSigma.gasSteps_bigSigma0
  simp only [Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost]
  simp only [Functions.unaryReturned] at ⊢
  omega

private theorem bigSigma1_setup_static :
    Challenge.EvmProof.Meter.runLocatedBlockStaticCost BigSigma.bigSigma1SetupPath = 23 := by
  rfl

private theorem bigSigma1_middle1_static :
    Challenge.EvmProof.Meter.runLocatedBlockStaticCost BigSigma.bigSigma1Middle1Path = 23 := by
  rfl

private theorem bigSigma1_middle2_static :
    Challenge.EvmProof.Meter.runLocatedBlockStaticCost BigSigma.bigSigma1Middle2Path = 23 := by
  rfl

private theorem bigSigma1_finish_static :
    Challenge.EvmProof.Meter.runLocatedBlockStaticCost BigSigma.bigSigma1FinishPath = 25 := by
  rfl

theorem gasSteps_bigSigma1_cost_potential (s : State)
    (x output returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1011)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hvalid : Decode.isValidJumpDest referenceBytecode returnDest.toNat = true) :
    (BigSigma.gasSteps_bigSigma1 s x output returnDest rest hcap hcode hfork
      hrun hnp hvalid).cost + MachineState.memCost s.activeWords.toNat =
      256 + MachineState.memCost
        (Functions.unaryReturned s (Word.evmBigSigma1 x) returnDest rest).activeWords.toNat := by
  have setupResult := BigSigma.run_setup BigSigma.bigSigma1SetupPath s 163 25 175
    x output returnDest rest (Or.inr ⟨rfl, rfl, rfl, rfl⟩) (by omega)
    hcode hrun
  have setupCost := block_cost_of_activeWords_eq BigSigma.bigSigma1SetupPath
    setupResult hfork (by simp [BigSigma.bigSigma1SetupPath, CopyFree]) (by rfl)
  rw [bigSigma1_setup_static] at setupCost
  have firstCost := gasSteps_rotr_cost s x 25 0 (UInt256.ofNat 175)
    (x :: output :: returnDest :: rest) (by simp; omega) (by decide)
    hcode hfork hrun hnp (by decide)
  have middle1Result := BigSigma.run_middle1 BigSigma.bigSigma1Middle1Path
    s 25 11 187 x output returnDest rest (Or.inr ⟨rfl, rfl, rfl, rfl⟩)
    (by omega) hcode hrun
  have middle1Cost := block_cost_of_activeWords_eq BigSigma.bigSigma1Middle1Path
    middle1Result hfork (by simp [BigSigma.bigSigma1Middle1Path, CopyFree])
      (by rfl)
  rw [bigSigma1_middle1_static] at middle1Cost
  simp at middle1Cost
  have secondCost := gasSteps_rotr_cost s x 11 0 (UInt256.ofNat 187)
    (Word.evmRotr32 x 25 :: x :: output :: returnDest :: rest)
    (by simp; omega) (by decide) hcode hfork hrun hnp (by decide)
  have middle2Result := BigSigma.run_middle2 BigSigma.bigSigma1Middle2Path
    s 25 11 6 199 187 x output returnDest rest
    (Or.inr ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩) (by omega) hcode hrun
  have middle2Cost := block_cost_of_activeWords_eq BigSigma.bigSigma1Middle2Path
    middle2Result hfork (by simp [BigSigma.bigSigma1Middle2Path, CopyFree])
      (by rfl)
  rw [bigSigma1_middle2_static] at middle2Cost
  have thirdCost := gasSteps_rotr_cost s x 6 0 (UInt256.ofNat 199)
    (Word.evmRotr32 x 11 :: Word.evmRotr32 x 25 ::
      x :: output :: returnDest :: rest)
    (by simp; omega) (by decide) hcode hfork hrun hnp (by decide)
  have finishResult := BigSigma.run_finish BigSigma.bigSigma1FinishPath
    s 25 11 6 199 (Word.evmBigSigma1 x) x output returnDest rest
    (Or.inr ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩) (by omega) hcode hrun hvalid
  have finishCost := block_cost_of_activeWords_eq BigSigma.bigSigma1FinishPath
    finishResult hfork (by simp [BigSigma.bigSigma1FinishPath, CopyFree]) (by rfl)
  rw [bigSigma1_finish_static] at finishCost
  unfold BigSigma.gasSteps_bigSigma1
  simp only [Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost]
  simp only [Functions.unaryReturned] at ⊢
  omega

end Challenge.Sha256.Reference.Proofs.Bytecode.ArithmeticGas
