import Challenge.Sha256.Reference.Proofs.Bytecode.ReferenceCorrect
import Challenge.Sha256.Reference.Proofs.Bytecode.PaddingGas
import Challenge.Sha256.Reference.Proofs.Bytecode.OutputGas
import Challenge.Sha256.Reference.Proofs.Bytecode.CompressionGas
import Challenge.Sha256.Reference.Proofs.Bytecode.DriverMemory
import Challenge.EvmProof.Meter

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Challenge.Sha256.Reference.Proofs.Bytecode.GasCost

open Challenge.Sha256
open EvmSemantics
open EvmSemantics.EVM

def referenceGas (input : ByteArray) : Nat :=
  1747 + 155996 * Driver.blockCount input +
    3 * ((input.size + 31) / 32) +
    MachineState.memCost (90 + 2 * Driver.blockCount input)

theorem memCost_monotone : Monotone MachineState.memCost := by
  intro a b hab
  unfold MachineState.memCost
  exact Nat.add_le_add (Nat.mul_le_mul_left 3 hab)
    (Nat.div_le_div_right (Nat.pow_le_pow_left hab 2))

@[simp] theorem gasSteps_setup_cost (input : ByteArray) :
    (Driver.gasSteps_setup input).cost = 3 := by
  rfl

theorem gasSteps_pad_cost (input : ByteArray) (hfit : CalldataFits input) :
    (PaddingTrace.gasSteps_pad input hfit).cost =
      1187 + 3 * ((input.size + 31) / 32) +
        MachineState.memCost (89 + 2 * Driver.blockCount input) := by
  simpa [Driver.blockCount, Padding.paddedLength] using
    PaddingGas.gasSteps_pad_cost input hfit

theorem gasSteps_blockLoop_cost_of_iterations
    (input : ByteArray) (hfit : CalldataFits input)
    (hiteration : ∀ i (hi : i < Driver.blockCount input),
      (Driver.gasSteps_blockLoopIteration input hfit i hi).cost +
          MachineState.memCost
            (Driver.blockLoopState input i).activeWords.toNat =
        155996 + MachineState.memCost
          (Driver.blockLoopState input (i + 1)).activeWords.toNat) :
    (Driver.gasSteps_blockLoop input hfit).cost +
        MachineState.memCost
          (Driver.blockLoopState input 0).activeWords.toNat =
      Driver.blockCount input * 155996 + MachineState.memCost
        (Driver.blockLoopState input
          (Driver.blockCount input)).activeWords.toNat := by
  rw [Driver.gasSteps_blockLoop_cost]
  exact Challenge.EvmProof.Meter.iterateBounded_cost_potential_add
    (Driver.blockCount input) 155996
    (Driver.gasSteps_blockLoopIteration input hfit) hiteration

theorem gasSteps_iteration_cost_of_compress
    (s : State) (input : ByteArray) (hfit : CalldataFits input)
    (i : Nat) (hi : i < Driver.blockCount input)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hcompress :
      (Driver.gasSteps_iterationCompress s input i hcode hfork hrun hnp).cost +
          MachineState.memCost (Driver.loopAt s input i).activeWords.toNat =
        155921 + MachineState.memCost
          (Driver.afterCompression s input i).activeWords.toNat) :
    (Driver.gasSteps_iteration s input hfit i hi hcode hfork hrun hnp).cost +
        MachineState.memCost (Driver.loopAt s input i).activeWords.toNat =
      155996 + MachineState.memCost
        (Driver.afterIteration s input i).activeWords.toNat := by
  have hConditionPotential := CompressionGas.blockCost_potential_of_static
    Driver.conditionPath 26
    (Driver.run_condition_continue s input hfit i hi hrun)
    (by simpa [Driver.loopAt, State.fork] using hfork)
    (by simp [Driver.conditionPath, CompressionGas.CopyFree]) (by rfl)
  have hCallPotential := CompressionGas.blockCost_potential_of_static
    Driver.callPath 23
    (Driver.run_call s input hfit i hi hcode hrun)
    (by simpa [Driver.afterCondition, Driver.loopAt, State.fork] using hfork)
    (by simp [Driver.callPath, CompressionGas.CopyFree]) (by rfl)
  have hIncrementPotential := CompressionGas.blockCost_potential_of_static
    Driver.incrementPath 26
    (Driver.run_increment s input hfit i hi hcode hrun)
    (by simpa [State.fork] using hfork)
    (by simp [Driver.incrementPath, CompressionGas.CopyFree]) (by rfl)
  have hCondition : Challenge.EvmProof.Stepper.runLocatedBlockCost
      Driver.conditionPath (Driver.loopAt s input i) = 26 := by
    have haw : (Driver.afterCondition s input i).activeWords =
        (Driver.loopAt s input i).activeWords := by rfl
    rw [haw] at hConditionPotential
    omega
  have hCall : Challenge.EvmProof.Stepper.runLocatedBlockCost Driver.callPath
      (Driver.afterCondition s input i) = 23 := by
    have haw : (Compression.compressEntry (Driver.loopAt s input i)
        (Driver.messageOffsetWord i) (UInt256.ofNat 1390)
        [Driver.blockOffsetWord i, Padding.paddedWord input]).activeWords =
          (Driver.afterCondition s input i).activeWords := by rfl
    rw [haw] at hCallPotential
    omega
  have hIncrement : Challenge.EvmProof.Stepper.runLocatedBlockCost
      Driver.incrementPath (Driver.afterCompression s input i) = 26 := by
    have haw : (Driver.afterIteration s input i).activeWords =
        (Driver.afterCompression s input i).activeWords := by rfl
    rw [haw] at hIncrementPotential
    omega
  simp only [Driver.gasSteps_iteration,
    Challenge.EvmProof.GasSteps.trans_cost,
    Driver.gasSteps_iterationCondition_cost,
    Driver.gasSteps_iterationCall_cost,
    Driver.gasSteps_iterationIncrement_cost]
  rw [hCondition, hCall, hIncrement]
  rw [show (Driver.afterIteration s input i).activeWords =
      (Driver.afterCompression s input i).activeWords by rfl]
  omega

theorem gasSteps_blockLoop_cost_of_compressions
    (input : ByteArray) (hfit : CalldataFits input)
    (hcompress : ∀ (s : State) (i : Nat)
      (hcode : s.executionEnv.code = referenceBytecode)
      (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
      (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
        s.executionEnv.codeAddr = false),
      (Driver.gasSteps_iterationCompress s input i
          hcode hfork hrun hnp).cost +
        MachineState.memCost (Driver.loopAt s input i).activeWords.toNat =
      155921 + MachineState.memCost
        (Driver.afterCompression s input i).activeWords.toNat) :
    (Driver.gasSteps_blockLoop input hfit).cost +
        MachineState.memCost
          (Driver.blockLoopState input 0).activeWords.toNat =
      Driver.blockCount input * 155996 + MachineState.memCost
        (Driver.blockLoopState input
          (Driver.blockCount input)).activeWords.toNat := by
  apply gasSteps_blockLoop_cost_of_iterations input hfit
  intro i hi
  let q := Driver.blockLoopState input i
  have qcode : q.executionEnv.code = referenceBytecode := by simp [q]
  have qfork : q.fork = .Osaka := by simp [q, State.fork]
  have qrun : q.halt = .Running := by simp [q]
  have qnp : Precompile.isPrecompileWithConfig q.executionEnv.precompileConfig q.executionEnv.fork
      q.executionEnv.codeAddr = false := by
    simpa [q, State.fork] using
      PaddingTrace.padReturned_noPrecompile input
  rw [Driver.gasSteps_blockLoopIteration_cost]
  apply gasSteps_iteration_cost_of_compress
  exact hcompress q i qcode qfork qrun qnp

set_option linter.unusedSimpArgs false in
@[simp] theorem gasSteps_exit_cost (input : ByteArray)
    (hfit : CalldataFits input) :
    (Driver.gasSteps_exit input hfit).cost = 26 := by
  have hoff : ¬Driver.blockOffset (Driver.blockCount input) <
      Padding.paddedLength input.size := by
    rw [Driver.paddedLength_eq_blockCount]
    simp [Driver.blockOffset]
  have hfixed := Driver.loopAt_blockLoopState input (Driver.blockCount input)
  have hpc : (Driver.blockLoopState input (Driver.blockCount input)).pc =
      UInt256.ofNat 1369 := by
    have h := congrArg (fun q : State => q.pc) hfixed
    simpa [Driver.loopAt] using h.symm
  have hstack :
      (Driver.blockLoopState input (Driver.blockCount input)).stack =
        [Driver.blockOffsetWord (Driver.blockCount input),
          Padding.paddedWord input] := by
    have h := congrArg (fun q : State => q.stack) hfixed
    simpa [Driver.loopAt] using h.symm
  simp [Driver.gasSteps_exit, Driver.conditionPath,
    Challenge.EvmProof.Stepper.runLocatedBlockCost,
    Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Stepper.instrCost, Gas.baseCost,
    Driver.blockLoopState, Driver.loopAt, Driver.afterIteration,
    Driver.blockOffsetWord, Driver.blockOffset, hoff, hpc, hstack]

/-- Arithmetic assembly of the reference schedule.  The hypotheses are the
three SHA-specific cost summaries; all trace composition and memory-cost
telescoping is discharged here. -/
theorem gasSteps_reference_cost_of_components
    (input : ByteArray) (hfit : CalldataFits input)
    (hloop : (Driver.gasSteps_blockLoop input hfit).cost =
      155996 * Driver.blockCount input +
        (MachineState.memCost (90 + 2 * Driver.blockCount input) -
          MachineState.memCost (89 + 2 * Driver.blockCount input)))
    (hactive : 17 ≤ (Driver.blockLoopState input
      (Driver.blockCount input)).activeWords.toNat) :
    (Driver.gasSteps_reference input hfit).cost = referenceGas input := by
  have houtput : (Output.gasSteps_output
      (Driver.blockLoopState input (Driver.blockCount input))
      (Driver.blockOffsetWord (Driver.blockCount input))
      [Padding.paddedWord input] (by simp) (by simp) (by simp [State.fork])
      (by simp) (by
        simpa [State.fork] using PaddingTrace.padReturned_noPrecompile input)
      ).cost = 531 := by
    apply OutputGas.gasSteps_output_cost_of_activeWords_ge
    exact hactive
  unfold Driver.gasSteps_reference
  simp only [Challenge.EvmProof.GasSteps.trans_cost]
  rw [gasSteps_pad_cost, gasSteps_setup_cost, hloop, gasSteps_exit_cost, houtput]
  have hmem : MachineState.memCost (89 + 2 * Driver.blockCount input) ≤
      MachineState.memCost (90 + 2 * Driver.blockCount input) :=
    memCost_monotone (by omega)
  unfold referenceGas
  omega

/-- Exact cost of the same complete execution certificate used by the
functional-correctness proof. -/
theorem gasSteps_reference_cost (input : ByteArray)
    (hfit : CalldataFits input) :
    (Driver.gasSteps_reference input hfit).cost = referenceGas input := by
  have hcompress : ∀ (s : State) (i : Nat)
      (hcode : s.executionEnv.code = referenceBytecode)
      (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
      (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
        s.executionEnv.codeAddr = false),
      (Driver.gasSteps_iterationCompress s input i
          hcode hfork hrun hnp).cost +
        MachineState.memCost (Driver.loopAt s input i).activeWords.toNat =
      155921 + MachineState.memCost
        (Driver.afterCompression s input i).activeWords.toNat := by
    intro s i hcode hfork hrun hnp
    rw [Driver.gasSteps_iterationCompress_cost]
    have h := CompressionGas.gasSteps_compress_cost_potential
      (Driver.loopAt s input i) (Driver.messageOffsetWord i)
      (UInt256.ofNat 1390)
      [Driver.blockOffsetWord i, Padding.paddedWord input]
      (by simp) (by simpa using hcode)
      (by simpa [State.fork] using hfork) (by simpa using hrun)
      (by simpa using hnp) (by decide)
    simpa [Driver.afterCompression, Compression.compressEntry] using h
  have hloopAdd := gasSteps_blockLoop_cost_of_compressions input hfit hcompress
  rw [DriverMemory.blockLoopState_zero_activeWords input hfit,
    DriverMemory.blockLoopState_final_activeWords input hfit] at hloopAdd
  have hmem : MachineState.memCost (89 + 2 * Driver.blockCount input) ≤
      MachineState.memCost (90 + 2 * Driver.blockCount input) :=
    memCost_monotone (by omega)
  have hloop : (Driver.gasSteps_blockLoop input hfit).cost =
      155996 * Driver.blockCount input +
        (MachineState.memCost (90 + 2 * Driver.blockCount input) -
          MachineState.memCost (89 + 2 * Driver.blockCount input)) := by
    omega
  exact gasSteps_reference_cost_of_components input hfit hloop
    (DriverMemory.blockLoopState_final_activeWords_ge_seventeen input hfit)

end Challenge.Sha256.Reference.Proofs.Bytecode.GasCost
