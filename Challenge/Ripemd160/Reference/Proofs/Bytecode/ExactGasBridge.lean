import Challenge.Ripemd160.Reference.Proofs.Bytecode.DirectCorrect
import Challenge.Ripemd160.Reference.Proofs.Bytecode.CompressionTrace
import Challenge.Ripemd160.Reference.Proofs.Bytecode.RoundTrace
import Challenge.Ripemd160.Reference.Proofs.Bytecode.OutputGas
import Challenge.EvmProof.Meter

set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000

/-!
# Exact-gas telescope for the RIPEMD-160 reference

This module performs the arithmetic closure needed by `DirectCorrect`.  The
only hypotheses left are facts whose producing traces are currently private
to `DirectCorrect` (the outer composition) or belong to the independently
developed padding/compression gas lanes.  Driver control-flow and the complete
block-count telescope are proved here from the shared `Meter` potential.
-/

namespace Challenge.Ripemd160.Reference.Proofs.Bytecode.ExactGasBridge

open Challenge.Ripemd160
open Challenge.EvmProof
open EvmSemantics
open EvmSemantics.EVM

set_option linter.unusedSimpArgs false in
private theorem condition_cost_potential (s : State) (input : ByteArray)
    (hfit : CalldataFits input) (i : Nat) (hi : i < DriverTrace.blockCount input)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    (DriverTrace.gasSteps_condition_continue s input hfit i hi hcode hfork
      hrun hnp).cost + MachineState.memCost s.activeWords.toNat =
        26 + MachineState.memCost s.activeWords.toNat := by
  have hmeter := Challenge.EvmProof.Meter.runLocatedBlock_cost_static_potential
    DriverTrace.conditionPath
    (DriverTrace.run_condition_continue s input hfit i hi hrun)
    (by simpa [DriverTrace.loopAt, State.fork] using hfork)
    (by
      intro located hmem q hq
      simp [DriverTrace.conditionPath,
        Challenge.EvmProof.Meter.instrCostWithoutMemory,
        Challenge.EvmProof.Meter.instrStaticCost] at hmem ⊢
      rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [Challenge.EvmProof.Meter.instrCostWithoutMemory,
          Challenge.EvmProof.Meter.instrStaticCost, hq])
  change Challenge.EvmProof.Stepper.runLocatedBlockCost
      DriverTrace.conditionPath (DriverTrace.loopAt s input i) +
        MachineState.memCost s.activeWords.toNat = _
  simpa [Challenge.EvmProof.Meter.runLocatedBlockStaticCost,
    Challenge.EvmProof.Meter.instrStaticCost, Gas.baseCost,
    DriverTrace.conditionPath, DriverTrace.loopAt,
    DriverTrace.afterCondition] using hmeter

set_option linter.unusedSimpArgs false in
private theorem call_cost_potential (s : State) (input : ByteArray)
    (hfit : CalldataFits input) (i : Nat) (hi : i < DriverTrace.blockCount input)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    (DriverTrace.gasSteps_call s input hfit i hi hcode hfork hrun hnp).cost +
        MachineState.memCost s.activeWords.toNat =
      23 + MachineState.memCost s.activeWords.toNat := by
  have hmeter := Challenge.EvmProof.Meter.runLocatedBlock_cost_static_potential
    DriverTrace.callPath (DriverTrace.run_call s input hfit i hi hcode hrun)
    (by simpa [DriverTrace.afterCondition, DriverTrace.loopAt, State.fork]
      using hfork)
    (by
      intro located hmem q hq
      simp [DriverTrace.callPath] at hmem
      rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [Challenge.EvmProof.Meter.instrCostWithoutMemory,
          Challenge.EvmProof.Meter.instrStaticCost, hq])
  change Challenge.EvmProof.Stepper.runLocatedBlockCost DriverTrace.callPath
      (DriverTrace.afterCondition s input i) +
        MachineState.memCost s.activeWords.toNat = _
  simpa [Challenge.EvmProof.Meter.runLocatedBlockStaticCost,
    Challenge.EvmProof.Meter.instrStaticCost, Gas.baseCost,
    DriverTrace.callPath, DriverTrace.afterCondition, DriverTrace.loopAt,
    DriverTrace.compressEntry] using hmeter

set_option linter.unusedSimpArgs false in
private theorem increment_cost_potential (s : State) (input : ByteArray)
    (i : Nat) (hoff : DriverTrace.blockOffset (i + 1) < 2 ^ 256)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    (DriverTrace.gasSteps_increment s input i hoff hcode hfork hrun hnp).cost +
        MachineState.memCost s.activeWords.toNat =
      26 + MachineState.memCost s.activeWords.toNat := by
  have hmeter := Challenge.EvmProof.Meter.runLocatedBlock_cost_static_potential
    DriverTrace.incrementPath (DriverTrace.run_increment s input i hoff hcode hrun)
    (by simpa [DriverTrace.compressReturned, State.fork] using hfork)
    (by
      intro located hmem q hq
      simp [DriverTrace.incrementPath] at hmem
      rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [Challenge.EvmProof.Meter.instrCostWithoutMemory,
          Challenge.EvmProof.Meter.instrStaticCost, hq])
  change Challenge.EvmProof.Stepper.runLocatedBlockCost DriverTrace.incrementPath
      (DriverTrace.compressReturned s input i) +
        MachineState.memCost s.activeWords.toNat = _
  simpa [Challenge.EvmProof.Meter.runLocatedBlockStaticCost,
    Challenge.EvmProof.Meter.instrStaticCost, Gas.baseCost,
    DriverTrace.incrementPath, DriverTrace.compressReturned,
    DriverTrace.afterIteration, DriverTrace.loopAt] using hmeter

/-- Non-memory work of the compression call itself.  The enclosing driver
adds `26 + 23 + 26 = 75`, producing the schedule's `148364` per block. -/
def compressionWork : Nat := 148289

def blockWork : Nat := 148364

theorem blockWork_eq : blockWork = 26 + 23 + compressionWork + 26 := by
  rfl

theorem iteration_cost_potential (s next : State) (input : ByteArray)
    (hfit : CalldataFits input) (i : Nat) (hi : i < DriverTrace.blockCount input)
    (hcodeS : s.executionEnv.code = referenceBytecode)
    (hforkS : s.fork = .Osaka) (hrunS : s.halt = .Running)
    (hnpS : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hcodeNext : next.executionEnv.code = referenceBytecode)
    (hforkNext : next.fork = .Osaka) (hrunNext : next.halt = .Running)
    (hnpNext : Precompile.isPrecompile next.executionEnv.fork
      next.executionEnv.codeAddr = false)
    (compress : GasSteps (DriverTrace.compressEntry s input i)
      (DriverTrace.compressReturned next input i))
    (hcompress : compress.cost + MachineState.memCost s.activeWords.toNat =
      compressionWork + MachineState.memCost next.activeWords.toNat) :
    (DriverTrace.gasSteps_iteration_of_compress s next input hfit i hi
      hcodeS hforkS hrunS hnpS hcodeNext hforkNext hrunNext hnpNext
      compress).cost + MachineState.memCost s.activeWords.toNat =
        blockWork + MachineState.memCost next.activeWords.toNat := by
  have hcondition := condition_cost_potential s input hfit i hi hcodeS
    hforkS hrunS hnpS
  have hcall := call_cost_potential s input hfit i hi hcodeS hforkS hrunS hnpS
  have hpadded : Padding.paddedLength input.size < 2 ^ 256 := by
    have hlt := Padding.paddedLength_lt input.size
    unfold CalldataFits at hfit
    norm_num at hfit ⊢
    omega
  have heq := DriverTrace.paddedLength_eq_blockCount input
  have hoff : DriverTrace.blockOffset (i + 1) < 2 ^ 256 := by
    unfold DriverTrace.blockOffset
    omega
  have hincrement := increment_cost_potential next input i hoff hcodeNext
    hforkNext hrunNext hnpNext
  simp only [DriverTrace.gasSteps_iteration_of_compress,
    Challenge.EvmProof.GasSteps.trans_cost]
  unfold blockWork compressionWork at *
  omega

def loopTrace (input : ByteArray) (hfit : CalldataFits input)
    (seam : DirectCorrect.CompressionSeam input) :
    GasSteps (DriverTrace.loopAt (seam.states 0) input 0)
      (DriverTrace.loopAt
        (seam.states (DriverTrace.blockCount input)) input
        (DriverTrace.blockCount input)) :=
  DriverTrace.gasSteps_loop_of_compress seam.states input hfit seam.code
    seam.fork seam.running seam.noPrecompile seam.compress

/-- The whole driver loop telescopes to one fixed work charge per padded
block plus the final memory potential. -/
theorem loopTrace_cost_potential (input : ByteArray)
    (hfit : CalldataFits input) (seam : DirectCorrect.CompressionSeam input)
    (hcompress : ∀ i (hi : i < DriverTrace.blockCount input),
      (seam.compress i hi).cost +
          MachineState.memCost (seam.states i).activeWords.toNat =
        compressionWork +
          MachineState.memCost (seam.states (i + 1)).activeWords.toNat) :
    (loopTrace input hfit seam).cost +
        MachineState.memCost (seam.states 0).activeWords.toNat =
      DriverTrace.blockCount input * blockWork +
        MachineState.memCost
          (seam.states (DriverTrace.blockCount input)).activeWords.toNat := by
  unfold loopTrace DriverTrace.gasSteps_loop_of_compress
  apply Challenge.EvmProof.Meter.iterateBounded_cost_potential_add
  intro i hi
  simpa [DriverTrace.loopAt] using
    iteration_cost_potential (seam.states i) (seam.states (i + 1)) input
      hfit i hi (seam.code i (by omega)) (seam.fork i (by omega))
      (seam.running i (by omega)) (seam.noPrecompile i (by omega))
      (seam.code (i + 1) (by omega)) (seam.fork (i + 1) (by omega))
      (seam.running (i + 1) (by omega))
      (seam.noPrecompile (i + 1) (by omega)) (seam.compress i hi)
      (hcompress i hi)

def paddingWork : Nat := 1212

/-- Driver setup/final test plus the complete five-word output routine:
`3 + 26 + 2636`.  The last summand is exposed path-by-path in `OutputGas`. -/
def framingWork : Nat := 2665

theorem fixedWork_eq : paddingWork + framingWork = 3877 := by
  rfl

/-- Cost facts delivered by the concrete schedule/round/compression trace.
The statement is potential-based, so all memory expansion telescopes instead
of requiring a first-block special case. -/
structure CompressionCostFacts (input : ByteArray)
    (seam : DirectCorrect.CompressionSeam input) : Prop where
  potential : ∀ i (hi : i < DriverTrace.blockCount input),
    (seam.compress i hi).cost +
        MachineState.memCost (seam.states i).activeWords.toNat =
      compressionWork +
        MachineState.memCost (seam.states (i + 1)).activeWords.toNat

/-- Narrow import interface for traces still private to `DirectCorrect` and
the independent padding-gas lane.  No compression or driver-loop arithmetic
is assumed here. -/
structure OuterCostFacts (input : ByteArray) (hfit : CalldataFits input)
    (seam : DirectCorrect.CompressionSeam input) : Prop where
  padding : (PaddingTrace.gasSteps_pad input hfit).cost =
    paddingWork + 3 * GasCost.calldataWords input.size +
      MachineState.memCost (64 + 2 * DriverTrace.blockCount input)
  initialActive : (seam.states 0).activeWords.toNat =
    64 + 2 * DriverTrace.blockCount input
  finalActive :
    (seam.states (DriverTrace.blockCount input)).activeWords.toNat =
      GasCost.finalActiveWords input.size
  framing : (DirectCorrect.fullTrace input hfit seam).cost =
    (PaddingTrace.gasSteps_pad input hfit).cost +
      (loopTrace input hfit seam).cost + framingWork

theorem driverBlockCount_eq_gasBlockCount (input : ByteArray) :
    DriverTrace.blockCount input = GasCost.blockCount input.size := by
  simp [DriverTrace.blockCount, GasCost.blockCount, Padding.paddedLength]

/-- Exact cost of the same `fullTrace` certificate used by functional
correctness. -/
theorem fullTrace_cost (input : ByteArray) (hfit : CalldataFits input)
    (seam : DirectCorrect.CompressionSeam input)
    (compression : CompressionCostFacts input seam)
    (outer : OuterCostFacts input hfit seam) :
    (DirectCorrect.fullTrace input hfit seam).cost =
      GasCost.referenceGas input := by
  have hloop := loopTrace_cost_potential input hfit seam compression.potential
  rw [outer.initialActive, outer.finalActive] at hloop
  rw [outer.framing, outer.padding]
  unfold GasCost.referenceGas GasCost.referenceGasForSize
  unfold GasCost.finalActiveWords at hloop ⊢
  rw [← driverBlockCount_eq_gasBlockCount input] at hloop ⊢
  unfold paddingWork framingWork
  unfold blockWork at hloop
  omega

/-- With concrete compression and outer cost facts installed, this discharges
the exact-cost premise of `DirectCorrect`.  The inferred remaining argument is
its already-separated functional output theorem. -/
noncomputable def correctWithSchedule
    (seam : ∀ (input : ByteArray), CalldataFits input →
      DirectCorrect.CompressionSeam input)
    (compression : ∀ (input : ByteArray) (hfit : CalldataFits input),
      CompressionCostFacts input (seam input hfit))
    (outer : ∀ (input : ByteArray) (hfit : CalldataFits input),
      OuterCostFacts input hfit (seam input hfit)) :=
  DirectCorrect.correctWithSchedule_of_compression seam
    (fun input hfit => fullTrace_cost input hfit (seam input hfit)
      (compression input hfit) (outer input hfit))

noncomputable def correct
    (seam : ∀ (input : ByteArray), CalldataFits input →
      DirectCorrect.CompressionSeam input)
    (compression : ∀ (input : ByteArray) (hfit : CalldataFits input),
      CompressionCostFacts input (seam input hfit))
    (outer : ∀ (input : ByteArray) (hfit : CalldataFits input),
      OuterCostFacts input hfit (seam input hfit)) :=
  DirectCorrect.correct_of_compression seam
    (fun input hfit => fullTrace_cost input hfit (seam input hfit)
      (compression input hfit) (outer input hfit))

end Challenge.Ripemd160.Reference.Proofs.Bytecode.ExactGasBridge
