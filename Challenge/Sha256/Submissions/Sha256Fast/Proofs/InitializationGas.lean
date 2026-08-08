import Challenge.Sha256.Submissions.Sha256Fast.Proofs.InitializationCorrect
import Challenge.EvmProof.FixedPathGas

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

namespace Challenge.Sha256.Submissions.Sha256Fast.Proofs.InitializationGas

open EvmSemantics EvmSemantics.EVM EvmSemantics.Crypto
open Challenge.EvmProof Challenge.EvmProof.Stepper
open InitializationCorrect

attribute [local simp] Challenge.EvmProof.Word.word_toNat_ofNat

private theorem stateCode (s q : State) (hq : q.executionEnv = s.executionEnv)
    (hcode : s.executionEnv.code = Loop.bytes) :
    q.executionEnv.code = Loop.bytes := by rw [hq]; exact hcode

private theorem stateFork (s q : State) (hq : q.executionEnv = s.executionEnv)
    (hfork : s.fork = .Osaka) : q.fork = .Osaka := by
  change q.executionEnv.fork = .Osaka
  rw [hq]
  exact hfork

private theorem stateRun (s q : State) (hq : q.halt = s.halt)
    (hrun : s.halt = .Running) : q.halt = .Running := by rw [hq, hrun]

private theorem stateNp (s q : State) (hq : q.executionEnv = s.executionEnv)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Precompile.isPrecompileWithConfig q.executionEnv.precompileConfig
      q.executionEnv.fork q.executionEnv.codeAddr = false := by rw [hq]; exact hnp

private noncomputable def growingTrace {s t : State}
    (path : List (Located Loop.art .Osaka))
    (work cost startWords endWords : Nat)
    (hcost : cost + MachineState.memCost startWords =
      work + MachineState.memCost endWords)
    (hcode : s.executionEnv.code = Loop.bytes)
    (hresult : runLocatedBlock path s = some t) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hfork : s.fork = .Osaka) (hstart : s.activeWords.toNat = startWords)
    (hend : t.activeWords.toNat = endWords)
    (hfree : path.all (fun q => Challenge.EvmProof.Meter.CopyFree
      q.instruction) = true)
    (hwork : Challenge.EvmProof.Meter.runLocatedBlockStaticCost path = work) :
    GasSteps s t :=
  Challenge.EvmProof.FixedPathGas.traceGrowing path work cost startWords endWords
    hfree hwork hcost (by simpa [Loop.art] using hcode) hfork hresult hrun hnp
    hstart hend

private structure Context (s : State) (n : UInt256) : Prop where
  code : s.executionEnv.code = Loop.bytes
  fork : s.fork = .Osaka
  run : s.halt = .Running
  pc : s.pc = UInt256.ofNat 0
  activeWords : s.activeWords = UInt256.ofNat 0
  stack : s.stack = []
  calldataSize : UInt256.ofNat s.executionEnv.calldata.size = n
  notPrecompile : Precompile.isPrecompileWithConfig
    s.executionEnv.precompileConfig s.executionEnv.fork
    s.executionEnv.codeAddr = false

private noncomputable def entryTrace (s : State) (n : UInt256)
    (c : Context s n) : GasSteps s (entryState s) :=
  growingTrace DriverBlocks.initializeEntryPath 11 11 0 0
    (by norm_num [MachineState.memCost]) c.code
    (by simpa [entryState] using
      (DriverBlocks.run_initializeEntry s c.code (by decide) c.run c.pc c.stack))
    c.run c.notPrecompile c.fork
    (by rw [c.activeWords, Challenge.EvmProof.Word.word_toNat_ofNat]; norm_num)
    (by change s.activeWords.toNat = 0
        rw [c.activeWords, Challenge.EvmProof.Word.word_toNat_ofNat]
        norm_num) (by rfl) (by rfl)

private noncomputable def hashTrace (s : State) (n : UInt256)
    (c : Context s n) :
    GasSteps (entryState s) (hashState (entryState s) n) :=
  growingTrace DriverBlocks.initializeHashPath 75 102 0 9
    (by norm_num [MachineState.memCost])
    (stateCode s _ rfl c.code)
    (by simpa [entryState, hashState] using
      (DriverBlocks.run_initializeHash (entryState s) n
        (stateRun s _ (Eq.refl _) c.run) (Eq.refl _) c.activeWords c.stack
        c.calldataSize))
    (stateRun s _ (Eq.refl _) c.run)
    (stateNp s _ (Eq.refl _) c.notPrecompile)
    (stateFork s _ (Eq.refl _) c.fork)
    (by change s.activeWords.toNat = 0
        rw [c.activeWords, Challenge.EvmProof.Word.word_toNat_ofNat]
        norm_num)
    (by simp [hashState]) (by rfl) (by rfl)

private noncomputable def c0Trace (s : State) (n : UInt256)
    (c : Context s n) : GasSteps (hashState (entryState s) n) (c0 s n) :=
  growingTrace DriverBlocks.initializeConstants0Path 72 310 9 84
    (by norm_num [MachineState.memCost]) (stateCode s _ rfl c.code)
    (by simpa [c0, constantState] using
      (DriverBlocks.run_initializeConstants0 (hashState (entryState s) n) n
        (stateRun s _ (Eq.refl _) c.run) (Eq.refl _) (Eq.refl _) (Eq.refl _)))
    (stateRun s _ (Eq.refl _) c.run)
    (stateNp s _ (Eq.refl _) c.notPrecompile)
    (stateFork s _ (Eq.refl _) c.fork) (by simp [hashState])
    (by simp [c0, constantState]) (by rfl) (by rfl)

private noncomputable def c1Trace (s : State) (n : UInt256)
    (c : Context s n) : GasSteps (c0 s n) (c1 s n) :=
  growingTrace DriverBlocks.initializeConstants1Path 72 99 84 92
    (by norm_num [MachineState.memCost]) (stateCode s _ rfl c.code)
    (by simpa [c1, constantState] using
      (DriverBlocks.run_initializeConstants1 (c0 s n) n
        (stateRun s _ (Eq.refl _) c.run) (Eq.refl _) (Eq.refl _) (Eq.refl _)))
    (stateRun s _ (Eq.refl _) c.run)
    (stateNp s _ (Eq.refl _) c.notPrecompile)
    (stateFork s _ (Eq.refl _) c.fork) (by simp [c0, constantState])
    (by simp [c1, constantState]) (by rfl) (by rfl)

private noncomputable def c2Trace (s : State) (n : UInt256)
    (c : Context s n) : GasSteps (c1 s n) (c2 s n) :=
  growingTrace DriverBlocks.initializeConstants2Path 72 99 92 100
    (by norm_num [MachineState.memCost]) (stateCode s _ rfl c.code)
    (by simpa [c2, constantState] using
      (DriverBlocks.run_initializeConstants2 (c1 s n) n
        (stateRun s _ (Eq.refl _) c.run) (Eq.refl _) (Eq.refl _) (Eq.refl _)))
    (stateRun s _ (Eq.refl _) c.run)
    (stateNp s _ (Eq.refl _) c.notPrecompile)
    (stateFork s _ (Eq.refl _) c.fork) (by simp [c1, constantState])
    (by simp [c2, constantState]) (by rfl) (by rfl)

private noncomputable def c3Trace (s : State) (n : UInt256)
    (c : Context s n) : GasSteps (c2 s n) (c3 s n) :=
  growingTrace DriverBlocks.initializeConstants3Path 72 99 100 108
    (by norm_num [MachineState.memCost]) (stateCode s _ rfl c.code)
    (by simpa [c3, constantState] using
      (DriverBlocks.run_initializeConstants3 (c2 s n) n
        (stateRun s _ (Eq.refl _) c.run) (Eq.refl _) (Eq.refl _) (Eq.refl _)))
    (stateRun s _ (Eq.refl _) c.run)
    (stateNp s _ (Eq.refl _) c.notPrecompile)
    (stateFork s _ (Eq.refl _) c.fork) (by simp [c2, constantState])
    (by simp [c3, constantState]) (by rfl) (by rfl)

private noncomputable def c4Trace (s : State) (n : UInt256)
    (c : Context s n) : GasSteps (c3 s n) (c4 s n) :=
  growingTrace DriverBlocks.initializeConstants4Path 72 100 108 116
    (by norm_num [MachineState.memCost]) (stateCode s _ rfl c.code)
    (by simpa [c4, constantState] using
      (DriverBlocks.run_initializeConstants4 (c3 s n) n
        (stateRun s _ (Eq.refl _) c.run) (Eq.refl _) (Eq.refl _) (Eq.refl _)))
    (stateRun s _ (Eq.refl _) c.run)
    (stateNp s _ (Eq.refl _) c.notPrecompile)
    (stateFork s _ (Eq.refl _) c.fork) (by simp [c3, constantState])
    (by simp [c4, constantState]) (by rfl) (by rfl)

private noncomputable def c5Trace (s : State) (n : UInt256)
    (c : Context s n) : GasSteps (c4 s n) (c5 s n) :=
  growingTrace DriverBlocks.initializeConstants5Path 72 100 116 124
    (by norm_num [MachineState.memCost]) (stateCode s _ rfl c.code)
    (by simpa [c5, constantState] using
      (DriverBlocks.run_initializeConstants5 (c4 s n) n
        (stateRun s _ (Eq.refl _) c.run) (Eq.refl _) (Eq.refl _) (Eq.refl _)))
    (stateRun s _ (Eq.refl _) c.run)
    (stateNp s _ (Eq.refl _) c.notPrecompile)
    (stateFork s _ (Eq.refl _) c.fork) (by simp [c4, constantState])
    (by simp [c5, constantState]) (by rfl) (by rfl)

private noncomputable def c6Trace (s : State) (n : UInt256)
    (c : Context s n) : GasSteps (c5 s n) (c6 s n) :=
  growingTrace DriverBlocks.initializeConstants6Path 72 100 124 132
    (by norm_num [MachineState.memCost]) (stateCode s _ rfl c.code)
    (by simpa [c6, constantState] using
      (DriverBlocks.run_initializeConstants6 (c5 s n) n
        (stateRun s _ (Eq.refl _) c.run) (Eq.refl _) (Eq.refl _) (Eq.refl _)))
    (stateRun s _ (Eq.refl _) c.run)
    (stateNp s _ (Eq.refl _) c.notPrecompile)
    (stateFork s _ (Eq.refl _) c.fork) (by simp [c5, constantState])
    (by simp [c6, constantState]) (by rfl) (by rfl)

private noncomputable def c7Trace (s : State) (n : UInt256)
    (c : Context s n) : GasSteps (c6 s n) (c7 s n) :=
  growingTrace DriverBlocks.initializeConstants7Path 72 100 132 140
    (by norm_num [MachineState.memCost]) (stateCode s _ rfl c.code)
    (by simpa [c7, constantState] using
      (DriverBlocks.run_initializeConstants7 (c6 s n) n
        (stateRun s _ (Eq.refl _) c.run) (Eq.refl _) (Eq.refl _) (Eq.refl _)))
    (stateRun s _ (Eq.refl _) c.run)
    (stateNp s _ (Eq.refl _) c.notPrecompile)
    (stateFork s _ (Eq.refl _) c.fork) (by simp [c6, constantState])
    (by simp [c7, constantState]) (by rfl) (by rfl)

private noncomputable def driverTrace (s : State) (n : UInt256)
    (c : Context s n) : GasSteps (c7 s n) (finalState s n) :=
  growingTrace DriverBlocks.initializeDriverPath 35 35 140 140
    (by norm_num [MachineState.memCost]) (stateCode s _ rfl c.code)
    (by simpa [finalState, endWord, remainder] using
      (DriverBlocks.run_initializeDriver (c7 s n) n
        (stateRun s _ (Eq.refl _) c.run) (Eq.refl _) (Eq.refl _) (Eq.refl _)))
    (stateRun s _ (Eq.refl _) c.run)
    (stateNp s _ (Eq.refl _) c.notPrecompile)
    (stateFork s _ (Eq.refl _) c.fork) (by simp [c7, constantState])
    (by rw [show (finalState s n).activeWords = UInt256.ofNat 140 by rfl,
      Challenge.EvmProof.Word.word_toNat_ofNat]; norm_num)
    (by rfl) (by rfl)

noncomputable def gasSteps_initialize (s : State) (n : UInt256)
    (hcode : s.executionEnv.code = Loop.bytes) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running) (hpc : s.pc = UInt256.ofNat 0)
    (haw : s.activeWords = UInt256.ofNat 0) (hstack : s.stack = [])
    (hn : UInt256.ofNat s.executionEnv.calldata.size = n)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps s (finalState s n) :=
  let c : Context s n := ⟨hcode, hfork, hrun, hpc, haw, hstack, hn, hnp⟩
  let ge := entryTrace s n c
  let gh := hashTrace s n c
  let g0 := c0Trace s n c
  let g1 := c1Trace s n c
  let g2 := c2Trace s n c
  let g3 := c3Trace s n c
  let g4 := c4Trace s n c
  let g5 := c5Trace s n c
  let g6 := c6Trace s n c
  let g7 := c7Trace s n c
  let gd := driverTrace s n c
  GasSteps.transKnown ge
    (GasSteps.transKnown gh
      (GasSteps.transKnown g0
        (GasSteps.transKnown g1
          (GasSteps.transKnown g2
            (GasSteps.transKnown g3
              (GasSteps.transKnown g4
                (GasSteps.transKnown g5
                  (GasSteps.transKnown g6
                    (GasSteps.transKnown g7 gd 100 35
                      (by simp [g7, c7Trace, growingTrace])
                      (by simp [gd, driverTrace, growingTrace]))
                    100 135 (by simp [g6, c6Trace, growingTrace]) rfl)
                  100 235 (by simp [g5, c5Trace, growingTrace]) rfl)
                100 335 (by simp [g4, c4Trace, growingTrace]) rfl)
              99 435 (by simp [g3, c3Trace, growingTrace]) rfl)
            99 534 (by simp [g2, c2Trace, growingTrace]) rfl)
          99 633 (by simp [g1, c1Trace, growingTrace]) rfl)
        310 732 (by simp [g0, c0Trace, growingTrace]) rfl)
      102 1042 (by simp [gh, hashTrace, growingTrace]) rfl)
    11 1144 (by simp [ge, entryTrace, growingTrace]) rfl

@[simp] theorem gasSteps_initialize_cost (s : State) (n : UInt256)
    (hcode : s.executionEnv.code = Loop.bytes) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running) (hpc : s.pc = UInt256.ofNat 0)
    (haw : s.activeWords = UInt256.ofNat 0) (hstack : s.stack = [])
    (hn : UInt256.ofNat s.executionEnv.calldata.size = n)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    (gasSteps_initialize s n hcode hfork hrun hpc haw hstack hn hnp).cost =
      1155 := by
  simp [gasSteps_initialize, entryTrace, hashTrace, c0Trace, c1Trace, c2Trace,
    c3Trace, c4Trace, c5Trace, c6Trace, c7Trace, driverTrace, growingTrace]

end Challenge.Sha256.Submissions.Sha256Fast.Proofs.InitializationGas
