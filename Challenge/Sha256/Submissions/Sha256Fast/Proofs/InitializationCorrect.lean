import Challenge.Sha256.Submissions.Sha256Fast.Proofs.CompressionCorrect

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

namespace Challenge.Sha256.Submissions.Sha256Fast.Proofs.InitializationCorrect

open EvmSemantics EvmSemantics.EVM
open Challenge.EvmProof Challenge.EvmProof.Stepper
open MemoryCorrect

def endWord (n : UInt256) : UInt256 :=
  UInt256.shiftLeft (UInt256.shiftRight n (UInt256.ofNat 6)) (UInt256.ofNat 6)

def remainder (n : UInt256) : UInt256 := UInt256.land (UInt256.ofNat 63) n

noncomputable def entryState (s : State) : State :=
  { s with pc := UInt256.ofNat 1804 }

noncomputable def hashState (s : State) (n : UInt256) : State :=
  { s with
    pc := UInt256.ofNat 1871
    activeWords := UInt256.ofNat 9
    memory := DriverBlocks.hashMemory s.memory
    stack := [n] }

noncomputable def constantState (index : Nat) (s : State) (n : UInt256) : State :=
  match index with
  | 0 => { s with
      pc := UInt256.ofNat 1943
      activeWords := UInt256.ofNat 84
      memory := DriverBlocks.constantMemory0 s.memory
      stack := [n] }
  | 1 => { s with
      pc := UInt256.ofNat 2015
      activeWords := UInt256.ofNat 92
      memory := DriverBlocks.constantMemory1 s.memory
      stack := [n] }
  | 2 => { s with
      pc := UInt256.ofNat 2087
      activeWords := UInt256.ofNat 100
      memory := DriverBlocks.constantMemory2 s.memory
      stack := [n] }
  | 3 => { s with
      pc := UInt256.ofNat 2159
      activeWords := UInt256.ofNat 108
      memory := DriverBlocks.constantMemory3 s.memory
      stack := [n] }
  | 4 => { s with
      pc := UInt256.ofNat 2231
      activeWords := UInt256.ofNat 116
      memory := DriverBlocks.constantMemory4 s.memory
      stack := [n] }
  | 5 => { s with
      pc := UInt256.ofNat 2303
      activeWords := UInt256.ofNat 124
      memory := DriverBlocks.constantMemory5 s.memory
      stack := [n] }
  | 6 => { s with
      pc := UInt256.ofNat 2375
      activeWords := UInt256.ofNat 132
      memory := DriverBlocks.constantMemory6 s.memory
      stack := [n] }
  | _ => { s with
      pc := UInt256.ofNat 2447
      activeWords := UInt256.ofNat 140
      memory := DriverBlocks.constantMemory7 s.memory
      stack := [n] }

noncomputable def c0 (s : State) (n : UInt256) :=
  constantState 0 (hashState (entryState s) n) n
noncomputable def c1 (s : State) (n : UInt256) := constantState 1 (c0 s n) n
noncomputable def c2 (s : State) (n : UInt256) := constantState 2 (c1 s n) n
noncomputable def c3 (s : State) (n : UInt256) := constantState 3 (c2 s n) n
noncomputable def c4 (s : State) (n : UInt256) := constantState 4 (c3 s n) n
noncomputable def c5 (s : State) (n : UInt256) := constantState 5 (c4 s n) n
noncomputable def c6 (s : State) (n : UInt256) := constantState 6 (c5 s n) n
noncomputable def c7 (s : State) (n : UInt256) := constantState 7 (c6 s n) n

noncomputable def finalState (s : State) (n : UInt256) : State :=
  { c7 s n with
    pc := UInt256.ofNat 2464
    stack := [UInt256.ofNat 2491, UInt256.isZero (endWord n),
      UInt256.ofNat 0, endWord n, remainder n, n] }

private theorem stateCode (s u : State) (hu : u.executionEnv = s.executionEnv)
    (hcode : s.executionEnv.code = Loop.bytes) :
    u.executionEnv.code = Loop.art.code := by
  rw [hu]
  simpa [Loop.art] using hcode

private theorem stateCodeBytes (s u : State)
    (hu : u.executionEnv = s.executionEnv)
    (hcode : s.executionEnv.code = Loop.bytes) :
    u.executionEnv.code = Loop.bytes := by rw [hu]; exact hcode

private theorem stateFork (s u : State) (hu : u.executionEnv = s.executionEnv)
    (hfork : s.fork = .Osaka) : u.fork = .Osaka := by
  change u.executionEnv.fork = .Osaka
  rw [hu]
  exact hfork

private theorem stateNp (s u : State) (hu : u.executionEnv = s.executionEnv)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Precompile.isPrecompileWithConfig u.executionEnv.precompileConfig
      u.executionEnv.fork u.executionEnv.codeAddr = false := by
  rw [hu]
  exact hnp

private theorem stateRun (s u : State) (hu : u.halt = s.halt)
    (hrun : s.halt = .Running) : u.halt = .Running := by rw [hu, hrun]

theorem gasSteps_entry (s : State)
    (hcode : s.executionEnv.code = Loop.bytes) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running) (hpc : s.pc = UInt256.ofNat 0)
    (hstack : s.stack = [])
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Nonempty (GasSteps s (entryState s)) := by
  refine ⟨?_⟩
  apply runLocatedBlock_sound Loop.art .Osaka DriverBlocks.initializeEntryPath
    (by simpa [Loop.art] using hcode) hfork
  · simpa [entryState] using DriverBlocks.run_initializeEntry s hcode
      (by decide) hrun hpc hstack
  · exact hrun
  · exact hnp

theorem gasSteps_hash (s : State) (n : UInt256)
    (haw : s.activeWords = UInt256.ofNat 0) (hstack : s.stack = [])
    (hn : UInt256.ofNat s.executionEnv.calldata.size = n)
    (hcode : s.executionEnv.code = Loop.bytes) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Nonempty (GasSteps (entryState s) (hashState (entryState s) n)) := by
  refine ⟨?_⟩
  let e := entryState s
  apply runLocatedBlock_sound Loop.art .Osaka DriverBlocks.initializeHashPath
    (stateCode s e (by rfl) hcode) (stateFork s e (by rfl) hfork)
  · simpa [e, entryState, hashState] using
      DriverBlocks.run_initializeHash e n
        (stateRun s e (by rfl) hrun) rfl (by simpa [e, entryState] using haw)
        (by simpa [e, entryState] using hstack)
        (by simpa [e, entryState] using hn)
  · exact stateRun s e (by rfl) hrun
  · exact stateNp s e (by rfl) hnp

private theorem gasSteps_c0 (s : State) (n : UInt256)
    (hcode : s.executionEnv.code = Loop.bytes) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running) (hpc : s.pc = UInt256.ofNat 1871)
    (haw : s.activeWords = UInt256.ofNat 9) (hstack : s.stack = [n])
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Nonempty (GasSteps s (constantState 0 s n)) := by
  exact ⟨runLocatedBlock_sound Loop.art .Osaka DriverBlocks.initializeConstants0Path
    (by simpa [Loop.art] using hcode) hfork
    (DriverBlocks.run_initializeConstants0 s n hrun hpc haw hstack) hrun hnp⟩

private theorem gasSteps_c1 (s : State) (n : UInt256)
    (hcode : s.executionEnv.code = Loop.bytes) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running) (hpc : s.pc = UInt256.ofNat 1943)
    (haw : s.activeWords = UInt256.ofNat 84) (hstack : s.stack = [n])
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Nonempty (GasSteps s (constantState 1 s n)) := by
  exact ⟨runLocatedBlock_sound Loop.art .Osaka DriverBlocks.initializeConstants1Path
    (by simpa [Loop.art] using hcode) hfork
    (DriverBlocks.run_initializeConstants1 s n hrun hpc haw hstack) hrun hnp⟩

private theorem gasSteps_c2 (s : State) (n : UInt256)
    (hcode : s.executionEnv.code = Loop.bytes) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running) (hpc : s.pc = UInt256.ofNat 2015)
    (haw : s.activeWords = UInt256.ofNat 92) (hstack : s.stack = [n])
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Nonempty (GasSteps s (constantState 2 s n)) := by
  exact ⟨runLocatedBlock_sound Loop.art .Osaka DriverBlocks.initializeConstants2Path
    (by simpa [Loop.art] using hcode) hfork
    (DriverBlocks.run_initializeConstants2 s n hrun hpc haw hstack) hrun hnp⟩

private theorem gasSteps_c3 (s : State) (n : UInt256)
    (hcode : s.executionEnv.code = Loop.bytes) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running) (hpc : s.pc = UInt256.ofNat 2087)
    (haw : s.activeWords = UInt256.ofNat 100) (hstack : s.stack = [n])
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Nonempty (GasSteps s (constantState 3 s n)) := by
  exact ⟨runLocatedBlock_sound Loop.art .Osaka DriverBlocks.initializeConstants3Path
    (by simpa [Loop.art] using hcode) hfork
    (DriverBlocks.run_initializeConstants3 s n hrun hpc haw hstack) hrun hnp⟩

private theorem gasSteps_c4 (s : State) (n : UInt256)
    (hcode : s.executionEnv.code = Loop.bytes) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running) (hpc : s.pc = UInt256.ofNat 2159)
    (haw : s.activeWords = UInt256.ofNat 108) (hstack : s.stack = [n])
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Nonempty (GasSteps s (constantState 4 s n)) := by
  exact ⟨runLocatedBlock_sound Loop.art .Osaka DriverBlocks.initializeConstants4Path
    (by simpa [Loop.art] using hcode) hfork
    (DriverBlocks.run_initializeConstants4 s n hrun hpc haw hstack) hrun hnp⟩

private theorem gasSteps_c5 (s : State) (n : UInt256)
    (hcode : s.executionEnv.code = Loop.bytes) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running) (hpc : s.pc = UInt256.ofNat 2231)
    (haw : s.activeWords = UInt256.ofNat 116) (hstack : s.stack = [n])
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Nonempty (GasSteps s (constantState 5 s n)) := by
  exact ⟨runLocatedBlock_sound Loop.art .Osaka DriverBlocks.initializeConstants5Path
    (by simpa [Loop.art] using hcode) hfork
    (DriverBlocks.run_initializeConstants5 s n hrun hpc haw hstack) hrun hnp⟩

private theorem gasSteps_c6 (s : State) (n : UInt256)
    (hcode : s.executionEnv.code = Loop.bytes) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running) (hpc : s.pc = UInt256.ofNat 2303)
    (haw : s.activeWords = UInt256.ofNat 124) (hstack : s.stack = [n])
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Nonempty (GasSteps s (constantState 6 s n)) := by
  exact ⟨runLocatedBlock_sound Loop.art .Osaka DriverBlocks.initializeConstants6Path
    (by simpa [Loop.art] using hcode) hfork
    (DriverBlocks.run_initializeConstants6 s n hrun hpc haw hstack) hrun hnp⟩

private theorem gasSteps_c7 (s : State) (n : UInt256)
    (hcode : s.executionEnv.code = Loop.bytes) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running) (hpc : s.pc = UInt256.ofNat 2375)
    (haw : s.activeWords = UInt256.ofNat 132) (hstack : s.stack = [n])
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Nonempty (GasSteps s (constantState 7 s n)) := by
  exact ⟨runLocatedBlock_sound Loop.art .Osaka DriverBlocks.initializeConstants7Path
    (by simpa [Loop.art] using hcode) hfork
    (DriverBlocks.run_initializeConstants7 s n hrun hpc haw hstack) hrun hnp⟩

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

private theorem toHash_exists (s : State) (n : UInt256) (c : Context s n) :
    Nonempty (GasSteps s (hashState (entryState s) n)) :=
  ⟨(Classical.choice
      (gasSteps_entry s c.code c.fork c.run c.pc c.stack c.notPrecompile)).trans
    (Classical.choice (gasSteps_hash s n c.activeWords c.stack c.calldataSize
      c.code c.fork c.run c.notPrecompile))⟩

private noncomputable def toHash (s : State) (n : UInt256) (c : Context s n) :
    GasSteps s (hashState (entryState s) n) :=
  Classical.choice (toHash_exists s n c)

private theorem toC0_exists (s : State) (n : UInt256) (c : Context s n) :
    Nonempty (GasSteps s (c0 s n)) :=
  ⟨(toHash s n c).trans (Classical.choice (gasSteps_c0 (hashState (entryState s) n) n
    (stateCodeBytes s _ (by rfl) c.code) (stateFork s _ (by rfl) c.fork)
    (stateRun s _ (by rfl) c.run) rfl rfl rfl
    (stateNp s _ (by rfl) c.notPrecompile)))⟩

private noncomputable def toC0 (s : State) (n : UInt256) (c : Context s n) :
    GasSteps s (c0 s n) := Classical.choice (toC0_exists s n c)

private theorem toC1_exists (s : State) (n : UInt256) (c : Context s n) :
    Nonempty (GasSteps s (c1 s n)) :=
  ⟨(toC0 s n c).trans (Classical.choice (gasSteps_c1 (c0 s n) n
    (stateCodeBytes s _ (by rfl) c.code) (stateFork s _ (by rfl) c.fork)
    (stateRun s _ (by rfl) c.run) rfl rfl rfl
    (stateNp s _ (by rfl) c.notPrecompile)))⟩

private noncomputable def toC1 (s : State) (n : UInt256) (c : Context s n) :
    GasSteps s (c1 s n) := Classical.choice (toC1_exists s n c)

private theorem toC2_exists (s : State) (n : UInt256) (c : Context s n) :
    Nonempty (GasSteps s (c2 s n)) :=
  ⟨(toC1 s n c).trans (Classical.choice (gasSteps_c2 (c1 s n) n
    (stateCodeBytes s _ (by rfl) c.code) (stateFork s _ (by rfl) c.fork)
    (stateRun s _ (by rfl) c.run) rfl rfl rfl
    (stateNp s _ (by rfl) c.notPrecompile)))⟩

private noncomputable def toC2 (s : State) (n : UInt256) (c : Context s n) :
    GasSteps s (c2 s n) := Classical.choice (toC2_exists s n c)

private theorem toC3_exists (s : State) (n : UInt256) (c : Context s n) :
    Nonempty (GasSteps s (c3 s n)) :=
  ⟨(toC2 s n c).trans (Classical.choice (gasSteps_c3 (c2 s n) n
    (stateCodeBytes s _ (by rfl) c.code) (stateFork s _ (by rfl) c.fork)
    (stateRun s _ (by rfl) c.run) rfl rfl rfl
    (stateNp s _ (by rfl) c.notPrecompile)))⟩

private noncomputable def toC3 (s : State) (n : UInt256) (c : Context s n) :
    GasSteps s (c3 s n) := Classical.choice (toC3_exists s n c)

private theorem toC4_exists (s : State) (n : UInt256) (c : Context s n) :
    Nonempty (GasSteps s (c4 s n)) :=
  ⟨(toC3 s n c).trans (Classical.choice (gasSteps_c4 (c3 s n) n
    (stateCodeBytes s _ (by rfl) c.code) (stateFork s _ (by rfl) c.fork)
    (stateRun s _ (by rfl) c.run) rfl rfl rfl
    (stateNp s _ (by rfl) c.notPrecompile)))⟩

private noncomputable def toC4 (s : State) (n : UInt256) (c : Context s n) :
    GasSteps s (c4 s n) := Classical.choice (toC4_exists s n c)

private theorem toC5_exists (s : State) (n : UInt256) (c : Context s n) :
    Nonempty (GasSteps s (c5 s n)) :=
  ⟨(toC4 s n c).trans (Classical.choice (gasSteps_c5 (c4 s n) n
    (stateCodeBytes s _ (by rfl) c.code) (stateFork s _ (by rfl) c.fork)
    (stateRun s _ (by rfl) c.run) rfl rfl rfl
    (stateNp s _ (by rfl) c.notPrecompile)))⟩

private noncomputable def toC5 (s : State) (n : UInt256) (c : Context s n) :
    GasSteps s (c5 s n) := Classical.choice (toC5_exists s n c)

private theorem toC6_exists (s : State) (n : UInt256) (c : Context s n) :
    Nonempty (GasSteps s (c6 s n)) :=
  ⟨(toC5 s n c).trans (Classical.choice (gasSteps_c6 (c5 s n) n
    (stateCodeBytes s _ (by rfl) c.code) (stateFork s _ (by rfl) c.fork)
    (stateRun s _ (by rfl) c.run) rfl rfl rfl
    (stateNp s _ (by rfl) c.notPrecompile)))⟩

private noncomputable def toC6 (s : State) (n : UInt256) (c : Context s n) :
    GasSteps s (c6 s n) := Classical.choice (toC6_exists s n c)

private theorem toC7_exists (s : State) (n : UInt256) (c : Context s n) :
    Nonempty (GasSteps s (c7 s n)) :=
  ⟨(toC6 s n c).trans (Classical.choice (gasSteps_c7 (c6 s n) n
    (stateCodeBytes s _ (by rfl) c.code) (stateFork s _ (by rfl) c.fork)
    (stateRun s _ (by rfl) c.run) rfl rfl rfl
    (stateNp s _ (by rfl) c.notPrecompile)))⟩

private noncomputable def toC7 (s : State) (n : UInt256) (c : Context s n) :
    GasSteps s (c7 s n) := Classical.choice (toC7_exists s n c)

private theorem gasSteps_initialize_exists (s : State) (n : UInt256)
    (hcode : s.executionEnv.code = Loop.bytes) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running) (hpc : s.pc = UInt256.ofNat 0)
    (haw : s.activeWords = UInt256.ofNat 0) (hstack : s.stack = [])
    (hn : UInt256.ofNat s.executionEnv.calldata.size = n)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Nonempty (GasSteps s (finalState s n)) := by
  let c : Context s n := ⟨hcode, hfork, hrun, hpc, haw, hstack, hn, hnp⟩
  have rDriver := DriverBlocks.run_initializeDriver (c7 s n) n
    (stateRun s _ (by rfl) hrun) rfl rfl rfl
  let gd : GasSteps (c7 s n) (finalState s n) :=
    runLocatedBlock_sound Loop.art .Osaka DriverBlocks.initializeDriverPath
      (stateCode s _ (by rfl) hcode) (stateFork s _ (by rfl) hfork)
      (by simpa [finalState, endWord, remainder] using rDriver)
      (stateRun s _ (by rfl) hrun) (stateNp s _ (by rfl) hnp)
  exact ⟨(toC7 s n c).trans gd⟩

noncomputable def gasSteps_initialize (s : State) (n : UInt256)
    (hcode : s.executionEnv.code = Loop.bytes) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running) (hpc : s.pc = UInt256.ofNat 0)
    (haw : s.activeWords = UInt256.ofNat 0) (hstack : s.stack = [])
    (hn : UInt256.ofNat s.executionEnv.calldata.size = n)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps s (finalState s n) :=
  Classical.choice (gasSteps_initialize_exists s n hcode hfork hrun hpc haw
    hstack hn hnp)

end Challenge.Sha256.Submissions.Sha256Fast.Proofs.InitializationCorrect
