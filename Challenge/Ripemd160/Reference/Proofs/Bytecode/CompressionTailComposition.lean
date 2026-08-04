import Challenge.Ripemd160.Reference.Proofs.Bytecode.CompressionTailTrace

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

/-!
# RIPEMD-160 compression-tail composition

This module completes the tail trace with the six cleanup pops and dynamic
return jump, then packages the whole right line and cross-combination as one
`GasSteps` witness.
-/

namespace Challenge.Ripemd160.Reference.Proofs.Bytecode.CompressionTailTrace

open EvmSemantics
open EvmSemantics.EVM
open CompressionTrace
open CompressionRightTrace

def combinationCleaned (s : State) (messageOffset returnDest : UInt256)
    (rest : List UInt256) : State :=
  { combination4 s messageOffset returnDest rest with
      pc := UInt256.ofNat 960, stack := returnDest :: rest }

def combinationReturned (s : State) (messageOffset returnDest : UInt256)
    (rest : List UInt256) : State :=
  { combinationCleaned s messageOffset returnDest rest with
      pc := returnDest, stack := rest }

@[simp] theorem combination4_pc (s : State)
    (messageOffset returnDest : UInt256) (rest : List UInt256) :
    (combination4 s messageOffset returnDest rest).pc = UInt256.ofNat 954 := by
  simp only [combination4]

@[simp] theorem combination4_stack (s : State)
    (messageOffset returnDest : UInt256) (rest : List UInt256) :
    (combination4 s messageOffset returnDest rest).stack =
      let out := tailCombination s
      out.h4 :: out.h3 :: out.h2 :: out.h1 :: out.h0 ::
        messageOffset :: returnDest :: rest := by
  simp only [combination4]

@[simp] theorem combination4_halt (s : State)
    (messageOffset returnDest : UInt256) (rest : List UInt256) :
    (combination4 s messageOffset returnDest rest).halt = s.halt := by
  simp only [combination4, touched4, touched3, touched2, touched1, touched0,
    touchWord]

@[simp] theorem combination4_executionEnv (s : State)
    (messageOffset returnDest : UInt256) (rest : List UInt256) :
    (combination4 s messageOffset returnDest rest).executionEnv =
      s.executionEnv := by
  simp only [combination4, touched4, touched3, touched2, touched1, touched0,
    touchWord]

@[simp] theorem combinationCleaned_pc (s : State)
    (messageOffset returnDest : UInt256) (rest : List UInt256) :
    (combinationCleaned s messageOffset returnDest rest).pc =
      UInt256.ofNat 960 := by rfl

@[simp] theorem combinationCleaned_stack (s : State)
    (messageOffset returnDest : UInt256) (rest : List UInt256) :
    (combinationCleaned s messageOffset returnDest rest).stack =
      returnDest :: rest := by rfl

@[simp] theorem combinationCleaned_halt (s : State)
    (messageOffset returnDest : UInt256) (rest : List UInt256) :
    (combinationCleaned s messageOffset returnDest rest).halt = s.halt := by
  rw [combinationCleaned, combination4_halt]

@[simp] theorem combinationCleaned_executionEnv (s : State)
    (messageOffset returnDest : UInt256) (rest : List UInt256) :
    (combinationCleaned s messageOffset returnDest rest).executionEnv =
      s.executionEnv := by
  rw [combinationCleaned, combination4_executionEnv]

set_option linter.unusedSimpArgs false in
theorem run_combinationPops (s : State)
    (messageOffset returnDest : UInt256) (rest : List UInt256)
    (hstack : rest.length < 970)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock combinationPopsLocated
      (combination4 s messageOffset returnDest rest) =
        some (combinationCleaned s messageOffset returnDest rest) := by
  have hcap (m : Nat) (hm : m ≤ 10) : rest.length + m < 1024 := by omega
  simp (config := { maxSteps := 100000 })
    [combinationPopsLocated, combinationCleanupLocated, combinationLocated,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      combinationCleaned, hrun, hcap,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.add_assoc]

set_option linter.unusedSimpArgs false in
theorem run_combinationJump (s : State)
    (messageOffset returnDest : UInt256) (rest : List UInt256)
    (hstack : rest.length < 970)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hrun : s.halt = .Running)
    (hvalid : Decode.isValidJumpDest referenceBytecode returnDest.toNat = true) :
    Challenge.EvmProof.Stepper.runLocatedBlock combinationJumpLocated
      (combinationCleaned s messageOffset returnDest rest) =
        some (combinationReturned s messageOffset returnDest rest) := by
  have hcap : rest.length + 1 < 1024 := by omega
  simp (config := { maxSteps := 100000 })
    [combinationJumpLocated, combinationCleanupLocated, combinationLocated,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      combinationReturned, hrun, hcode, hvalid, hcap]

@[simp] theorem combination0_executionEnv (s : State)
    (messageOffset returnDest : UInt256) (rest : List UInt256) :
    (combination0 s messageOffset returnDest rest).executionEnv = s.executionEnv := by
  simp only [combination0, touched0, touchWord]

@[simp] theorem combination0_halt (s : State)
    (messageOffset returnDest : UInt256) (rest : List UInt256) :
    (combination0 s messageOffset returnDest rest).halt = s.halt := by
  simp only [combination0, touched0, touchWord]

@[simp] theorem combination1_executionEnv (s : State)
    (messageOffset returnDest : UInt256) (rest : List UInt256) :
    (combination1 s messageOffset returnDest rest).executionEnv = s.executionEnv := by
  simp only [combination1, touched1, touched0, touchWord]

@[simp] theorem combination1_halt (s : State)
    (messageOffset returnDest : UInt256) (rest : List UInt256) :
    (combination1 s messageOffset returnDest rest).halt = s.halt := by
  simp only [combination1, touched1, touched0, touchWord]

@[simp] theorem combination2_executionEnv (s : State)
    (messageOffset returnDest : UInt256) (rest : List UInt256) :
    (combination2 s messageOffset returnDest rest).executionEnv = s.executionEnv := by
  simp only [combination2, touched2, touched1, touched0, touchWord]

@[simp] theorem combination2_halt (s : State)
    (messageOffset returnDest : UInt256) (rest : List UInt256) :
    (combination2 s messageOffset returnDest rest).halt = s.halt := by
  simp only [combination2, touched2, touched1, touched0, touchWord]

@[simp] theorem combination3_executionEnv (s : State)
    (messageOffset returnDest : UInt256) (rest : List UInt256) :
    (combination3 s messageOffset returnDest rest).executionEnv = s.executionEnv := by
  simp only [combination3, touched3, touched2, touched1, touched0, touchWord]

@[simp] theorem combination3_halt (s : State)
    (messageOffset returnDest : UInt256) (rest : List UInt256) :
    (combination3 s messageOffset returnDest rest).halt = s.halt := by
  simp only [combination3, touched3, touched2, touched1, touched0, touchWord]

def gasSteps_combination0 (s : State) (messageOffset returnDest : UInt256)
    (rest : List UInt256) (hstack : rest.length < 970)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (combinationEntry s messageOffset returnDest rest)
      (combination0 s messageOffset returnDest rest) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka combination0Located
  · simpa [combinationEntry, Artifact.referenceArtifact] using hcode
  · simpa [combinationEntry] using hfork
  · exact run_combination0 s messageOffset returnDest rest hstack hrun
  · simpa [combinationEntry] using hrun
  · simpa [combinationEntry] using hnp

def gasSteps_combination1 (s : State) (messageOffset returnDest : UInt256)
    (rest : List UInt256) (hstack : rest.length < 970)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (combination0 s messageOffset returnDest rest)
      (combination1 s messageOffset returnDest rest) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka combination1Located
  · simpa only [combination0_executionEnv, Artifact.referenceArtifact] using hcode
  · simpa [State.fork] using hfork
  · exact run_combination1 s messageOffset returnDest rest hstack hrun
  · simpa using hrun
  · simpa using hnp

def gasSteps_combination2 (s : State) (messageOffset returnDest : UInt256)
    (rest : List UInt256) (hstack : rest.length < 970)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (combination1 s messageOffset returnDest rest)
      (combination2 s messageOffset returnDest rest) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka combination2Located
  · simpa only [combination1_executionEnv, Artifact.referenceArtifact] using hcode
  · simpa [State.fork] using hfork
  · exact run_combination2 s messageOffset returnDest rest hstack hrun
  · simpa using hrun
  · simpa using hnp

def gasSteps_combination3 (s : State) (messageOffset returnDest : UInt256)
    (rest : List UInt256) (hstack : rest.length < 970)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (combination2 s messageOffset returnDest rest)
      (combination3 s messageOffset returnDest rest) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka combination3Located
  · simpa only [combination2_executionEnv, Artifact.referenceArtifact] using hcode
  · simpa [State.fork] using hfork
  · exact run_combination3 s messageOffset returnDest rest hstack hrun
  · simpa using hrun
  · simpa using hnp

def gasSteps_combination4 (s : State) (messageOffset returnDest : UInt256)
    (rest : List UInt256) (hstack : rest.length < 970)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (combination3 s messageOffset returnDest rest)
      (combination4 s messageOffset returnDest rest) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka combination4Located
  · simpa only [combination3_executionEnv, Artifact.referenceArtifact] using hcode
  · simpa [State.fork] using hfork
  · exact run_combination4 s messageOffset returnDest rest hstack hrun
  · simpa using hrun
  · simpa using hnp

def gasSteps_combinationPops (s : State)
    (messageOffset returnDest : UInt256) (rest : List UInt256)
    (hstack : rest.length < 970)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (combination4 s messageOffset returnDest rest)
      (combinationCleaned s messageOffset returnDest rest) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka combinationPopsLocated
  · simpa only [combination4_executionEnv, Artifact.referenceArtifact] using hcode
  · simpa [State.fork] using hfork
  · exact run_combinationPops s messageOffset returnDest rest hstack hrun
  · simpa using hrun
  · simpa using hnp

def gasSteps_combinationJump (s : State)
    (messageOffset returnDest : UInt256) (rest : List UInt256)
    (hstack : rest.length < 970)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hvalid : Decode.isValidJumpDest referenceBytecode returnDest.toNat = true) :
    Challenge.EvmProof.GasSteps
      (combinationCleaned s messageOffset returnDest rest)
      (combinationReturned s messageOffset returnDest rest) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka combinationJumpLocated
  · simpa only [combinationCleaned_executionEnv, Artifact.referenceArtifact] using hcode
  · simpa [State.fork] using hfork
  · exact run_combinationJump s messageOffset returnDest rest hstack hcode hrun hvalid
  · simpa using hrun
  · simpa using hnp

def gasSteps_combination (s : State)
    (messageOffset returnDest : UInt256) (rest : List UInt256)
    (hstack : rest.length < 970)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hvalid : Decode.isValidJumpDest referenceBytecode returnDest.toNat = true) :
    Challenge.EvmProof.GasSteps
      (combinationEntry s messageOffset returnDest rest)
      (combinationReturned s messageOffset returnDest rest) := by
  exact (gasSteps_combination0 s messageOffset returnDest rest hstack
    hcode hfork hrun hnp).trans
    ((gasSteps_combination1 s messageOffset returnDest rest hstack
      hcode hfork hrun hnp).trans
    ((gasSteps_combination2 s messageOffset returnDest rest hstack
      hcode hfork hrun hnp).trans
    ((gasSteps_combination3 s messageOffset returnDest rest hstack
      hcode hfork hrun hnp).trans
    ((gasSteps_combination4 s messageOffset returnDest rest hstack
      hcode hfork hrun hnp).trans
    ((gasSteps_combinationPops s messageOffset returnDest rest hstack
      hcode hfork hrun hnp).trans
      (gasSteps_combinationJump s messageOffset returnDest rest hstack
        hcode hfork hrun hnp hvalid))))))

def rightTailResult (s : State) (messageOffset returnDest : UInt256)
    (rest : List UInt256) : State :=
  combinationReturned (rightStates s messageOffset returnDest rest 80)
    messageOffset returnDest rest

def tailHashAt32 (s : State) : Compression.EvmHashState :=
  { h0 := wordAt s 32
    h1 := wordAt s 64
    h2 := wordAt s 96
    h3 := wordAt s 128
    h4 := wordAt s 160 }

theorem rightTailResult_hash (s : State)
    (messageOffset returnDest : UInt256) (rest : List UInt256) :
    tailHashAt32 (rightTailResult s messageOffset returnDest rest) =
      tailCombination (rightStates s messageOffset returnDest rest 80) := by
  simp (config := { maxSteps := 500000 })
    [tailHashAt32, rightTailResult, combinationReturned, combinationCleaned,
      combination4, storeWordMemory, wordAt,
      Challenge.EvmProof.Memory.readWord_writeWord,
      Challenge.EvmProof.Memory.readWord_writeBytes_disjoint]

theorem rightTailResult_hash_correct (s : State)
    (messageOffset returnDest : UInt256) (rest : List UInt256)
    {h : Compression.HashState} {left right : Compression.Working}
    (hsaved : savedHashAt512 (rightStates s messageOffset returnDest rest 80) =
      Compression.embedHash h)
    (hleft : workingAt (rightStates s messageOffset returnDest rest 80) 192 =
      Compression.embed left)
    (hright : workingAt (rightStates s messageOffset returnDest rest 80) 352 =
      Compression.embed right) :
    tailHashAt32 (rightTailResult s messageOffset returnDest rest) =
      Compression.embedHash (Compression.combine h left right) := by
  rw [rightTailResult_hash]
  unfold tailCombination
  rw [hsaved, hleft, hright]
  exact tailCombination_embedded h left right

/-- The complete concrete right line, loop exit, cross-combination, and return. -/
def gasSteps_rightLoopAndTail (s : State)
    (messageOffset returnDest : UInt256) (rest : List UInt256)
    (hstack : rest.length < 970)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hvalid : Decode.isValidJumpDest referenceBytecode returnDest.toNat = true) :
    Challenge.EvmProof.GasSteps
      (rightLoopAt s messageOffset returnDest rest 0)
      (rightTailResult s messageOffset returnDest rest) := by
  have g80 := gasSteps_right80Concrete s messageOffset returnDest rest
    hstack hcode hfork hrun hnp
  have hqcode : (rightStates s messageOffset returnDest rest 80).executionEnv.code =
      referenceBytecode := by
    rw [rightStates_executionEnv]
    exact hcode
  have hqfork : (rightStates s messageOffset returnDest rest 80).fork = .Osaka := by
    rw [State.fork, rightStates_executionEnv]
    exact hfork
  have hqrun : (rightStates s messageOffset returnDest rest 80).halt = .Running := by
    rw [rightStates_halt]
    exact hrun
  have hqnp : Precompile.isPrecompile
      (rightStates s messageOffset returnDest rest 80).executionEnv.fork
      (rightStates s messageOffset returnDest rest 80).executionEnv.codeAddr =
        false := by
    simpa [rightStates_executionEnv] using hnp
  let q := rightStates s messageOffset returnDest rest 80
  have gt := gasSteps_rightTest_exit q messageOffset returnDest rest
    (by omega) hqcode hqfork hqrun hqnp
  have ge := gasSteps_rightExit q messageOffset returnDest rest
    (by omega) hqcode hqfork hqrun hqnp
  have gc := gasSteps_combination q messageOffset returnDest rest hstack
    hqcode hqfork hqrun hqnp hvalid
  exact g80.trans (gt.trans (ge.trans gc))

end Challenge.Ripemd160.Reference.Proofs.Bytecode.CompressionTailTrace
