import Challenge.Sha256.Submissions.Sha256Fast.Proofs.InitializationDriver

set_option warningAsError false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000

namespace Challenge.Sha256.Submissions.Sha256Fast.Proofs.EndToEndTrace

open EvmSemantics EvmSemantics.EVM EvmSemantics.Crypto
open Challenge.EvmProof
open MemoryCorrect DriverLoop InitializationDriver

noncomputable def tailReady (input : ByteArray) : State :=
  if blockCount input = 0 then directTail input
  else tailAfterFull (fullStart input) input [] (blockCount input - 1)

noncomputable def finalState (input : ByteArray) : State :=
  let s := tailReady input
  let H := hashAt input (blockCount input)
  if input.size % 64 < 56 then
    TailCorrect.shortResult s H (endWord input) (endWord input)
      (remWord input) (sizeWord input) []
  else
    TailCorrect.longResult s H (endWord input) (endWord input)
      (remWord input) (sizeWord input) []

@[simp] theorem remWord_toNat (input : ByteArray) :
    (remWord input).toNat = input.size % 64 := by
  unfold remWord
  rw [Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt input.size (by omega))
      (by norm_num))]

private theorem short_condition (input : ByteArray)
    (hshort : input.size % 64 < 56) :
    UInt256.isTrue (UInt256.lt (remWord input) (UInt256.ofNat 56)) := by
  unfold UInt256.isTrue UInt256.lt
  rw [remWord_toNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt (by norm_num : 56 < 2 ^ 256)]
  simp [hshort]

private theorem long_condition (input : ByteArray)
    (hlong : ¬ input.size % 64 < 56) :
    ¬ UInt256.isTrue (UInt256.lt (remWord input) (UInt256.ofNat 56)) := by
  unfold UInt256.isTrue UInt256.lt
  rw [remWord_toNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt (by norm_num : 56 < 2 ^ 256)]
  simp [hlong]
  rfl

noncomputable def gasSteps_tailReady (input : ByteArray)
    (hfit : CalldataFits input) :
    GasSteps (initial input) (tailReady input) := by
  let gi := InitializationDriver.gasSteps_initialize input
  by_cases hz : blockCount input = 0
  · let gb := InitializationDriver.gasSteps_tailBranch input hfit hz
    let raw : GasSteps (initial input) (tailReady input) := GasSteps.cast
      (GasSteps.transKnown gi gb 1155 10 (by simp [gi]) (by simp [gb]))
      rfl (by simp [tailReady, hz])
    exact GasSteps.reprice raw (1165 + blockCount input * 21229) (by
      simp [raw, hz])
  · have hb : 0 < blockCount input := Nat.pos_of_ne_zero hz
    let gb := InitializationDriver.gasSteps_fullBranch input hfit hb
    let gl := DriverLoop.gasSteps_toTail (fullStart input) input [] hfit
      (by simp) (by rfl) hb (by rfl) (by rfl) (by rfl) (by rfl)
      (by rfl) (by rfl) Challenge.Sha256.deployAddress_not_precompile
      (by
        simpa [fullStart, initialized] using
          InitializationMemory.finalState_hash (initial input) (sizeWord input))
      (by
        simpa [fullStart, initialized] using
          InitializationMemory.finalState_constants (initial input) (sizeWord input))
    let gbl := GasSteps.transKnown gb gl 10 (blockCount input * 21229)
      (by simp [gb]) (by simp [gl])
    let raw : GasSteps (initial input) (tailReady input) :=
      GasSteps.cast (GasSteps.transKnown gi gbl 1155
      (10 + blockCount input * 21229) (by simp [gi]) rfl)
      rfl (by simp [tailReady, hz])
    exact GasSteps.reprice raw (1165 + blockCount input * 21229) (by
      simp [raw]
      omega)

@[simp] theorem gasSteps_tailReady_cost (input : ByteArray)
    (hfit : CalldataFits input) :
    (gasSteps_tailReady input hfit).cost =
      1165 + blockCount input * 21229 := by
  by_cases hz : blockCount input = 0
  · simp [gasSteps_tailReady, hz]
  · simp [gasSteps_tailReady, hz]

theorem tailReady_executionEnv (input : ByteArray) :
    (tailReady input).executionEnv = (initial input).executionEnv := by
  unfold tailReady
  split
  · rfl
  · unfold tailAfterFull
    rw [DriverCorrect.tailState_executionEnv,
      DriverLoop.fullState_executionEnv]
    rfl

@[simp] theorem tailReady_halt (input : ByteArray) :
    (tailReady input).halt = .Running := by
  rw [show (tailReady input).halt = (initial input).halt by
    unfold tailReady
    split
    · rfl
    · unfold tailAfterFull
      rw [DriverCorrect.tailState_halt, DriverLoop.fullState_halt]
      rfl]
  rfl

@[simp] theorem tailReady_fork (input : ByteArray) :
    (tailReady input).fork = .Osaka := by
  change (tailReady input).executionEnv.fork = .Osaka
  rw [tailReady_executionEnv]
  rfl

@[simp] theorem tailReady_code (input : ByteArray) :
    (tailReady input).executionEnv.code = Loop.bytes := by
  rw [tailReady_executionEnv]
  rfl

@[simp] theorem tailReady_calldata (input : ByteArray) :
    (tailReady input).executionEnv.calldata = input := by
  rw [tailReady_executionEnv]
  rfl

@[simp] theorem tailReady_activeWords (input : ByteArray) :
    (tailReady input).activeWords = UInt256.ofNat 140 := by
  unfold tailReady
  split
  · rfl
  · rfl

@[simp] theorem tailReady_pc (input : ByteArray) :
    (tailReady input).pc = UInt256.ofNat 2491 := by
  unfold tailReady
  split <;> rfl

@[simp] theorem tailReady_stack (input : ByteArray) :
    (tailReady input).stack =
      [endWord input, endWord input, remWord input, sizeWord input] := by
  unfold tailReady
  split
  · rename_i hz
    have he : endWord input = offsetWord 0 := by simp [endWord, hz]
    simp [directTail, he]
  · rename_i hz
    have hb : 0 < blockCount input := Nat.pos_of_ne_zero hz
    let i := blockCount input - 1
    have hi : i + 1 = blockCount input := by omega
    change (tailAfterFull (fullStart input) input [] i).stack = _
    simp only [tailAfterFull, DriverCorrect.tailState, DriverCorrect.testedState]
    rw [show UInt256.ofNat 64 + offsetWord i = offsetWord (i + 1) by
      unfold offsetWord
      rw [Challenge.EvmProof.Word.ofNat_add_mod]
      congr 1
      omega, hi]
    simp [endWord]

@[simp] theorem tailReady_callStack (input : ByteArray) :
    (tailReady input).callStack = [] := by
  unfold tailReady
  split
  · rfl
  · unfold tailAfterFull
    rw [DriverCorrect.tailState_callStack, DriverLoop.fullState_callStack]
    rfl

theorem tailReady_notPrecompile (input : ByteArray) :
    Precompile.isPrecompileWithConfig
      (tailReady input).executionEnv.precompileConfig
      (tailReady input).executionEnv.fork
      (tailReady input).executionEnv.codeAddr = false := by
  rw [tailReady_executionEnv]
  simpa [initial, Challenge.Sha256.initialState] using
    Challenge.Sha256.deployAddress_not_precompile

theorem tailReady_hash (input : ByteArray) (hfit : CalldataFits input) :
    HashCorrect (tailReady input).memory (hashAt input (blockCount input)) := by
  unfold tailReady
  split
  · rename_i hz
    rw [hz]
    simpa [directTail, initialized, hashAt] using
      InitializationMemory.finalState_hash (initial input) (sizeWord input)
  · rename_i hz
    have hb : 0 < blockCount input := Nat.pos_of_ne_zero hz
    apply DriverLoop.tailAfterFull_hash
      (s := fullStart input) (input := input) (rest := []) hfit
      (by rfl) hb
    simpa [fullStart, initialized] using
      InitializationMemory.finalState_hash (initial input) (sizeWord input)

theorem tailReady_constants (input : ByteArray) :
    ConstantsCorrect (tailReady input).memory := by
  unfold tailReady
  split
  · simpa [directTail, initialized] using
      InitializationMemory.finalState_constants (initial input) (sizeWord input)
  · apply DriverLoop.tailAfterFull_constants
    simpa [fullStart, initialized] using
      InitializationMemory.finalState_constants (initial input) (sizeWord input)

noncomputable def gasSteps_finalState (input : ByteArray)
    (hfit : CalldataFits input) :
    GasSteps (initial input) (finalState input) := by
  let s := tailReady input
  let H := hashAt input (blockCount input)
  let gt := gasSteps_tailReady input hfit
  by_cases hs : input.size % 64 < 56
  · let g := TailCorrect.gasSteps_short s H
      (endWord input) (endWord input) (remWord input) (sizeWord input) []
      (by simp) (by simpa [remWord_toNat] using Nat.mod_lt input.size (by omega))
      (by simpa [s]) (by simpa [s]) (by simpa [s]) (by simpa [s])
      (by simpa [s]) (by simpa [s])
      (by simpa [s] using tailReady_notPrecompile input)
      (short_condition input hs) (by simpa [s, H] using tailReady_hash input hfit)
      (by simpa [s] using tailReady_constants input)
    let raw : GasSteps (initial input) (finalState input) := GasSteps.cast
      (GasSteps.transKnown gt g (1165 + blockCount input * 21229) 21387
        (by simp [gt]) (by simp [g]))
      rfl (by simp [finalState, s, H, hs])
    exact GasSteps.reprice raw
      (22552 + blockCount input * 21229 +
        (if input.size % 64 < 56 then 0 else 21198)) (by
      simp [raw, hs]
      omega)
  · let g := TailCorrect.gasSteps_long s H
      (endWord input) (endWord input) (remWord input) (sizeWord input) []
      (by simp) (by simpa [remWord_toNat] using Nat.mod_lt input.size (by omega))
      (by simpa [s]) (by simpa [s]) (by simpa [s]) (by simpa [s])
      (by simpa [s]) (by simpa [s])
      (by simpa [s] using tailReady_notPrecompile input)
      (long_condition input hs) (by simpa [s, H] using tailReady_hash input hfit)
      (by simpa [s] using tailReady_constants input)
    let raw : GasSteps (initial input) (finalState input) := GasSteps.cast
      (GasSteps.transKnown gt g (1165 + blockCount input * 21229) 42585
        (by simp [gt]) (by simp [g]))
      rfl (by simp [finalState, s, H, hs])
    exact GasSteps.reprice raw
      (22552 + blockCount input * 21229 +
        (if input.size % 64 < 56 then 0 else 21198)) (by
      simp [raw, hs]
      omega)

@[simp] theorem gasSteps_finalState_cost (input : ByteArray)
    (hfit : CalldataFits input) :
    (gasSteps_finalState input hfit).cost =
      22552 + blockCount input * 21229 +
        (if input.size % 64 < 56 then 0 else 21198) := by
  by_cases hs : input.size % 64 < 56
  · simp [gasSteps_finalState, hs]
  · simp [gasSteps_finalState, hs]

@[simp] theorem finalState_isDone (input : ByteArray) :
    (finalState input).isDone = true := by
  by_cases hs : input.size % 64 < 56
  · simp [finalState, hs, TailCorrect.shortResult, State.isDone,
      State.isHalted, State.isRunning, tailReady_callStack]
  · simp [finalState, hs, TailCorrect.longResult, State.isDone,
      State.isHalted, State.isRunning, tailReady_callStack]

end Challenge.Sha256.Submissions.Sha256Fast.Proofs.EndToEndTrace
