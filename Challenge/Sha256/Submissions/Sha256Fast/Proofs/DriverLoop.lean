import Challenge.Sha256.Submissions.Sha256Fast.Proofs.DriverControl
import Challenge.Sha256.Submissions.Sha256Fast.Proofs.DriverInvariants
import Challenge.Sha256.Submissions.Sha256Fast.Proofs.TailCorrect

set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000

namespace Challenge.Sha256.Submissions.Sha256Fast.Proofs.DriverLoop

open EvmSemantics EvmSemantics.EVM EvmSemantics.Crypto
open Challenge.EvmProof
open MemoryCorrect DriverCorrect

namespace SpecBridge

abbrev absorbBlocks :=
  Challenge.Sha256.Reference.Proofs.Bytecode.SpecBridge.absorbBlocks

end SpecBridge

def blockCount (input : ByteArray) : Nat := input.size / 64
def offsetWord (i : Nat) : UInt256 := UInt256.ofNat (i * 64)
def endWord (input : ByteArray) : UInt256 := offsetWord (blockCount input)
def remWord (input : ByteArray) : UInt256 := UInt256.ofNat (input.size % 64)
def sizeWord (input : ByteArray) : UInt256 := UInt256.ofNat input.size

def hashAt (input : ByteArray) (i : Nat) : Array UInt32 :=
  SpecBridge.absorbBlocks Sha256.H0 input 0 i

def fullState (s : State) (input : ByteArray) (rest : List UInt256) : Nat → State
  | 0 => s
  | i + 1 => nextFullState (fullState s input rest i) (hashAt input i)
      (offsetWord i) (endWord input) (remWord input) (sizeWord input) rest

def tailAfterFull (s : State) (input : ByteArray) (rest : List UInt256)
    (i : Nat) : State :=
  tailState (fullState s input rest i) (hashAt input i)
    (offsetWord i) (endWord input) (remWord input) (sizeWord input) rest

theorem offset_bound (input : ByteArray) (hfit : CalldataFits input)
    (i : Nat) (hi : i ≤ blockCount input) : i * 64 < 2 ^ 256 := by
  unfold CalldataFits at hfit
  unfold blockCount at hi
  have hle : i * 64 ≤ input.size := by
    have := Nat.div_mul_le_self input.size 64
    omega
  omega

@[simp] theorem offsetWord_toNat (input : ByteArray) (hfit : CalldataFits input)
    (i : Nat) (hi : i ≤ blockCount input) :
    (offsetWord i).toNat = i * 64 := by
  unfold offsetWord
  rw [Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt (offset_bound input hfit i hi)]

private theorem offset_add (i : Nat) :
    UInt256.ofNat 64 + offsetWord i = offsetWord (i + 1) := by
  unfold offsetWord
  rw [Challenge.EvmProof.Word.ofNat_add_mod]
  congr 1
  omega

private theorem continue_condition (input : ByteArray)
    (hfit : CalldataFits input) (i : Nat) (hi : i + 1 < blockCount input) :
    UInt256.isTrue
      (UInt256.lt (UInt256.ofNat 64 + offsetWord i) (endWord input)) := by
  rw [offset_add i]
  unfold UInt256.isTrue UInt256.lt endWord
  rw [offsetWord_toNat input hfit (i + 1) (by omega),
    offsetWord_toNat input hfit (blockCount input) (by omega)]
  simp [hi]

private theorem exit_condition (input : ByteArray)
    (_hfit : CalldataFits input) (i : Nat) (hi : i + 1 = blockCount input) :
    ¬ UInt256.isTrue
      (UInt256.lt (UInt256.ofNat 64 + offsetWord i) (endWord input)) := by
  rw [offset_add i, hi]
  unfold UInt256.isTrue UInt256.lt endWord
  simp
  rfl

theorem fullState_executionEnv (s : State) (input : ByteArray)
    (rest : List UInt256) (i : Nat) :
    (fullState s input rest i).executionEnv = s.executionEnv := by
  induction i with
  | zero => rfl
  | succ i ih => simpa [fullState] using ih

theorem fullState_halt (s : State) (input : ByteArray)
    (rest : List UInt256) (i : Nat) :
    (fullState s input rest i).halt = s.halt := by
  induction i with
  | zero => rfl
  | succ i ih => simpa [fullState] using ih

theorem fullState_fork (s : State) (input : ByteArray)
    (rest : List UInt256) (i : Nat) :
    (fullState s input rest i).fork = s.fork := by
  induction i with
  | zero => rfl
  | succ i ih => simpa [fullState] using ih

theorem fullState_callStack (s : State) (input : ByteArray)
    (rest : List UInt256) (i : Nat) :
    (fullState s input rest i).callStack = s.callStack := by
  induction i with
  | zero => rfl
  | succ i ih => simpa [fullState] using ih

theorem fullState_activeWords (s : State) (input : ByteArray)
    (rest : List UInt256) (i : Nat) (haw : s.activeWords = UInt256.ofNat 140) :
    (fullState s input rest i).activeWords = UInt256.ofNat 140 := by
  cases i with
  | zero => exact haw
  | succ i => rfl

theorem fullState_pc (s : State) (input : ByteArray)
    (rest : List UInt256) (i : Nat) (hpc : s.pc = UInt256.ofNat 2465) :
    (fullState s input rest i).pc = UInt256.ofNat 2465 := by
  cases i with
  | zero => exact hpc
  | succ i => rfl

theorem fullState_stack (s : State) (input : ByteArray)
    (rest : List UInt256) (i : Nat)
    (hstack : s.stack = [offsetWord 0, endWord input, remWord input,
      sizeWord input] ++ rest) :
    (fullState s input rest i).stack =
      [offsetWord i, endWord input, remWord input, sizeWord input] ++ rest := by
  cases i with
  | zero => exact hstack
  | succ i =>
      simp only [fullState, nextFullState]
      rw [offset_add i]

theorem fullState_constants (s : State) (input : ByteArray)
    (rest : List UInt256) (i : Nat) (hK : ConstantsCorrect s.memory) :
    ConstantsCorrect (fullState s input rest i).memory := by
  induction i with
  | zero => exact hK
  | succ i ih =>
      simpa [fullState, nextFullState, testedState] using
        DriverInvariants.blockResult_constants
          (fullState s input rest i) (hashAt input i)
          (offsetWord i) (endWord input) (remWord input) (sizeWord input)
          rest ih

theorem fullState_hash (s : State) (input : ByteArray)
    (rest : List UInt256) (hfit : CalldataFits input)
    (hinput : s.executionEnv.calldata = input)
    (i : Nat) (hi : i ≤ blockCount input)
    (hH : HashCorrect s.memory Sha256.H0) :
    HashCorrect (fullState s input rest i).memory (hashAt input i) := by
  induction i with
  | zero => simpa [fullState, hashAt] using hH
  | succ i ih =>
      have hprev := ih (by omega)
      have h := DriverInvariants.blockResult_hash
        (fullState s input rest i) (hashAt input i)
        (offsetWord i) (endWord input) (remWord input) (sizeWord input) rest
      rw [offsetWord_toNat input hfit i (by omega)] at h
      have hcal : (fullState s input rest i).executionEnv.calldata = input := by
        rw [fullState_executionEnv, hinput]
      rw [hcal] at h
      have hs :=
        Challenge.Sha256.Reference.Proofs.Bytecode.SpecBridge.absorbBlocks_succ
          Sha256.H0 input 0 i
      simpa [fullState, nextFullState, testedState, hashAt, hs] using h

private noncomputable def gasSteps_iteration (s : State) (input : ByteArray)
    (rest : List UInt256) (hfit : CalldataFits input)
    (hcap : rest.length < 985) (hinput : s.executionEnv.calldata = input)
    (haw : s.activeWords = UInt256.ofNat 140)
    (hcode : s.executionEnv.code = Loop.bytes) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running) (hpc : s.pc = UInt256.ofNat 2465)
    (hstack : s.stack = [offsetWord 0, endWord input, remWord input,
      sizeWord input] ++ rest)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hH : HashCorrect s.memory Sha256.H0) (hK : ConstantsCorrect s.memory)
    (i : Nat) (hi : i + 1 < blockCount input) :
    GasSteps (fullState s input rest i) (fullState s input rest (i + 1)) :=
  let q := fullState s input rest i
  let gb := DriverCorrect.gasSteps_block q (hashAt input i)
    (offsetWord i) (endWord input) (remWord input) (sizeWord input) rest
    hcap (fullState_activeWords s input rest i haw)
    (by simpa [q, fullState_executionEnv] using hcode)
    (by simpa [q, fullState_fork] using hfork)
    (by simpa [q, fullState_halt] using hrun)
    (fullState_pc s input rest i hpc)
    (fullState_stack s input rest i hstack)
    (by simpa [q, fullState_executionEnv, fullState_fork] using hnp)
    (fullState_hash s input rest hfit hinput i (by omega) hH)
    (fullState_constants s input rest i hK)
  let gc := DriverControl.gasSteps_continue q (hashAt input i)
    (offsetWord i) (endWord input) (remWord input) (sizeWord input) rest
    hcap (by simpa [q, fullState_executionEnv] using hcode)
    (by simpa [q, fullState_fork] using hfork)
    (by simpa [q, fullState_halt] using hrun)
    (by simpa [q, fullState_executionEnv, fullState_fork] using hnp)
    (continue_condition input hfit i hi)
  GasSteps.cast (GasSteps.transKnown gb gc 21200 29 rfl rfl) rfl
    (by simp [q, fullState])

@[simp] private theorem gasSteps_iteration_cost (s : State) (input : ByteArray)
    (rest : List UInt256) (hfit : CalldataFits input)
    (hcap : rest.length < 985) (hinput : s.executionEnv.calldata = input)
    (haw : s.activeWords = UInt256.ofNat 140)
    (hcode : s.executionEnv.code = Loop.bytes) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running) (hpc : s.pc = UInt256.ofNat 2465)
    (hstack : s.stack = [offsetWord 0, endWord input, remWord input,
      sizeWord input] ++ rest)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hH : HashCorrect s.memory Sha256.H0) (hK : ConstantsCorrect s.memory)
    (i : Nat) (hi : i + 1 < blockCount input) :
    (gasSteps_iteration s input rest hfit hcap hinput haw hcode hfork hrun hpc
      hstack hnp hH hK i hi).cost = 21229 := rfl

noncomputable def gasSteps_prefix (s : State) (input : ByteArray)
    (rest : List UInt256) (hfit : CalldataFits input)
    (hcap : rest.length < 985) (hinput : s.executionEnv.calldata = input)
    (haw : s.activeWords = UInt256.ofNat 140)
    (hcode : s.executionEnv.code = Loop.bytes) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running) (hpc : s.pc = UInt256.ofNat 2465)
    (hstack : s.stack = [offsetWord 0, endWord input, remWord input,
      sizeWord input] ++ rest)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hH : HashCorrect s.memory Sha256.H0) (hK : ConstantsCorrect s.memory)
    (i : Nat) (hi : i < blockCount input) :
    GasSteps s (fullState s input rest i) :=
  GasSteps.cast
    (GasSteps.iterateBoundedKnown i 21229 (fun j hj =>
      gasSteps_iteration s input rest hfit hcap hinput haw hcode hfork hrun hpc
        hstack hnp hH hK j (by omega))
      (fun j hj => gasSteps_iteration_cost s input rest hfit hcap hinput haw
        hcode hfork hrun hpc hstack hnp hH hK j (by omega)))
    rfl rfl

@[simp] theorem gasSteps_prefix_cost (s : State) (input : ByteArray)
    (rest : List UInt256) (hfit : CalldataFits input)
    (hcap : rest.length < 985) (hinput : s.executionEnv.calldata = input)
    (haw : s.activeWords = UInt256.ofNat 140)
    (hcode : s.executionEnv.code = Loop.bytes) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running) (hpc : s.pc = UInt256.ofNat 2465)
    (hstack : s.stack = [offsetWord 0, endWord input, remWord input,
      sizeWord input] ++ rest)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hH : HashCorrect s.memory Sha256.H0) (hK : ConstantsCorrect s.memory)
    (i : Nat) (hi : i < blockCount input) :
    (gasSteps_prefix s input rest hfit hcap hinput haw hcode hfork hrun hpc
      hstack hnp hH hK i hi).cost = i * 21229 := rfl

noncomputable def gasSteps_toTail (s : State) (input : ByteArray)
    (rest : List UInt256) (hfit : CalldataFits input)
    (hcap : rest.length < 985) (hinput : s.executionEnv.calldata = input)
    (hblocks : 0 < blockCount input)
    (haw : s.activeWords = UInt256.ofNat 140)
    (hcode : s.executionEnv.code = Loop.bytes) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running) (hpc : s.pc = UInt256.ofNat 2465)
    (hstack : s.stack = [offsetWord 0, endWord input, remWord input,
      sizeWord input] ++ rest)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hH : HashCorrect s.memory Sha256.H0) (hK : ConstantsCorrect s.memory) :
    GasSteps s (tailAfterFull s input rest (blockCount input - 1)) := by
  let i := blockCount input - 1
  let q := fullState s input rest i
  have hi : i < blockCount input := by omega
  have hieq : i + 1 = blockCount input := by omega
  let gp := gasSteps_prefix s input rest hfit hcap hinput haw hcode hfork hrun hpc
    hstack hnp hH hK i hi
  let gb := DriverCorrect.gasSteps_block q (hashAt input i)
    (offsetWord i) (endWord input) (remWord input) (sizeWord input) rest
    hcap (fullState_activeWords s input rest i haw)
    (by simpa [q, fullState_executionEnv] using hcode)
    (by simpa [q, fullState_fork] using hfork)
    (by simpa [q, fullState_halt] using hrun)
    (fullState_pc s input rest i hpc)
    (fullState_stack s input rest i hstack)
    (by simpa [q, fullState_executionEnv, fullState_fork] using hnp)
    (fullState_hash s input rest hfit hinput i (by omega) hH)
    (fullState_constants s input rest i hK)
  let ge := DriverControl.gasSteps_exit q (hashAt input i)
    (offsetWord i) (endWord input) (remWord input) (sizeWord input) rest
    hcap (by simpa [q, fullState_executionEnv] using hcode)
    (by simpa [q, fullState_fork] using hfork)
    (by simpa [q, fullState_halt] using hrun)
    (by simpa [q, fullState_executionEnv, fullState_fork] using hnp)
    (exit_condition input hfit i hieq)
  have hgb : gb.cost = 21200 := by simp [gb]
  have hge : ge.cost = 29 := by simp [ge]
  have hgp : gp.cost = i * 21229 := by simp [gp]
  let last : GasSteps q (tailAfterFull s input rest i) :=
    GasSteps.cast (GasSteps.transKnown gb ge 21200 29 hgb hge) rfl
      (by simp [tailAfterFull, q])
  let raw := GasSteps.transKnown gp last (i * 21229) 21229 hgp rfl
  apply GasSteps.reprice raw (blockCount input * 21229)
  change i * 21229 + 21229 = blockCount input * 21229
  omega

@[simp] theorem gasSteps_toTail_cost (s : State) (input : ByteArray)
    (rest : List UInt256) (hfit : CalldataFits input)
    (hcap : rest.length < 985) (hinput : s.executionEnv.calldata = input)
    (hblocks : 0 < blockCount input)
    (haw : s.activeWords = UInt256.ofNat 140)
    (hcode : s.executionEnv.code = Loop.bytes) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running) (hpc : s.pc = UInt256.ofNat 2465)
    (hstack : s.stack = [offsetWord 0, endWord input, remWord input,
      sizeWord input] ++ rest)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hH : HashCorrect s.memory Sha256.H0) (hK : ConstantsCorrect s.memory) :
    (gasSteps_toTail s input rest hfit hcap hinput hblocks haw hcode hfork hrun
      hpc hstack hnp hH hK).cost = blockCount input * 21229 := by
  simp [gasSteps_toTail]

theorem tailAfterFull_hash (s : State) (input : ByteArray)
    (rest : List UInt256) (hfit : CalldataFits input)
    (hinput : s.executionEnv.calldata = input)
    (hblocks : 0 < blockCount input)
    (_hH : HashCorrect s.memory Sha256.H0) :
    HashCorrect (tailAfterFull s input rest (blockCount input - 1)).memory
      (hashAt input (blockCount input)) := by
  let i := blockCount input - 1
  have h := DriverInvariants.blockResult_hash
    (fullState s input rest i) (hashAt input i)
    (offsetWord i) (endWord input) (remWord input) (sizeWord input) rest
  rw [offsetWord_toNat input hfit i (by omega)] at h
  have hcal : (fullState s input rest i).executionEnv.calldata = input := by
    rw [fullState_executionEnv, hinput]
  rw [hcal] at h
  have hs :=
    Challenge.Sha256.Reference.Proofs.Bytecode.SpecBridge.absorbBlocks_succ
      Sha256.H0 input 0 i
  have hcount : blockCount input = i + 1 := by omega
  have hsub : i + 1 - 1 = i := by omega
  simpa [tailAfterFull, tailState, testedState, hashAt, hcount, hsub, hs] using h

theorem tailAfterFull_constants (s : State) (input : ByteArray)
    (rest : List UInt256) (hK : ConstantsCorrect s.memory) :
    ConstantsCorrect (tailAfterFull s input rest (blockCount input - 1)).memory := by
  apply DriverInvariants.blockResult_constants
  exact fullState_constants s input rest (blockCount input - 1) hK

end Challenge.Sha256.Submissions.Sha256Fast.Proofs.DriverLoop
