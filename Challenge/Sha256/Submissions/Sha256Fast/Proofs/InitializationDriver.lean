import Challenge.Sha256.Submissions.Sha256Fast.Proofs.DriverLoop
import Challenge.Sha256.Submissions.Sha256Fast.Proofs.InitializationGas
import Challenge.Sha256.Submissions.Sha256Fast.Proofs.GasTools

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

namespace Challenge.Sha256.Submissions.Sha256Fast.Proofs.InitializationDriver

open EvmSemantics EvmSemantics.EVM EvmSemantics.Crypto
open Challenge.EvmProof Challenge.EvmProof.Stepper
open DriverLoop

def initial (input : ByteArray) : State :=
  Challenge.Sha256.initialState Loop.bytes input 0

noncomputable def initialized (input : ByteArray) : State :=
  InitializationCorrect.finalState (initial input) (sizeWord input)

noncomputable def fullStart (input : ByteArray) : State :=
  { initialized input with
    pc := UInt256.ofNat 2465
    stack := [offsetWord 0, endWord input, remWord input, sizeWord input] }

noncomputable def directTail (input : ByteArray) : State :=
  { initialized input with
    pc := UInt256.ofNat 2491
    stack := [offsetWord 0, endWord input, remWord input, sizeWord input] }

theorem initialization_endWord (input : ByteArray) (hfit : CalldataFits input) :
    InitializationCorrect.endWord (sizeWord input) = endWord input := by
  unfold InitializationCorrect.endWord sizeWord endWord offsetWord blockCount
  unfold CalldataFits at hfit
  rw [Challenge.EvmProof.Word.shiftRight_ofNat
      (Nat.lt_trans hfit (by norm_num)) (by omega)]
  rw [Challenge.EvmProof.Word.shiftLeft_ofNat]
  · congr 1
    rw [Nat.shiftRight_eq_div_pow]
    norm_num
  · exact Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) (Nat.lt_trans hfit (by norm_num))
  · omega
  · rw [Nat.shiftRight_eq_div_pow]
    norm_num
    have hle := Nat.div_mul_le_self input.size 64
    exact lt_of_le_of_lt hle (Nat.lt_trans hfit (by norm_num))

theorem initialization_remainder (input : ByteArray)
    (hfit : CalldataFits input) :
    InitializationCorrect.remainder (sizeWord input) = remWord input := by
  unfold InitializationCorrect.remainder sizeWord remWord
  apply Challenge.EvmProof.Word.word_ext
  rw [Challenge.EvmProof.Word.word_toNat_land,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt (by norm_num : 63 < 2 ^ 256),
    Nat.mod_eq_of_lt (Nat.lt_trans hfit (by norm_num))]
  rw [Nat.and_comm, show 63 = 2 ^ 6 - 1 by norm_num,
    Nat.and_two_pow_sub_one_eq_mod]
  rw [Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt input.size (by omega))
      (by norm_num))]

noncomputable def gasSteps_initialize (input : ByteArray) :
    GasSteps (initial input) (initialized input) :=
  InitializationGas.gasSteps_initialize (initial input) (sizeWord input)
    rfl rfl rfl rfl rfl rfl rfl Challenge.Sha256.deployAddress_not_precompile

noncomputable def gasSteps_fullBranch (input : ByteArray) (hfit : CalldataFits input)
    (hblocks : 0 < blockCount input) :
    GasSteps (initialized input) (fullStart input) := by
  let s := initialized input
  let hresult : runLocatedBlock DriverBlocks.initialBranchPath s =
      some (fullStart input) := by
    have hendNat : (endWord input).toNat = blockCount input * 64 :=
      offsetWord_toNat input hfit (blockCount input) (by omega)
    have hne : blockCount input * 64 ≠ 0 := by omega
    have hcond : ¬ UInt256.isTrue (UInt256.isZero (endWord input)) := by
      unfold UInt256.isTrue UInt256.isZero
      rw [hendNat]
      simp [hne]
      rfl
    simpa [s, initialized, fullStart, InitializationCorrect.finalState,
      offsetWord, initialization_endWord input hfit,
      initialization_remainder input hfit]
      using DriverBlocks.run_initialBranch_full s (endWord input)
        (remWord input) (sizeWord input) [] (by simp) (by rfl) (by rfl)
        hcond (by simp [s, initialized, InitializationCorrect.finalState,
          initialization_endWord input hfit, initialization_remainder input hfit])
  exact Challenge.EvmProof.FixedPathGas.trace DriverBlocks.initialBranchPath 10
    (by rfl) (by rfl) (by rfl) (by rfl) hresult (by rfl)
    Challenge.Sha256.deployAddress_not_precompile rfl

noncomputable def gasSteps_tailBranch (input : ByteArray) (hfit : CalldataFits input)
    (hblocks : blockCount input = 0) :
    GasSteps (initialized input) (directTail input) := by
  let s := initialized input
  let hresult : runLocatedBlock DriverBlocks.initialBranchPath s =
      some (directTail input) := by
    have hend : endWord input = UInt256.ofNat 0 := by
      simp [endWord, offsetWord, hblocks]
    have hcond : UInt256.isTrue (UInt256.isZero (endWord input)) := by
      rw [hend]
      decide
    simpa [s, initialized, directTail, InitializationCorrect.finalState,
      offsetWord, initialization_endWord input hfit,
      initialization_remainder input hfit]
      using DriverBlocks.run_initialBranch_tail s (endWord input)
        (remWord input) (sizeWord input) [] (by simp) (by rfl) (by rfl)
        (by rfl) hcond (by simp [s, initialized, InitializationCorrect.finalState,
          initialization_endWord input hfit, initialization_remainder input hfit])
  exact Challenge.EvmProof.FixedPathGas.trace DriverBlocks.initialBranchPath 10
    (by rfl) (by rfl) (by rfl) (by rfl) hresult (by rfl)
    Challenge.Sha256.deployAddress_not_precompile rfl

@[simp] theorem gasSteps_initialize_cost (input : ByteArray) :
    (gasSteps_initialize input).cost = 1155 := rfl

@[simp] theorem gasSteps_fullBranch_cost (input : ByteArray)
    (hfit : CalldataFits input) (hblocks : 0 < blockCount input) :
    (gasSteps_fullBranch input hfit hblocks).cost = 10 := rfl

@[simp] theorem gasSteps_tailBranch_cost (input : ByteArray)
    (hfit : CalldataFits input) (hblocks : blockCount input = 0) :
    (gasSteps_tailBranch input hfit hblocks).cost = 10 := rfl

end Challenge.Sha256.Submissions.Sha256Fast.Proofs.InitializationDriver
