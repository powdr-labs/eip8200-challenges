import Challenge.Ripemd160.Reference.Proofs.Bytecode.ExactGasBridge
import Challenge.Ripemd160.Reference.Proofs.Bytecode.InitializationGasTrace
import Challenge.Ripemd160.Reference.Proofs.Bytecode.OutputResultBridge
import Batteries.Tactic.OpenPrivate

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Challenge.Ripemd160.Reference.Proofs.Bytecode.OuterGasTrace

open Challenge.Ripemd160
open Challenge.EvmProof
open EvmSemantics
open EvmSemantics.EVM

open private gasSteps_driver gasSteps_output gasSteps_outputLoop
  gasSteps_outputIteration gasSteps_writeWord gasSteps_writeLoop
  gasSteps_writeIteration loadedH writeLoopState afterWrittenWord
  outputLoopState outputResult writeLoopState_normalized
  outputLoopState_normalized from
  Challenge.Ripemd160.Reference.Proofs.Bytecode.DirectCorrect

open private gasSteps_padPrefix run_lengthCondition run_lengthByte
  run_lengthStore run_lengthIncrement run_lengthBackPush run_lengthBackJump
  lengthBackReturned_eq run_lengthCopy run_lengthSentinelAddress
  run_lengthSentinelStore run_lengthFooterSetup padSentinelStored_eq
  run_enter run_paddedLength run_lengthExitCompare run_lengthExitZero
  run_lengthExitDest run_lengthExitJumpToBody run_lengthExitPop
  run_lengthExitSwap run_lengthExitJump padReturnedFromExit_eq from
  Challenge.Ripemd160.Reference.Proofs.Bytecode.PaddingTrace

private def paddingTargetWords (input : ByteArray) : Nat :=
  64 + 2 * DriverTrace.blockCount input

private theorem paddingTargetWords_mul (input : ByteArray) :
    paddingTargetWords input * 32 =
      Padding.messageOffset + Padding.paddedLength input.size := by
  simp [paddingTargetWords, DriverTrace.blockCount, Padding.messageOffset,
    Padding.paddedLength]
  omega

private theorem activeWordsAfter_le_words (curr offset size words : Nat)
    (hcurr : curr ≤ words) (hend : offset + size ≤ words * 32) :
    MachineState.activeWordsAfter curr offset size ≤ words := by
  unfold MachineState.activeWordsAfter
  split
  · exact hcurr
  · rw [Nat.max_le]
    constructor
    · exact hcurr
    · have hq : (offset + size - 1) / 32 < words :=
        (Nat.div_lt_iff_lt_mul (by omega)).2 (by omega)
      omega

private theorem paddingTargetWords_lt (input : ByteArray)
    (hfit : CalldataFits input) : paddingTargetWords input < 2 ^ 256 := by
  have hpad := Padding.paddedLength_lt input.size
  have hmul := paddingTargetWords_mul input
  unfold CalldataFits at hfit
  norm_num [Padding.messageOffset] at hfit hmul ⊢
  omega

theorem padLengthReady_activeWords (input : ByteArray) :
    (PaddingTrace.padLengthReady input).activeWords.toNat = 59 := by
  have h1184 : (1184 : UInt256).toNat = 1184 := by
    change (UInt256.ofNat 1184).toNat = 1184
    norm_num
  have h1216 : (1216 : UInt256).toNat = 1216 := by
    change (UInt256.ofNat 1216).toNat = 1216
    norm_num
  have h1248 : (1248 : UInt256).toNat = 1248 := by
    change (UInt256.ofNat 1248).toNat = 1248
    norm_num
  have h1280 : (1280 : UInt256).toNat = 1280 := by
    change (UInt256.ofNat 1280).toNat = 1280
    norm_num
  have h1312 : (1312 : UInt256).toNat = 1312 := by
    change (UInt256.ofNat 1312).toNat = 1312
    norm_num
  have h1344 : (1344 : UInt256).toNat = 1344 := by
    change (UInt256.ofNat 1344).toNat = 1344
    norm_num
  have h1376 : (1376 : UInt256).toNat = 1376 := by
    change (UInt256.ofNat 1376).toNat = 1376
    norm_num
  have h1408 : (1408 : UInt256).toNat = 1408 := by
    change (UInt256.ofNat 1408).toNat = 1408
    norm_num
  have h1440 : (1440 : UInt256).toNat = 1440 := by
    change (UInt256.ofNat 1440).toNat = 1440
    norm_num
  have h1472 : (1472 : UInt256).toNat = 1472 := by
    change (UInt256.ofNat 1472).toNat = 1472
    norm_num
  have h1504 : (1504 : UInt256).toNat = 1504 := by
    change (UInt256.ofNat 1504).toNat = 1504
    norm_num
  have h1536 : (1536 : UInt256).toNat = 1536 := by
    change (UInt256.ofNat 1536).toNat = 1536
    norm_num
  have h1568 : (1568 : UInt256).toNat = 1568 := by
    change (UInt256.ofNat 1568).toNat = 1568
    norm_num
  have h1600 : (1600 : UInt256).toNat = 1600 := by
    change (UInt256.ofNat 1600).toNat = 1600
    norm_num
  have h1632 : (1632 : UInt256).toNat = 1632 := by
    change (UInt256.ofNat 1632).toNat = 1632
    norm_num
  have h1664 : (1664 : UInt256).toNat = 1664 := by
    change (UInt256.ofNat 1664).toNat = 1664
    norm_num
  have h1696 : (1696 : UInt256).toNat = 1696 := by
    change (UInt256.ofNat 1696).toNat = 1696
    norm_num
  have h1728 : (1728 : UInt256).toNat = 1728 := by
    change (UInt256.ofNat 1728).toNat = 1728
    norm_num
  have h1760 : (1760 : UInt256).toNat = 1760 := by
    change (UInt256.ofNat 1760).toNat = 1760
    norm_num
  have h1792 : (1792 : UInt256).toNat = 1792 := by
    change (UInt256.ofNat 1792).toNat = 1792
    norm_num
  have h1824 : (1824 : UInt256).toNat = 1824 := by
    change (UInt256.ofNat 1824).toNat = 1824
    norm_num
  have h1856 : (1856 : UInt256).toNat = 1856 := by
    change (UInt256.ofNat 1856).toNat = 1856
    norm_num
  have h32 : (32 : UInt256).toNat = 32 := by
    change (UInt256.ofNat 32).toNat = 32
    norm_num
  have h64 : (64 : UInt256).toNat = 64 := by
    change (UInt256.ofNat 64).toNat = 64
    norm_num
  have h96 : (96 : UInt256).toNat = 96 := by
    change (UInt256.ofNat 96).toNat = 96
    norm_num
  have h128 : (128 : UInt256).toNat = 128 := by
    change (UInt256.ofNat 128).toNat = 128
    norm_num
  have h160 : (160 : UInt256).toNat = 160 := by
    change (UInt256.ofNat 160).toNat = 160
    norm_num
  simp [PaddingTrace.padLengthReady, PaddingTrace.padEntry,
    PaddingTrace.pushedPad, PaddingTrace.pushedOutput,
    PaddingTrace.pushedReturn, Main.initializedState, Artifact.initStores,
    Main.applyInitStore, Execution.mainStart, Execution.atPC, initialState,
    State.activeWordsAfterUInt256, MachineState.activeWordsAfter,
    Challenge.EvmProof.Word.word_toNat_ofNat, h1184, h1216, h1248, h1280,
    h1312, h1344, h1376, h1408, h1440, h1472, h1504, h1536, h1568, h1600,
    h1632, h1664, h1696, h1728, h1760, h1792, h1824, h1856, h32, h64, h96,
    h128, h160]

private theorem padSentinel_activeWords_le (input : ByteArray)
    (hfit : CalldataFits input) :
    (PaddingTrace.padSentinel input).activeWords.toNat ≤
      paddingTargetWords input := by
  have hfooter := Padding.input_and_footer_fit input.size
  have hmul := paddingTargetWords_mul input
  have hstart : 59 ≤ paddingTargetWords input := by
    unfold paddingTargetWords
    omega
  let aw₁ := MachineState.activeWordsAfter 59 Padding.messageOffset input.size
  let aw₂ := MachineState.activeWordsAfter aw₁
    (Padding.messageOffset + input.size) 1
  have haw₁ : aw₁ ≤ paddingTargetWords input := by
    apply activeWordsAfter_le_words
    · exact hstart
    · omega
  have haw₂ : aw₂ ≤ paddingTargetWords input := by
    apply activeWordsAfter_le_words
    · exact haw₁
    · omega
  have htargetLt := paddingTargetWords_lt input hfit
  have haw₁_lt : aw₁ < 2 ^ 256 := lt_of_le_of_lt haw₁ htargetLt
  have haw₂_lt : aw₂ < 2 ^ 256 := lt_of_le_of_lt haw₂ htargetLt
  simp [PaddingTrace.padSentinel, PaddingTrace.padCopied,
    State.activeWordsAfterUInt256,
    padLengthReady_activeWords input]
  dsimp [aw₁, aw₂] at haw₁_lt haw₂_lt haw₂ ⊢
  rw [Nat.mod_eq_of_lt haw₁_lt, Nat.mod_eq_of_lt haw₂_lt]
  exact haw₂

private theorem lengthActiveWordsAfter_lt (input : ByteArray)
    (hfit : CalldataFits input) (i : Nat) (hi : i < 8) :
    MachineState.activeWordsAfter
        (PaddingTrace.lengthLoopActiveWords input i).toNat
        (PaddingTrace.lengthOffsetWord input + UInt256.ofNat i).toNat 1 <
      2 ^ 256 := by
  rw [PaddingTrace.lengthOffset_add_toNat input hfit i (by omega)]
  have haddr : Padding.messageOffset + Padding.paddedLength input.size - 8 + i + 1 <
      2 ^ 256 := by
    have hlt := Padding.paddedLength_lt input.size
    unfold CalldataFits at hfit
    norm_num [Padding.messageOffset] at hfit ⊢
    omega
  unfold MachineState.activeWordsAfter
  rw [if_neg (by decide : (1 : Nat) ≠ 0), Nat.max_lt]
  constructor
  · exact (PaddingTrace.lengthLoopActiveWords input i).val.isLt
  · have hdiv :
        (Padding.messageOffset + Padding.paddedLength input.size - 8 + i + 1 - 1) /
            32 ≤
          Padding.messageOffset + Padding.paddedLength input.size - 8 + i + 1 - 1 :=
        Nat.div_le_self _ _
    omega

private theorem lengthLoopActiveWords_succ_toNat (input : ByteArray)
    (hfit : CalldataFits input) (i : Nat) (hi : i < 8) :
    (PaddingTrace.lengthLoopActiveWords input (i + 1)).toNat =
      MachineState.activeWordsAfter
        (PaddingTrace.lengthLoopActiveWords input i).toNat
        (PaddingTrace.lengthOffsetWord input + UInt256.ofNat i).toNat 1 := by
  rw [PaddingTrace.lengthLoopActiveWords,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact Nat.mod_eq_of_lt (lengthActiveWordsAfter_lt input hfit i hi)

private theorem lengthLoopActiveWords_le (input : ByteArray)
    (hfit : CalldataFits input) (i : Nat) (hi : i ≤ 8) :
    (PaddingTrace.lengthLoopActiveWords input i).toNat ≤
      paddingTargetWords input := by
  induction i with
  | zero =>
      simpa [PaddingTrace.lengthLoopActiveWords] using
        padSentinel_activeWords_le input hfit
  | succ i ih =>
      have hi8 : i < 8 := by omega
      rw [lengthLoopActiveWords_succ_toNat input hfit i hi8]
      apply activeWordsAfter_le_words
      · exact ih (by omega)
      · rw [PaddingTrace.lengthOffset_add_toNat input hfit i (by omega)]
        have hmul := paddingTargetWords_mul input
        have hfooter := Padding.input_and_footer_fit input.size
        omega

theorem padReturned_activeWords (input : ByteArray) (hfit : CalldataFits input) :
    (PaddingTrace.padReturned input).activeWords.toNat =
      64 + 2 * DriverTrace.blockCount input := by
  change (PaddingTrace.lengthLoopActiveWords input 8).toNat = _
  have hupper7 := lengthLoopActiveWords_le input hfit 7 (by omega)
  rw [lengthLoopActiveWords_succ_toNat input hfit 7 (by omega)]
  unfold MachineState.activeWordsAfter
  rw [if_neg (by decide : (1 : Nat) ≠ 0)]
  have hoff := PaddingTrace.lengthOffset_add_toNat input hfit 7 (by omega)
  rw [hoff]
  have hmul := paddingTargetWords_mul input
  have htargetPos : 0 < paddingTargetWords input := by
    simp [paddingTargetWords]
  have hquot :
      (Padding.messageOffset + Padding.paddedLength input.size - 8 + 7 + 1 - 1) /
          32 = paddingTargetWords input - 1 := by
    apply Nat.div_eq_of_lt_le
    · omega
    · omega
  dsimp only
  rw [hquot, Nat.sub_add_cancel (by omega : 1 ≤ paddingTargetWords input)]
  change Nat.max (PaddingTrace.lengthLoopActiveWords input 7).toNat
    (paddingTargetWords input) = _
  calc
    Nat.max (PaddingTrace.lengthLoopActiveWords input 7).toNat
        (paddingTargetWords input) = paddingTargetWords input :=
      Nat.max_eq_right hupper7
    _ = 64 + 2 * DriverTrace.blockCount input := rfl

private theorem lengthCopy_cost_potential (input : ByteArray)
    (hfit : CalldataFits input) :
    (Output.gasSteps_block PaddingTrace.lengthCopyPath
      (PaddingTrace.padLengthReady input) (PaddingTrace.padCopied input)
      (by rfl) (by rfl) (run_lengthCopy input hfit) (by rfl)
      deployAddress_not_precompile).cost +
        MachineState.memCost
          (PaddingTrace.padLengthReady input).activeWords.toNat =
      (11 + 3 * ((input.size + 31) / 32)) +
        MachineState.memCost (PaddingTrace.padCopied input).activeWords.toNat := by
  have hsize : input.size < 2 ^ 256 := Nat.lt_trans hfit (by norm_num)
  have hsizeWord : (UInt256.ofNat input.size).toNat = input.size := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hsize]
  change Challenge.EvmProof.Stepper.runLocatedBlockCost
      PaddingTrace.lengthCopyPath (PaddingTrace.padLengthReady input) + _ = _
  rw [Challenge.EvmProof.Meter.runLocatedBlock_cost_potential
    PaddingTrace.lengthCopyPath (run_lengthCopy input hfit)]
  simp [Challenge.EvmProof.Meter.runLocatedBlockCostWithoutMemory,
    Challenge.EvmProof.Meter.instrCostWithoutMemory,
    PaddingTrace.lengthCopyPath, PaddingTrace.lengthSetupPath,
    Artifact.padSetupPath, Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr, Gas.copyWordCost, Gas.baseCost,
    hsizeWord]
  omega

private theorem lengthSentinelAddress_cost_potential (input : ByteArray) :
    (Output.gasSteps_block PaddingTrace.lengthSentinelAddressPath
      (PaddingTrace.padCopied input) (PaddingTrace.padSentinelAddressReady input)
      (by rfl) (by rfl) (run_lengthSentinelAddress input) (by rfl)
      deployAddress_not_precompile).cost +
        MachineState.memCost (PaddingTrace.padCopied input).activeWords.toNat =
      12 + MachineState.memCost
        (PaddingTrace.padSentinelAddressReady input).activeWords.toNat := by
  change Challenge.EvmProof.Stepper.runLocatedBlockCost
      PaddingTrace.lengthSentinelAddressPath (PaddingTrace.padCopied input) + _ = _
  rw [Challenge.EvmProof.Meter.runLocatedBlock_cost_potential
    PaddingTrace.lengthSentinelAddressPath (run_lengthSentinelAddress input)]
  simp [Challenge.EvmProof.Meter.runLocatedBlockCostWithoutMemory,
    Challenge.EvmProof.Meter.instrCostWithoutMemory,
    PaddingTrace.lengthSentinelAddressPath, PaddingTrace.lengthSentinelPath,
    PaddingTrace.lengthSetupPath, Artifact.padSetupPath,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Gas.baseCost]

private theorem lengthSentinelStore_cost_potential (input : ByteArray)
    (hfit : CalldataFits input) :
    (Output.gasSteps_block PaddingTrace.lengthSentinelStorePath
      (PaddingTrace.padSentinelAddressReady input)
      (PaddingTrace.padSentinelStored input)
      (by rfl) (by rfl) (run_lengthSentinelStore input hfit) (by rfl)
      deployAddress_not_precompile).cost +
        MachineState.memCost
          (PaddingTrace.padSentinelAddressReady input).activeWords.toNat =
      3 + MachineState.memCost
        (PaddingTrace.padSentinelStored input).activeWords.toNat := by
  change Challenge.EvmProof.Stepper.runLocatedBlockCost
      PaddingTrace.lengthSentinelStorePath
        (PaddingTrace.padSentinelAddressReady input) + _ = _
  rw [Challenge.EvmProof.Meter.runLocatedBlock_cost_potential
    PaddingTrace.lengthSentinelStorePath (run_lengthSentinelStore input hfit)]
  simp [Challenge.EvmProof.Meter.runLocatedBlockCostWithoutMemory,
    Challenge.EvmProof.Meter.instrCostWithoutMemory,
    PaddingTrace.lengthSentinelStorePath, PaddingTrace.lengthSentinelPath,
    PaddingTrace.lengthSetupPath, Artifact.padSetupPath, Gas.baseCost]

private theorem lengthFooterSetup_cost_potential (input : ByteArray) :
    (Output.gasSteps_block PaddingTrace.lengthFooterSetupPath
      (PaddingTrace.padSentinel input) (PaddingTrace.lengthLoopStart input)
      (by rfl) (by rfl) (run_lengthFooterSetup input) (by rfl)
      deployAddress_not_precompile).cost +
        MachineState.memCost (PaddingTrace.padSentinel input).activeWords.toNat =
      26 + MachineState.memCost
        (PaddingTrace.lengthLoopStart input).activeWords.toNat := by
  change Challenge.EvmProof.Stepper.runLocatedBlockCost
      PaddingTrace.lengthFooterSetupPath (PaddingTrace.padSentinel input) + _ = _
  rw [Challenge.EvmProof.Meter.runLocatedBlock_cost_static_potential
    PaddingTrace.lengthFooterSetupPath (run_lengthFooterSetup input) (by rfl)]
  · norm_num [Challenge.EvmProof.Meter.runLocatedBlockStaticCost,
      Challenge.EvmProof.Meter.instrStaticCost,
      PaddingTrace.lengthFooterSetupPath, PaddingTrace.lengthSetupPath,
      Artifact.padSetupPath, Gas.baseCost]
  · intro located hmem q hq
    simp [PaddingTrace.lengthFooterSetupPath, PaddingTrace.lengthSetupPath,
      Artifact.padSetupPath] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [Challenge.EvmProof.Meter.instrCostWithoutMemory,
        Challenge.EvmProof.Meter.instrStaticCost, hq]

private theorem lengthSetup_cost_decomp (input : ByteArray)
    (hfit : CalldataFits input) :
    (PaddingTrace.gasSteps_lengthSetup input hfit).cost =
      Challenge.EvmProof.Stepper.runLocatedBlockCost PaddingTrace.lengthCopyPath
          (PaddingTrace.padLengthReady input) +
        ((Challenge.EvmProof.Stepper.runLocatedBlockCost
            PaddingTrace.lengthSentinelAddressPath (PaddingTrace.padCopied input) +
          Challenge.EvmProof.Stepper.runLocatedBlockCost
            PaddingTrace.lengthSentinelStorePath
              (PaddingTrace.padSentinelAddressReady input)) +
          Challenge.EvmProof.Stepper.runLocatedBlockCost
            PaddingTrace.lengthFooterSetupPath (PaddingTrace.padSentinel input)) := by
  rfl

private theorem lengthSetup_cost_potential (input : ByteArray)
    (hfit : CalldataFits input) :
    (PaddingTrace.gasSteps_lengthSetup input hfit).cost +
        MachineState.memCost 59 =
      52 + 3 * ((input.size + 31) / 32) +
        MachineState.memCost (PaddingTrace.padSentinel input).activeWords.toNat := by
  have hcopy := lengthCopy_cost_potential input hfit
  change Challenge.EvmProof.Stepper.runLocatedBlockCost
      PaddingTrace.lengthCopyPath (PaddingTrace.padLengthReady input) +
      MachineState.memCost (PaddingTrace.padLengthReady input).activeWords.toNat = _ at hcopy
  rw [padLengthReady_activeWords input] at hcopy
  have haddr := lengthSentinelAddress_cost_potential input
  change Challenge.EvmProof.Stepper.runLocatedBlockCost
      PaddingTrace.lengthSentinelAddressPath (PaddingTrace.padCopied input) + _ = _ at haddr
  have hstoreRaw := lengthSentinelStore_cost_potential input hfit
  change Challenge.EvmProof.Stepper.runLocatedBlockCost
      PaddingTrace.lengthSentinelStorePath
        (PaddingTrace.padSentinelAddressReady input) + _ = _ at hstoreRaw
  have hstore : Challenge.EvmProof.Stepper.runLocatedBlockCost
      PaddingTrace.lengthSentinelStorePath
        (PaddingTrace.padSentinelAddressReady input) +
      MachineState.memCost
        (PaddingTrace.padSentinelAddressReady input).activeWords.toNat =
    3 + MachineState.memCost (PaddingTrace.padSentinel input).activeWords.toNat := by
    have hendpoint : MachineState.memCost
        (PaddingTrace.padSentinelStored input).activeWords.toNat =
      MachineState.memCost (PaddingTrace.padSentinel input).activeWords.toNat :=
      congrArg (fun s : State => MachineState.memCost s.activeWords.toNat)
        (padSentinelStored_eq input hfit)
    rw [← hendpoint]
    exact hstoreRaw
  have hfooter := lengthFooterSetup_cost_potential input
  change Challenge.EvmProof.Stepper.runLocatedBlockCost
      PaddingTrace.lengthFooterSetupPath (PaddingTrace.padSentinel input) +
      MachineState.memCost (PaddingTrace.padSentinel input).activeWords.toNat =
    26 + MachineState.memCost
      (PaddingTrace.padSentinel input).activeWords.toNat at hfooter
  rw [lengthSetup_cost_decomp input hfit]
  omega

private theorem lengthCondition_cost_potential (input : ByteArray)
    (i : Nat) (hi : i < 8) :
    Challenge.EvmProof.Stepper.runLocatedBlockCost
        PaddingTrace.lengthConditionPath (PaddingTrace.lengthLoopState input i) +
      MachineState.memCost
        (PaddingTrace.lengthLoopState input i).activeWords.toNat =
    26 + MachineState.memCost
      (PaddingTrace.lengthBodyState input i).activeWords.toNat := by
  rw [Challenge.EvmProof.Meter.runLocatedBlock_cost_static_potential
    PaddingTrace.lengthConditionPath (run_lengthCondition input i hi) (by rfl)]
  · norm_num [Challenge.EvmProof.Meter.runLocatedBlockStaticCost,
      Challenge.EvmProof.Meter.instrStaticCost,
      PaddingTrace.lengthConditionPath, PaddingTrace.lengthIterationPath,
      Gas.baseCost]
  · intro located hmem q hq
    simp [PaddingTrace.lengthConditionPath,
      PaddingTrace.lengthIterationPath] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [Challenge.EvmProof.Meter.instrCostWithoutMemory,
        Challenge.EvmProof.Meter.instrStaticCost, hq]

private theorem lengthByte_cost_potential (input : ByteArray) (i : Nat) :
    Challenge.EvmProof.Stepper.runLocatedBlockCost PaddingTrace.lengthBytePath
        (PaddingTrace.lengthBodyState input i) +
      MachineState.memCost
        (PaddingTrace.lengthBodyState input i).activeWords.toNat =
    21 + MachineState.memCost
      (PaddingTrace.lengthByteState input i).activeWords.toNat := by
  rw [Challenge.EvmProof.Meter.runLocatedBlock_cost_static_potential
    PaddingTrace.lengthBytePath (run_lengthByte input i) (by rfl)]
  · norm_num [Challenge.EvmProof.Meter.runLocatedBlockStaticCost,
      Challenge.EvmProof.Meter.instrStaticCost,
      PaddingTrace.lengthBytePath, PaddingTrace.lengthIterationPath,
      Gas.baseCost]
  · intro located hmem q hq
    simp [PaddingTrace.lengthBytePath,
      PaddingTrace.lengthIterationPath] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [Challenge.EvmProof.Meter.instrCostWithoutMemory,
        Challenge.EvmProof.Meter.instrStaticCost, hq]

private theorem lengthStore_cost_potential (input : ByteArray) (i : Nat) :
    Challenge.EvmProof.Stepper.runLocatedBlockCost PaddingTrace.lengthStorePath
        (PaddingTrace.lengthByteState input i) +
      MachineState.memCost
        (PaddingTrace.lengthByteState input i).activeWords.toNat =
    12 + MachineState.memCost
      (PaddingTrace.lengthStoredState input i).activeWords.toNat := by
  rw [Challenge.EvmProof.Meter.runLocatedBlock_cost_static_potential
    PaddingTrace.lengthStorePath (run_lengthStore input i) (by rfl)]
  · norm_num [Challenge.EvmProof.Meter.runLocatedBlockStaticCost,
      Challenge.EvmProof.Meter.instrStaticCost,
      PaddingTrace.lengthStorePath, PaddingTrace.lengthIterationPath,
      Gas.baseCost]
  · intro located hmem q hq
    simp [PaddingTrace.lengthStorePath,
      PaddingTrace.lengthIterationPath] at hmem
    rcases hmem with rfl | rfl | rfl | rfl <;>
      simp [Challenge.EvmProof.Meter.instrCostWithoutMemory,
        Challenge.EvmProof.Meter.instrStaticCost, hq]

private theorem lengthIncrement_cost_potential (input : ByteArray)
    (i : Nat) (hi : i < 8) :
    Challenge.EvmProof.Stepper.runLocatedBlockCost
        PaddingTrace.lengthIncrementPath (PaddingTrace.lengthStoredState input i) +
      MachineState.memCost
        (PaddingTrace.lengthStoredState input i).activeWords.toNat =
    14 + MachineState.memCost
      (PaddingTrace.lengthIncrementedState input i).activeWords.toNat := by
  rw [Challenge.EvmProof.Meter.runLocatedBlock_cost_static_potential
    PaddingTrace.lengthIncrementPath (run_lengthIncrement input i hi) (by rfl)]
  · norm_num [Challenge.EvmProof.Meter.runLocatedBlockStaticCost,
      Challenge.EvmProof.Meter.instrStaticCost,
      PaddingTrace.lengthIncrementPath, PaddingTrace.lengthIterationPath,
      Gas.baseCost]
  · intro located hmem q hq
    simp [PaddingTrace.lengthIncrementPath,
      PaddingTrace.lengthIterationPath] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl <;>
      simp [Challenge.EvmProof.Meter.instrCostWithoutMemory,
        Challenge.EvmProof.Meter.instrStaticCost, hq]

private theorem lengthBackPush_cost_potential (input : ByteArray) (i : Nat) :
    Challenge.EvmProof.Stepper.runLocatedBlockCost PaddingTrace.lengthBackPushPath
        (PaddingTrace.lengthIncrementedState input i) +
      MachineState.memCost
        (PaddingTrace.lengthIncrementedState input i).activeWords.toNat =
    3 + MachineState.memCost
      (PaddingTrace.lengthBackReady input i).activeWords.toNat := by
  rw [Challenge.EvmProof.Meter.runLocatedBlock_cost_static_potential
    PaddingTrace.lengthBackPushPath (run_lengthBackPush input i) (by rfl)]
  · norm_num [Challenge.EvmProof.Meter.runLocatedBlockStaticCost,
      Challenge.EvmProof.Meter.instrStaticCost, PaddingTrace.lengthBackPushPath,
      PaddingTrace.lengthBackPath, PaddingTrace.lengthIterationPath, Gas.baseCost]
  · intro located hmem q hq
    simp [PaddingTrace.lengthBackPushPath, PaddingTrace.lengthBackPath,
      PaddingTrace.lengthIterationPath] at hmem
    rcases hmem with rfl
    simp [Challenge.EvmProof.Meter.instrCostWithoutMemory,
      Challenge.EvmProof.Meter.instrStaticCost, hq]

private theorem lengthBackJump_cost_potential (input : ByteArray) (i : Nat) :
    Challenge.EvmProof.Stepper.runLocatedBlockCost PaddingTrace.lengthBackJumpPath
        (PaddingTrace.lengthBackReady input i) +
      MachineState.memCost
        (PaddingTrace.lengthBackReady input i).activeWords.toNat =
    8 + MachineState.memCost
      (PaddingTrace.lengthBackReturned input i).activeWords.toNat := by
  rw [Challenge.EvmProof.Meter.runLocatedBlock_cost_static_potential
    PaddingTrace.lengthBackJumpPath (run_lengthBackJump input i) (by rfl)]
  · norm_num [Challenge.EvmProof.Meter.runLocatedBlockStaticCost,
      Challenge.EvmProof.Meter.instrStaticCost, PaddingTrace.lengthBackJumpPath,
      PaddingTrace.lengthBackPath, PaddingTrace.lengthIterationPath, Gas.baseCost]
  · intro located hmem q hq
    simp [PaddingTrace.lengthBackJumpPath, PaddingTrace.lengthBackPath,
      PaddingTrace.lengthIterationPath] at hmem
    rcases hmem with rfl
    simp [Challenge.EvmProof.Meter.instrCostWithoutMemory,
      Challenge.EvmProof.Meter.instrStaticCost, hq]

private theorem lengthIteration_cost_decomp (input : ByteArray)
    (i : Nat) (hi : i < 8) :
    (PaddingTrace.gasSteps_lengthIteration input i hi).cost =
      Challenge.EvmProof.Stepper.runLocatedBlockCost
          PaddingTrace.lengthConditionPath (PaddingTrace.lengthLoopState input i) +
        (Challenge.EvmProof.Stepper.runLocatedBlockCost PaddingTrace.lengthBytePath
            (PaddingTrace.lengthBodyState input i) +
          (Challenge.EvmProof.Stepper.runLocatedBlockCost
              PaddingTrace.lengthStorePath (PaddingTrace.lengthByteState input i) +
            (Challenge.EvmProof.Stepper.runLocatedBlockCost
                PaddingTrace.lengthIncrementPath
                  (PaddingTrace.lengthStoredState input i) +
              (Challenge.EvmProof.Stepper.runLocatedBlockCost
                  PaddingTrace.lengthBackPushPath
                    (PaddingTrace.lengthIncrementedState input i) +
                Challenge.EvmProof.Stepper.runLocatedBlockCost
                  PaddingTrace.lengthBackJumpPath
                    (PaddingTrace.lengthBackReady input i))))) := by
  rfl

private theorem lengthIteration_cost_potential (input : ByteArray)
    (i : Nat) (hi : i < 8) :
    (PaddingTrace.gasSteps_lengthIteration input i hi).cost +
        MachineState.memCost
          (PaddingTrace.lengthLoopActiveWords input i).toNat =
      84 + MachineState.memCost
        (PaddingTrace.lengthLoopActiveWords input (i + 1)).toNat := by
  have hcondition := lengthCondition_cost_potential input i hi
  have hbyte := lengthByte_cost_potential input i
  have hstore := lengthStore_cost_potential input i
  have hincrement := lengthIncrement_cost_potential input i hi
  have hbackPush := lengthBackPush_cost_potential input i
  have hbackJumpRaw := lengthBackJump_cost_potential input i
  change Challenge.EvmProof.Stepper.runLocatedBlockCost
      PaddingTrace.lengthConditionPath (PaddingTrace.lengthLoopState input i) +
      MachineState.memCost (PaddingTrace.lengthLoopActiveWords input i).toNat =
    26 + MachineState.memCost
      (PaddingTrace.lengthLoopActiveWords input i).toNat at hcondition
  change Challenge.EvmProof.Stepper.runLocatedBlockCost
      PaddingTrace.lengthBytePath (PaddingTrace.lengthBodyState input i) +
      MachineState.memCost (PaddingTrace.lengthLoopActiveWords input i).toNat =
    21 + MachineState.memCost
      (PaddingTrace.lengthLoopActiveWords input i).toNat at hbyte
  change Challenge.EvmProof.Stepper.runLocatedBlockCost
      PaddingTrace.lengthStorePath (PaddingTrace.lengthByteState input i) +
      MachineState.memCost (PaddingTrace.lengthLoopActiveWords input i).toNat =
    12 + MachineState.memCost
      (PaddingTrace.lengthLoopActiveWords input (i + 1)).toNat at hstore
  change Challenge.EvmProof.Stepper.runLocatedBlockCost
      PaddingTrace.lengthIncrementPath (PaddingTrace.lengthStoredState input i) +
      MachineState.memCost (PaddingTrace.lengthLoopActiveWords input (i + 1)).toNat =
    14 + MachineState.memCost
      (PaddingTrace.lengthLoopActiveWords input (i + 1)).toNat at hincrement
  change Challenge.EvmProof.Stepper.runLocatedBlockCost
      PaddingTrace.lengthBackPushPath
        (PaddingTrace.lengthIncrementedState input i) +
      MachineState.memCost (PaddingTrace.lengthLoopActiveWords input (i + 1)).toNat =
    3 + MachineState.memCost
      (PaddingTrace.lengthLoopActiveWords input (i + 1)).toNat at hbackPush
  have hendpoint : MachineState.memCost
      (PaddingTrace.lengthBackReturned input i).activeWords.toNat =
    MachineState.memCost
      (PaddingTrace.lengthLoopState input (i + 1)).activeWords.toNat :=
    congrArg (fun s : State => MachineState.memCost s.activeWords.toNat)
      (lengthBackReturned_eq input i)
  rw [hendpoint] at hbackJumpRaw
  change Challenge.EvmProof.Stepper.runLocatedBlockCost
      PaddingTrace.lengthBackJumpPath (PaddingTrace.lengthBackReady input i) +
      MachineState.memCost (PaddingTrace.lengthLoopActiveWords input (i + 1)).toNat =
    8 + MachineState.memCost
      (PaddingTrace.lengthLoopActiveWords input (i + 1)).toNat at hbackJumpRaw
  rw [lengthIteration_cost_decomp input i hi]
  omega

private theorem lengthLoop_cost_potential (input : ByteArray) :
    (PaddingTrace.gasSteps_lengthLoop input).cost +
        MachineState.memCost
          (PaddingTrace.lengthLoopActiveWords input 0).toNat =
      672 + MachineState.memCost
        (PaddingTrace.lengthLoopActiveWords input 8).toNat := by
  unfold PaddingTrace.gasSteps_lengthLoop
  change (Challenge.EvmProof.GasSteps.iterateBounded 8
      (PaddingTrace.gasSteps_lengthIteration input)).cost +
      MachineState.memCost
        (PaddingTrace.lengthLoopState input 0).activeWords.toNat =
    672 + MachineState.memCost
      (PaddingTrace.lengthLoopState input 8).activeWords.toNat
  exact Challenge.EvmProof.Meter.iterateBounded_cost_potential_add
    8 84 (PaddingTrace.gasSteps_lengthIteration input)
    (fun i hi => lengthIteration_cost_potential input i hi)

private theorem initialize_cost (input : ByteArray) :
    (Main.gasSteps_initialize input).cost = 580 := by
  have hactive := padLengthReady_activeWords input
  change (Main.initializedState input).activeWords.toNat = 59 at hactive
  exact InitializationGasTrace.initialize_cost_of_active input hactive

private theorem enterPad_cost (input : ByteArray) :
    (PaddingTrace.gasSteps_enterPad input).cost = 16 := by
  rfl

private theorem paddedLength_cost (input : ByteArray) :
    (PaddingTrace.gasSteps_paddedLength input).cost = 29 := by
  rfl

private theorem lengthExit_cost (input : ByteArray) :
    (PaddingTrace.gasSteps_lengthExit input).cost = 46 := by
  rfl

theorem padding_cost (input : ByteArray) (hfit : CalldataFits input) :
    (PaddingTrace.gasSteps_pad input hfit).cost =
      1212 + 3 * GasCost.calldataWords input.size +
        MachineState.memCost (64 + 2 * DriverTrace.blockCount input) := by
  have hsetup := lengthSetup_cost_potential input hfit
  have hloop := lengthLoop_cost_potential input
  rw [show (PaddingTrace.lengthLoopActiveWords input 0).toNat =
      (PaddingTrace.padSentinel input).activeWords.toNat by rfl] at hloop
  change (PaddingTrace.gasSteps_lengthLoop input).cost +
      MachineState.memCost (PaddingTrace.padSentinel input).activeWords.toNat =
    672 + MachineState.memCost
      (PaddingTrace.padReturned input).activeWords.toNat at hloop
  rw [padReturned_activeWords input hfit] at hloop
  unfold GasCost.calldataWords
  have hmem59 : MachineState.memCost 59 = 183 := by
    norm_num [MachineState.memCost]
  rw [hmem59] at hsetup
  have hbody :
      (PaddingTrace.gasSteps_lengthSetup input hfit).cost +
          (PaddingTrace.gasSteps_lengthLoop input).cost =
        541 + 3 * ((input.size + 31) / 32) +
          MachineState.memCost
            (64 + 2 * DriverTrace.blockCount input) := by
    omega
  unfold PaddingTrace.gasSteps_pad gasSteps_padPrefix PaddingTrace.gasSteps_padBody
  simp only [Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.GasSteps.cast_cost]
  rw [initialize_cost input, enterPad_cost input, paddedLength_cost input,
    lengthExit_cost input]
  omega

theorem seam_initial_activeWords (input : ByteArray) (hfit : CalldataFits input)
    (seam : DirectCorrect.CompressionSeam input) :
    (seam.states 0).activeWords.toNat =
      64 + 2 * DriverTrace.blockCount input := by
  have h := congrArg (fun s : State => s.activeWords.toNat) seam.initial
  change (seam.states 0).activeWords.toNat =
    (PaddingTrace.padReturned input).activeWords.toNat at h
  rw [padReturned_activeWords input hfit] at h
  exact h

end Challenge.Ripemd160.Reference.Proofs.Bytecode.OuterGasTrace
