import Challenge.Sha256.Reference.Proofs.Bytecode.PaddingTrace

open EvmSemantics EvmSemantics.EVM
open Challenge.Sha256
open Challenge.Sha256.Reference.Proofs.Bytecode

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Challenge.Sha256.Reference.Proofs.Bytecode.PaddingGas

private theorem padLengthReady_activeWords (input : ByteArray) :
    (PaddingTrace.padLengthReady input).activeWords.toNat = 17 := by
  rfl

private theorem memCost_monotone : Monotone MachineState.memCost := by
  intro a b hab
  unfold MachineState.memCost
  exact Nat.add_le_add (Nat.mul_le_mul_left 3 hab)
    (Nat.div_le_div_right (Nat.pow_le_pow_left hab 2))

private theorem activeWordsAfter_ge (curr offset size : Nat) :
    curr ≤ MachineState.activeWordsAfter curr offset size := by
  rw [MachineState.activeWordsAfter]
  split
  · rfl
  · exact Nat.le_max_left _ _

private theorem lengthSetup_cost_run (input : ByteArray) (hfit : CalldataFits input) :
    (PaddingTrace.gasSteps_lengthSetup input hfit).cost =
      Challenge.EvmProof.Stepper.runLocatedBlockCost
        PaddingTrace.lengthSetupPath (PaddingTrace.padLengthReady input) := by
  simp only [PaddingTrace.gasSteps_lengthSetup,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost]

theorem lengthSetup_cost (input : ByteArray) (hfit : CalldataFits input) :
    (PaddingTrace.gasSteps_lengthSetup input hfit).cost =
      2 + 3 * ((input.size + 31) / 32) +
        MachineState.memCost
          (PaddingTrace.padSentinel input).activeWords.toNat := by
  have hsize : input.size < 2 ^ 256 := by
    exact Nat.lt_trans hfit (by norm_num)
  have hoff : Padding.messageOffset < 2 ^ 256 := by decide
  have hsum : Padding.messageOffset + input.size < 2 ^ 256 := by
    unfold CalldataFits at hfit
    norm_num [Padding.messageOffset] at hfit ⊢
    omega
  have hsum1 : Padding.messageOffset + input.size + 1 < 2 ^ 256 := by
    unfold CalldataFits at hfit
    norm_num [Padding.messageOffset] at hfit ⊢
    omega
  have hadd : (UInt256.ofNat Padding.messageOffset +
      UInt256.ofNat input.size).toNat = Padding.messageOffset + input.size := by
    rw [Challenge.EvmProof.Word.ofNat_add_ofNat hsum,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hsum]
  have hsizeWord : (UInt256.ofNat input.size).toNat = input.size := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hsize]
  have hoffWord : (UInt256.ofNat Padding.messageOffset).toNat =
      Padding.messageOffset := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hoff]
  have hzero : (⟨0⟩ : UInt256) = UInt256.ofNat 0 := by decide
  let aw₁ := MachineState.activeWordsAfter 17 Padding.messageOffset input.size
  let aw₂ := MachineState.activeWordsAfter aw₁
    (Padding.messageOffset + input.size) 1
  have haw₁_lt : aw₁ < 2 ^ 256 := by
    dsimp [aw₁]
    simp only [MachineState.activeWordsAfter]
    split
    · norm_num
    · rw [Nat.max_lt]
      constructor
      · norm_num
      · have hdiv : (Padding.messageOffset + input.size - 1) / 32 ≤
            Padding.messageOffset + input.size - 1 := Nat.div_le_self _ _
        omega
  have haw₂_lt : aw₂ < 2 ^ 256 := by
    dsimp [aw₂]
    simp only [MachineState.activeWordsAfter]
    split
    · exact haw₁_lt
    · rw [Nat.max_lt]
      constructor
      · exact haw₁_lt
      · have hdiv :
            (Padding.messageOffset + input.size + 1 - 1) / 32 ≤
              Padding.messageOffset + input.size + 1 - 1 :=
            Nat.div_le_self _ _
        omega
  have haw₁_le : aw₁ ≤ aw₂ := by
    exact activeWordsAfter_ge _ _ _
  have hmem₁ : MachineState.memCost 17 ≤ MachineState.memCost aw₁ := by
    apply memCost_monotone
    exact activeWordsAfter_ge _ _ _
  have hmem₂ : MachineState.memCost aw₁ ≤ MachineState.memCost aw₂ :=
    memCost_monotone haw₁_le
  simp only [PaddingTrace.gasSteps_lengthSetup,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost]
  simp [Challenge.EvmProof.Stepper.runLocatedBlockCost,
    PaddingTrace.lengthSetupPath,
    Challenge.EvmProof.Stepper.instrCost,
    Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr,
    Gas.totalCost, Gas.calldatacopyTotal, Gas.mstore8Total,
    MachineState.memExpansionDelta, Gas.copyWordCost,
    PaddingTrace.padSentinel, PaddingTrace.padCopied,
    State.activeWordsAfterUInt256, hsizeWord, hoffWord, hzero, hadd,
    Gas.baseCost, show (PaddingTrace.padLengthReady input).activeWords.toNat = 17
      by rfl]
  change MachineState.activeWordsAfter 17 Padding.messageOffset input.size <
      2 ^ 256 at haw₁_lt
  change MachineState.activeWordsAfter
      (MachineState.activeWordsAfter 17 Padding.messageOffset input.size)
      (Padding.messageOffset + input.size) 1 < 2 ^ 256 at haw₂_lt
  norm_num at haw₁_lt haw₂_lt
  rw [Nat.mod_eq_of_lt haw₁_lt, Nat.mod_eq_of_lt haw₂_lt]
  dsimp [aw₁, aw₂] at hmem₁ hmem₂
  have hmem17 : MachineState.memCost 17 = 51 := by decide
  rw [hmem17] at hmem₁ ⊢
  omega

private theorem lengthCondition_cost (input : ByteArray)
    (i : Nat) (hi : i < 8) :
    Challenge.EvmProof.Stepper.runLocatedBlockCost
      PaddingTrace.lengthConditionPath
      (PaddingTrace.lengthLoopState input i) = 25 := by
  have hi256 : i < 2 ^ 256 := by omega
  have hiWord : (UInt256.ofNat i).toNat = i := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hi256]
  have hlt : UInt256.lt (UInt256.ofNat i) (UInt256.ofNat 8) =
      UInt256.ofNat 1 := by
    simp [UInt256.lt, hiWord, Challenge.EvmProof.Word.word_toNat_ofNat, hi]
  have hzero : UInt256.isZero (UInt256.ofNat 1) = (⟨0⟩ : UInt256) := by decide
  have hzeroToNat : (⟨0⟩ : UInt256).toNat = 0 := rfl
  simp [Challenge.EvmProof.Stepper.runLocatedBlockCost,
    PaddingTrace.lengthConditionPath, PaddingTrace.lengthIterationPath,
    Challenge.EvmProof.Stepper.instrCost,
    Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr, Gas.baseCost,
    PaddingTrace.lengthLoopState, hlt, hzero]

private theorem lengthByte_cost (input : ByteArray) (i : Nat) :
    Challenge.EvmProof.Stepper.runLocatedBlockCost
      PaddingTrace.lengthBytePath (PaddingTrace.lengthBodyState input i) = 27 := by
  simp [Challenge.EvmProof.Stepper.runLocatedBlockCost,
    PaddingTrace.lengthBytePath, PaddingTrace.lengthIterationPath,
    Challenge.EvmProof.Stepper.instrCost,
    Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr, Gas.baseCost,
    PaddingTrace.lengthBodyState, PaddingTrace.lengthLoopState]

private theorem lengthStore_cost (input : ByteArray) (hfit : CalldataFits input)
    (i : Nat) (hi : i < 8) :
    Challenge.EvmProof.Stepper.runLocatedBlockCost
      PaddingTrace.lengthStorePath (PaddingTrace.lengthByteState input i) =
      12 + (MachineState.memCost
          (PaddingTrace.lengthLoopActiveWords input (i + 1)).toNat -
        MachineState.memCost
          (PaddingTrace.lengthLoopActiveWords input i).toNat) := by
  have hoff := PaddingTrace.lengthOffset_add_toNat input hfit i (by omega)
  have haddr : Padding.messageOffset + Padding.paddedLength input.size - 8 + i + 1 <
      2 ^ 256 := by
    have hlt := Padding.paddedLength_lt input.size
    unfold CalldataFits at hfit
    norm_num [Padding.messageOffset] at hfit ⊢
    omega
  have haw_lt : MachineState.activeWordsAfter
      (PaddingTrace.lengthLoopActiveWords input i).toNat
      (Padding.messageOffset + Padding.paddedLength input.size - 8 + i) 1 <
      2 ^ 256 := by
    unfold MachineState.activeWordsAfter
    rw [if_neg (by decide : (1 : Nat) ≠ 0), Nat.max_lt]
    constructor
    · change (PaddingTrace.lengthLoopActiveWords input i).val.val < UInt256.size
      exact (PaddingTrace.lengthLoopActiveWords input i).val.isLt
    · have hdiv :
          (Padding.messageOffset + Padding.paddedLength input.size - 8 + i + 1 - 1) / 32 ≤
            Padding.messageOffset + Padding.paddedLength input.size - 8 + i + 1 - 1 :=
          Nat.div_le_self _ _
      omega
  simp [Challenge.EvmProof.Stepper.runLocatedBlockCost,
    PaddingTrace.lengthStorePath, PaddingTrace.lengthIterationPath,
    Challenge.EvmProof.Stepper.instrCost,
    Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr,
    Gas.totalCost, Gas.mstore8Total, MachineState.memExpansionDelta,
    Gas.baseCost, PaddingTrace.lengthByteState,
    PaddingTrace.lengthLoopState, PaddingTrace.lengthLoopActiveWords, hoff]
  norm_num at haw_lt
  rw [Nat.mod_eq_of_lt haw_lt]
  omega

private theorem lengthIncrement_cost (input : ByteArray)
    (i : Nat) (hi : i < 8) :
    Challenge.EvmProof.Stepper.runLocatedBlockCost
      PaddingTrace.lengthIncrementPath
      (PaddingTrace.lengthStoredState input i) = 14 := by
  have hiSucc : i + 1 < 2 ^ 256 := by omega
  have hadd : UInt256.ofNat i + UInt256.ofNat 1 = UInt256.ofNat (i + 1) :=
    Challenge.EvmProof.Word.ofNat_add_ofNat hiSucc
  simp [Challenge.EvmProof.Stepper.runLocatedBlockCost,
    PaddingTrace.lengthIncrementPath, PaddingTrace.lengthIterationPath,
    Challenge.EvmProof.Stepper.instrCost,
    Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr, Gas.baseCost,
    PaddingTrace.lengthStoredState, PaddingTrace.lengthLoopState, hadd,
    List.exchange]

private theorem lengthBack_cost (input : ByteArray) (i : Nat) :
    Challenge.EvmProof.Stepper.runLocatedBlockCost
      PaddingTrace.lengthBackPath
      (PaddingTrace.lengthIncrementedState input i) = 12 := by
  simp [Challenge.EvmProof.Stepper.runLocatedBlockCost,
    PaddingTrace.lengthBackPath, PaddingTrace.lengthIterationPath,
    Challenge.EvmProof.Stepper.instrCost,
    Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr, Gas.baseCost,
    PaddingTrace.lengthIncrementedState, PaddingTrace.lengthStoredState,
    PaddingTrace.lengthLoopState]

theorem lengthIteration_cost (input : ByteArray) (hfit : CalldataFits input)
    (i : Nat) (hi : i < 8) :
    (PaddingTrace.gasSteps_lengthIteration input i hi).cost =
      90 + (MachineState.memCost
          (PaddingTrace.lengthLoopActiveWords input (i + 1)).toNat -
        MachineState.memCost
          (PaddingTrace.lengthLoopActiveWords input i).toNat) := by
  simp only [PaddingTrace.gasSteps_lengthIteration,
    Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost]
  rw [lengthCondition_cost input i hi, lengthByte_cost input i,
    lengthStore_cost input hfit i hi, lengthIncrement_cost input i hi,
    lengthBack_cost input i]
  omega

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
  · change (PaddingTrace.lengthLoopActiveWords input i).val.val < UInt256.size
    exact (PaddingTrace.lengthLoopActiveWords input i).val.isLt
  · have hdiv :
        (Padding.messageOffset + Padding.paddedLength input.size - 8 + i + 1 - 1) / 32 ≤
          Padding.messageOffset + Padding.paddedLength input.size - 8 + i + 1 - 1 :=
        Nat.div_le_self _ _
    omega

private theorem lengthLoopActiveWords_succ_toNat (input : ByteArray)
    (hfit : CalldataFits input) (i : Nat) (hi : i < 8) :
    (PaddingTrace.lengthLoopActiveWords input (i + 1)).toNat =
      MachineState.activeWordsAfter
        (PaddingTrace.lengthLoopActiveWords input i).toNat
        (PaddingTrace.lengthOffsetWord input + UInt256.ofNat i).toNat 1 := by
  rw [PaddingTrace.lengthLoopActiveWords]
  rw [Challenge.EvmProof.Word.word_toNat_ofNat]
  exact Nat.mod_eq_of_lt (lengthActiveWordsAfter_lt input hfit i hi)

private theorem lengthLoopPotential_step (input : ByteArray)
    (hfit : CalldataFits input) (i : Nat) (hi : i < 8) :
    MachineState.memCost (PaddingTrace.lengthLoopActiveWords input i).toNat ≤
      MachineState.memCost
        (PaddingTrace.lengthLoopActiveWords input (i + 1)).toNat := by
  rw [lengthLoopActiveWords_succ_toNat input hfit i hi]
  exact memCost_monotone (activeWordsAfter_ge _ _ _)

private theorem iterateBounded_cost_of_potential_add {I : Nat → State}
    (count base : Nat) (potential : Nat → Nat)
    (body : ∀ i, i < count → Challenge.EvmProof.GasSteps (I i) (I (i + 1)))
    (hcost : ∀ i (hi : i < count),
      (body i hi).cost + potential i = base + potential (i + 1)) :
    (Challenge.EvmProof.GasSteps.iterateBounded count body).cost + potential 0 =
      count * base + potential count := by
  induction count with
  | zero => simp
  | succ count ih =>
      rw [Challenge.EvmProof.GasSteps.iterateBounded_succ_cost]
      have hih := ih
        (body := fun i hi => body i (Nat.lt_succ_of_lt hi))
        (hcost := fun i hi => hcost i (Nat.lt_succ_of_lt hi))
      have hlast := hcost count (Nat.lt_succ_self count)
      simp only [Nat.succ_mul]
      omega

theorem lengthLoop_cost_add (input : ByteArray) (hfit : CalldataFits input) :
    (PaddingTrace.gasSteps_lengthLoop input).cost +
        MachineState.memCost
          (PaddingTrace.lengthLoopActiveWords input 0).toNat =
      720 + MachineState.memCost
        (PaddingTrace.lengthLoopActiveWords input 8).toNat := by
  unfold PaddingTrace.gasSteps_lengthLoop
  apply iterateBounded_cost_of_potential_add 8 90
    (fun i => MachineState.memCost
      (PaddingTrace.lengthLoopActiveWords input i).toNat)
  intro i hi
  rw [lengthIteration_cost input hfit i hi]
  have hmono := lengthLoopPotential_step input hfit i hi
  omega

private def paddingTargetWords (input : ByteArray) : Nat :=
  89 + 2 * ((input.size + 72) / 64)

private theorem paddingTargetWords_mul (input : ByteArray) :
    paddingTargetWords input * 32 =
      Padding.messageOffset + Padding.paddedLength input.size := by
  simp [paddingTargetWords, Padding.messageOffset, Padding.paddedLength]
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

private theorem padSentinel_activeWords_le (input : ByteArray)
    (hfit : CalldataFits input) :
    (PaddingTrace.padSentinel input).activeWords.toNat ≤
      paddingTargetWords input := by
  have hfooter := Padding.input_and_footer_fit input.size
  have hmul := paddingTargetWords_mul input
  have hstart : 17 ≤ paddingTargetWords input := by
    simp [paddingTargetWords]
    have : 0 < (input.size + 72) / 64 := by omega
    omega
  let aw₁ := MachineState.activeWordsAfter 17 Padding.messageOffset input.size
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
    show (PaddingTrace.padLengthReady input).activeWords.toNat = 17 by rfl]
  dsimp [aw₁, aw₂] at haw₁_lt haw₂_lt haw₂ ⊢
  rw [Nat.mod_eq_of_lt haw₁_lt, Nat.mod_eq_of_lt haw₂_lt]
  exact haw₂

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

theorem lengthLoopActiveWords_eight (input : ByteArray)
    (hfit : CalldataFits input) :
    (PaddingTrace.lengthLoopActiveWords input 8).toNat =
      89 + 2 * ((input.size + 72) / 64) := by
  have hupper7 := lengthLoopActiveWords_le input hfit 7 (by omega)
  rw [lengthLoopActiveWords_succ_toNat input hfit 7 (by omega)]
  unfold MachineState.activeWordsAfter
  rw [if_neg (by decide : (1 : Nat) ≠ 0)]
  have hoff := PaddingTrace.lengthOffset_add_toNat input hfit 7 (by omega)
  rw [hoff]
  have hmul := paddingTargetWords_mul input
  have htargetPos : 0 < paddingTargetWords input := by
    have hpad := Padding.paddedLength_pos input.size
    omega
  have hquot :
      (Padding.messageOffset + Padding.paddedLength input.size - 8 + 7 + 1 - 1) / 32 =
        paddingTargetWords input - 1 := by
    apply Nat.div_eq_of_lt_le
    · omega
    · omega
  dsimp only
  rw [hquot]
  have hone : 1 ≤ paddingTargetWords input := by omega
  rw [Nat.sub_add_cancel hone]
  change Nat.max (PaddingTrace.lengthLoopActiveWords input 7).toNat
    (paddingTargetWords input) = paddingTargetWords input
  exact Nat.max_eq_right hupper7

private theorem padReadSize_cost (input : ByteArray) :
    (PaddingTrace.gasSteps_padReadSize input).cost = 3 := by
  rfl

private theorem enterPad_cost (input : ByteArray) :
    (PaddingTrace.gasSteps_enterPad input).cost = 16 := by
  simp only [PaddingTrace.gasSteps_enterPad,
    Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.GasStep.pushN,
    Challenge.EvmProof.GasStep.push0,
    Challenge.EvmProof.GasStep.jump,
    Challenge.EvmProof.GasStep.of_running,
    id_eq,
    Challenge.EvmProof.GasSteps.one_cost]
  norm_num [PaddingTrace.pushedPad, PaddingTrace.pushedOutput,
    PaddingTrace.pushedReturn, Main.initializedState, Main.initStart,
    Main.applyInitStore, initialState, State.fork, Gas.baseCost]

private theorem lengthExitCompare_cost (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlockCost
      PaddingTrace.lengthExitComparePath
      (PaddingTrace.lengthLoopState input 8) = 9 := by
  simp [Challenge.EvmProof.Stepper.runLocatedBlockCost,
    PaddingTrace.lengthExitComparePath, PaddingTrace.lengthExitPath,
    Challenge.EvmProof.Stepper.instrCost,
    Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr, Gas.baseCost,
    PaddingTrace.lengthLoopState]

private theorem lengthExitBranch_cost (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlockCost
      PaddingTrace.lengthExitBranchPath
      (PaddingTrace.lengthExitComparedState input) = 16 := by
  have hzero : UInt256.isZero (⟨0⟩ : UInt256) = UInt256.ofNat 1 := by decide
  simp [Challenge.EvmProof.Stepper.runLocatedBlockCost,
    PaddingTrace.lengthExitBranchPath, PaddingTrace.lengthExitPath,
    Challenge.EvmProof.Stepper.instrCost,
    Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr, Gas.baseCost,
    PaddingTrace.lengthExitComparedState, PaddingTrace.lengthLoopState,
    hzero]

private theorem lengthExitPop_cost (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlockCost
      PaddingTrace.lengthExitPopPath
      (PaddingTrace.lengthExitBodyState input) = 9 := by
  simp [Challenge.EvmProof.Stepper.runLocatedBlockCost,
    PaddingTrace.lengthExitPopPath, PaddingTrace.lengthExitPath,
    Challenge.EvmProof.Stepper.instrCost,
    Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr, Gas.baseCost,
    PaddingTrace.lengthExitBodyState, PaddingTrace.lengthLoopState]

private theorem lengthExitReturn_cost (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlockCost
      PaddingTrace.lengthExitReturnPath
      (PaddingTrace.lengthExitPoppedState input) = 11 := by
  simp [Challenge.EvmProof.Stepper.runLocatedBlockCost,
    PaddingTrace.lengthExitReturnPath, PaddingTrace.lengthExitPath,
    Challenge.EvmProof.Stepper.instrCost,
    Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr, Gas.baseCost,
    PaddingTrace.lengthExitPoppedState, PaddingTrace.lengthLoopState,
    List.exchange]

private theorem lengthExit_cost (input : ByteArray) :
    (PaddingTrace.gasSteps_lengthExit input).cost = 45 := by
  simp only [PaddingTrace.gasSteps_lengthExit,
    Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost]
  rw [lengthExitCompare_cost input, lengthExitBranch_cost input,
    lengthExitPop_cost input, lengthExitReturn_cost input]

theorem lengthSetupLoop_cost (input : ByteArray) (hfit : CalldataFits input) :
    (PaddingTrace.gasSteps_lengthSetup input hfit).cost +
        (PaddingTrace.gasSteps_lengthLoop input).cost =
      722 + 3 * ((input.size + 31) / 32) +
        MachineState.memCost (89 + 2 * ((input.size + 72) / 64)) := by
  have hsetup := lengthSetup_cost input hfit
  have hloop := lengthLoop_cost_add input hfit
  change (PaddingTrace.gasSteps_lengthLoop input).cost +
      MachineState.memCost (PaddingTrace.padSentinel input).activeWords.toNat =
    720 + MachineState.memCost
      (PaddingTrace.lengthLoopActiveWords input 8).toNat at hloop
  rw [lengthLoopActiveWords_eight input hfit] at hloop
  rw [hsetup]
  omega

theorem gasSteps_pad_cost_of_fixed (input : ByteArray)
    (hfit : CalldataFits input)
    (hinit : (Main.gasSteps_initialize input).cost = 375)
    (hcompute : (PaddingTrace.gasSteps_computePaddedLength input).cost = 26) :
    (PaddingTrace.gasSteps_pad input hfit).cost =
      1187 + 3 * ((input.size + 31) / 32) +
        MachineState.memCost (89 + 2 * ((input.size + 72) / 64)) := by
  unfold PaddingTrace.gasSteps_pad
  simp only [Challenge.EvmProof.GasSteps.trans_cost]
  rw [hinit, enterPad_cost input, padReadSize_cost input, hcompute,
    lengthExit_cost input]
  have hsetupLoop := lengthSetupLoop_cost input hfit
  omega
private theorem toMain_cost (input : ByteArray) :
    (Reference.gasSteps_to_main input).cost = 179 := by
  rfl

private theorem mainJumpdest_cost (input : ByteArray) :
    (Main.gasSteps_mainJumpdest input).cost = 1 := by
  rfl

@[simp] theorem initStore_cost (s : State) (w : Artifact.InitStore)
    (hw : w ∈ Artifact.initStores)
    (hpc : s.pc = UInt256.ofNat (Artifact.instructionPC w.index))
    (hstack : s.stack = [])
    (hcode : s.executionEnv.code = referenceBytecode)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    (Main.gasSteps_initStore s w hw hpc hstack hcode hrun hnp).cost =
      6 + Gas.mstoreTotal
        { s with
          stack := w.offset :: w.value :: s.stack
          pc := s.pc + UInt256.ofNat (w.valueWidth.val + 1) +
            UInt256.ofNat (w.offsetWidth.val + 1) }
        w.offset := by
  simp only [Main.gasSteps_initStore,
    Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.GasSteps.cast_cost,
    Challenge.EvmProof.GasStep.pushN,
    Challenge.EvmProof.GasStep.of_running,
    Challenge.EvmProof.GasSteps.one_cost,
    Challenge.EvmProof.GasStep.mstore_cost]
  simp only [Artifact.initStores, List.mem_cons, List.not_mem_nil,
    or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num [Gas.baseCost, State.fork] <;> omega
theorem initStore_cost_add (s : State) (w : Artifact.InitStore)
    (hw : w ∈ Artifact.initStores)
    (hpc : s.pc = UInt256.ofNat (Artifact.instructionPC w.index))
    (hstack : s.stack = [])
    (hcode : s.executionEnv.code = referenceBytecode)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    (Main.gasSteps_initStore s w hw hpc hstack hcode hrun hnp).cost +
        MachineState.memCost s.activeWords.toNat =
      9 + MachineState.memCost (Main.applyInitStore s w).activeWords.toNat := by
  rw [initStore_cost]
  have hcurr : s.activeWords.toNat < 2 ^ 256 := by
    change s.activeWords.val.val < UInt256.size
    exact s.activeWords.val.isLt
  have hoff : w.offset.toNat ≤ 512 := by
    simp only [Artifact.initStores, List.mem_cons, List.not_mem_nil,
      or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      decide
  have hnext_lt : MachineState.activeWordsAfter s.activeWords.toNat
      w.offset.toNat 32 < 2 ^ 256 := by
    unfold MachineState.activeWordsAfter
    rw [if_neg (by decide : (32 : Nat) ≠ 0), Nat.max_lt]
    constructor
    · exact hcurr
    · have hdiv : (w.offset.toNat + 32 - 1) / 32 ≤
          w.offset.toNat + 32 - 1 := Nat.div_le_self _ _
      norm_num at hcurr ⊢
      omega
  have hmono := memCost_monotone
    (show s.activeWords.toNat ≤
      MachineState.activeWordsAfter s.activeWords.toNat w.offset.toNat 32 by
      unfold MachineState.activeWordsAfter
      rw [if_neg (by decide : (32 : Nat) ≠ 0)]
      exact Nat.le_max_left _ _)
  simp [Gas.mstoreTotal, MachineState.memExpansionDelta,
    Main.applyInitStore, State.activeWordsAfterUInt256, Gas.baseCost]
  norm_num at hnext_lt
  rw [Nat.mod_eq_of_lt hnext_lt]
  omega

theorem initStores_cost_add (s : State) :
    (ws : List Artifact.InitStore) →
    (hmem : ∀ w, w ∈ ws → w ∈ Artifact.initStores) →
    (hchain : Main.InitChain ws) →
    (hpc : ∀ w, ws.head? = some w →
      s.pc = UInt256.ofNat (Artifact.instructionPC w.index)) →
    (hstack : s.stack = []) →
    (hcode : s.executionEnv.code = referenceBytecode) →
    (hrun : s.halt = .Running) →
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) →
    (Main.gasSteps_initStores s ws hmem hchain hpc hstack hcode hrun hnp).cost +
        MachineState.memCost s.activeWords.toNat =
      ws.length * 9 +
        MachineState.memCost (ws.foldl Main.applyInitStore s).activeWords.toNat
  | [], _, _, _, _, _, _, _ => by
      simp [Main.gasSteps_initStores]
  | [w], hmem, hchain, hpc, hstack, hcode, hrun, hnp => by
      have hw : w ∈ Artifact.initStores := hmem w (by simp)
      have hpcw : s.pc = UInt256.ofNat (Artifact.instructionPC w.index) :=
        hpc w (by simp)
      have hone := initStore_cost_add s w hw hpcw hstack hcode hrun hnp
      simp only [Main.gasSteps_initStores,
        Challenge.EvmProof.GasSteps.cast_cost, List.length_cons,
        List.length_nil, List.foldl_cons, List.foldl_nil]
      omega

  | w :: next :: rest, hmem, hchain, hpc, hstack, hcode, hrun, hnp => by
      have hw : w ∈ Artifact.initStores := hmem w (by simp)
      have hpcw : s.pc = UInt256.ofNat (Artifact.instructionPC w.index) :=
        hpc w (by simp)
      have hhead := initStore_cost_add s w hw hpcw hstack hcode hrun hnp
      have hnext : next.index = w.index + 3 := hchain.1
      have htail : Main.InitChain (next :: rest) := hchain.2
      have hrest := initStores_cost_add (Main.applyInitStore s w)
        (next :: rest)
        (fun x hx => hmem x (List.mem_cons_of_mem w hx))
        htail
        (fun x hx => by
          simp only [List.head?_cons, Option.some.injEq] at hx
          subst x
          simp [Main.applyInitStore, hnext])
        (by simp [Main.applyInitStore])
        (by simpa [Main.applyInitStore] using hcode)
        (by simpa [Main.applyInitStore] using hrun)
        (by simpa [Main.applyInitStore] using hnp)
      simp only [List.length_cons, List.foldl_cons] at hrest
      simp only [Main.gasSteps_initStores,
        Challenge.EvmProof.GasSteps.cast_cost,
        Challenge.EvmProof.GasSteps.trans_cost, List.length_cons,
        List.foldl_cons]
      omega
theorem initStores_full_cost (input : ByteArray)
    (hmem : ∀ w, w ∈ Artifact.initStores → w ∈ Artifact.initStores)
    (hchain : Main.InitChain Artifact.initStores)
    (hpc : ∀ w, Artifact.initStores.head? = some w →
      (Main.initStart input).pc =
        UInt256.ofNat (Artifact.instructionPC w.index))
    (hstack : (Main.initStart input).stack = [])
    (hcode : (Main.initStart input).executionEnv.code = referenceBytecode)
    (hrun : (Main.initStart input).halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig (Main.initStart input).executionEnv.precompileConfig (Main.initStart input).executionEnv.fork
      (Main.initStart input).executionEnv.codeAddr = false) :
    (Main.gasSteps_initStores (Main.initStart input) Artifact.initStores
      hmem hchain hpc hstack hcode hrun hnp).cost = 195 := by
  have h := initStores_cost_add (Main.initStart input) Artifact.initStores
    hmem hchain hpc hstack hcode hrun hnp
  rw [show (Main.initStart input).activeWords.toNat = 0 by rfl,
    show (Artifact.initStores.foldl Main.applyInitStore
      (Main.initStart input)).activeWords.toNat = 17 by rfl] at h
  norm_num [Artifact.initStores, MachineState.memCost] at h ⊢
  omega

theorem initialize_cost (input : ByteArray) :
    (Main.gasSteps_initialize input).cost = 375 := by
  simp only [Main.gasSteps_initialize,
    Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.GasSteps.cast_cost]
  rw [toMain_cost, mainJumpdest_cost, initStores_full_cost]


theorem gasSteps_pad_cost (input : ByteArray) (hfit : CalldataFits input) :
    (PaddingTrace.gasSteps_pad input hfit).cost =
      1187 + 3 * ((input.size + 31) / 32) +
        MachineState.memCost (89 + 2 * ((input.size + 72) / 64)) := by
  exact gasSteps_pad_cost_of_fixed input hfit (initialize_cost input)
    (PaddingTrace.gasSteps_computePaddedLength_cost input)

end Challenge.Sha256.Reference.Proofs.Bytecode.PaddingGas
