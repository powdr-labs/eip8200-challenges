import Challenge.Bls12381G1Add.Reference.Proofs.SourceMainPrefix

set_option warningAsError true

/-! # Frozen G1ADD both-infinity return branch -/

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

/-- The first statement after successful point validation. -/
def mainBothInfinityStmt : Stmt Op := mainPointScopeBody[4]!

/-- Exact source condition for the both-infinity return. -/
def mainBothInfinityValue (yst : EvmState) : U256 :=
  mainInf1 yst &&& mainInf2 yst

/-- Exact state produced by the source `return(0, 128)`. -/
def mainBothInfinityReturnState (yst : EvmState) : EvmState :=
  { touchMemory (mainValidatedState yst) 0 128 with
    halted := some (.ret, readBytes (mainValidatedState yst).memory 0 128) }

private theorem mainBothInfinityStmt_shape : mainBothInfinityStmt =
    .cond (.builtin .and [.var "\x0096", .var "\x0097"])
      [.exprStmt
        (.builtin .ret [.lit (.number 0), .lit (.number 128)])] := by
  rfl

/-- The source takes the both-infinity branch exactly when the conjunction of
the two frozen infinity words is nonzero. -/
theorem step_mainBothInfinity_return (yst : EvmState)
    (hboth : mainBothInfinityValue yst ≠ 0) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect mainFuns
      (mainPointEnv yst) (mainValidatedState yst) mainBothInfinityStmt
      (mainPointEnv yst) (mainBothInfinityReturnState yst) .halt := by
  rw [mainBothInfinityStmt_shape]
  have hinf1 : EvalExpr Challenge.EvmProof.modexpExec.toDialect mainFuns
      (mainPointEnv yst) (mainValidatedState yst) (.var "\x0096")
      (.vals [mainInf1 yst] (mainValidatedState yst)) := Step.var (by rfl)
  have hinf2 : EvalExpr Challenge.EvmProof.modexpExec.toDialect mainFuns
      (mainPointEnv yst) (mainValidatedState yst) (.var "\x0097")
      (.vals [mainInf2 yst] (mainValidatedState yst)) := Step.var (by rfl)
  have hcondition : EvalExpr Challenge.EvmProof.modexpExec.toDialect mainFuns
      (mainPointEnv yst) (mainValidatedState yst)
      (.builtin .and [.var "\x0096", .var "\x0097"])
      (.vals [mainBothInfinityValue yst] (mainValidatedState yst)) := by
    exact Step.builtinOk
      (Step.argsCons (Step.argsCons Step.argsNil hinf2) hinf1) rfl
  have hzero : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: mainFuns) (mainPointEnv yst) (mainValidatedState yst)
      (.lit (.number 0)) (.vals [0] (mainValidatedState yst)) := Step.lit
  have hsize : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: mainFuns) (mainPointEnv yst) (mainValidatedState yst)
      (.lit (.number 128)) (.vals [128] (mainValidatedState yst)) := Step.lit
  have hret : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: mainFuns) (mainPointEnv yst) (mainValidatedState yst)
      (.builtin .ret [.lit (.number 0), .lit (.number 128)])
      (.halt (mainBothInfinityReturnState yst)) := by
    exact Step.builtinHalt
      (Step.argsCons (Step.argsCons Step.argsNil hsize) hzero) rfl
  have hseq : ExecStmts Challenge.EvmProof.modexpExec.toDialect
      ([] :: mainFuns) (mainPointEnv yst) (mainValidatedState yst)
      [.exprStmt
        (.builtin .ret [.lit (.number 0), .lit (.number 128)])]
      (mainPointEnv yst) (mainBothInfinityReturnState yst) .halt := by
    exact Step.seqStop (Step.exprStmtHalt hret) (by decide)
  have hseq' : ExecStmts Challenge.EvmProof.modexpExec.toDialect
      (hoist Challenge.EvmProof.modexpExec.toDialect
        [.exprStmt
          (.builtin .ret [.lit (.number 0), .lit (.number 128)])] :: mainFuns)
      (mainPointEnv yst) (mainValidatedState yst)
      [.exprStmt
        (.builtin .ret [.lit (.number 0), .lit (.number 128)])]
      (mainPointEnv yst) (mainBothInfinityReturnState yst) .halt := by
    simpa [hoist] using hseq
  have hblock : ExecStmt Challenge.EvmProof.modexpExec.toDialect mainFuns
      (mainPointEnv yst) (mainValidatedState yst)
      (.block [.exprStmt
        (.builtin .ret [.lit (.number 0), .lit (.number 128)])])
      (mainPointEnv yst) (mainBothInfinityReturnState yst) .halt := by
    have hblock' := Step.block
      (D := Challenge.EvmProof.modexpExec.toDialect) hseq'
    simpa [restore] using hblock'
  exact Step.ifTrue hcondition hboth hblock

/-- Point validation preserves the 128-byte first-point output window. -/
theorem mainValidatedState_readOutput (yst : EvmState) :
    readBytes (mainValidatedState yst).memory 0 128 =
      readBytes (mainDecodedState yst).memory 0 128 := by
  unfold mainValidatedState mainCurve2ArgsState mainAfterCurve1
    mainCurve1ArgsState onCurveFinalState onCurveState2 onCurveState1
  repeat' rw [fpMulFinalState_readBytes_before_scratch _ _ _ _ _ _ _
    (by norm_num : 0 + 128 ≤ 1024)]
  simp [afterFourLoads, mainAfterInf2Reads, mainAfterInf1Reads,
    mainAfterCanonicalReads, mainAfterPaddingReads]
  repeat' rw [fpMulFinalState_readBytes_before_scratch _ _ _ _ _ _ _
    (by norm_num : 0 + 128 ≤ 1024)]
  rfl

private theorem mainDecodedState_memory (yst : EvmState) :
    (mainDecodedState yst).memory =
      storeWord
        (storeWord
          (storeWord
            (storeWord
              (storeWord
                (storeWord
                  (storeWord
                    (storeWord yst.memory 0 (mainInputWord yst 0))
                    32 (mainInputWord yst 32))
                  64 (mainInputWord yst 64))
                96 (mainInputWord yst 96))
              128 (mainInputWord yst 128))
            160 (mainInputWord yst 160))
          192 (mainInputWord yst 192))
        224 (mainInputWord yst 224) := by
  rfl

private theorem fourZeroWords (memory : Nat → UInt8) :
    readBytes
        (storeWord
          (storeWord
            (storeWord
              (storeWord memory 0 (0#256)) 32 (0#256))
            64 (0#256))
          96 (0#256))
        0 128 = List.replicate 128 0 := by
  rw [show 128 = 32 + 96 by omega,
    Challenge.EvmProof.ModexpMemory.readBytes_add]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 0 32 96 _ (by omega)]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 0 32 64 _ (by omega)]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 0 32 32 _ (by omega)]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_zero]
  rw [show 96 = 32 + 64 by omega,
    Challenge.EvmProof.ModexpMemory.readBytes_add]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 32 32 96 _ (by omega)]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 32 32 64 _ (by omega)]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_zero]
  rw [show 64 = 32 + 32 by omega,
    Challenge.EvmProof.ModexpMemory.readBytes_add]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 64 32 96 _ (by omega)]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_zero]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_zero]
  decide

private theorem wordFrom_replicate_zero (size offset : Nat)
    (hfit : offset + 32 ≤ size) :
    wordFrom (List.replicate size 0) offset = 0#256 := by
  unfold wordFrom
  have hbyte (i : Nat) (hi : i < 32) :
      byteFrom (List.replicate size 0) (offset + i) = 0 := by
    unfold byteFrom
    rw [List.getD_eq_getElem?_getD]
    rw [List.getElem?_replicate, if_pos (by omega)]
    rfl
  have hfold : ∀ (indices : List Nat) (acc : U256),
      (∀ i ∈ indices, i < 32) →
      indices.foldl (fun (acc : U256) i =>
          (acc <<< (8 : Nat)) |||
            BitVec.ofNat 256
              (byteFrom (List.replicate size 0) (offset + i)).toNat) acc =
        indices.foldl (fun (acc : U256) (_ : Nat) =>
          acc <<< (8 : Nat)) acc := by
    intro indices acc hall
    induction indices generalizing acc with
    | nil => rfl
    | cons i rest ih =>
        rw [List.foldl_cons, List.foldl_cons, hbyte i (hall i (by simp))]
        simp only [UInt8.toNat_zero, BitVec.or_zero]
        exact ih _ (fun j hj => hall j (by simp [hj]))
  rw [hfold (List.range 32) 0 (by intro i hi; simpa using hi)]
  decide

private theorem mainDecodedState_readOutput_zero (yst : EvmState)
    (hcalldata : yst.env.calldata = List.replicate 256 0) :
    readBytes (mainDecodedState yst).memory 0 128 =
      List.replicate 128 0 := by
  rw [mainDecodedState_memory]
  simp only [mainInputWord, hcalldata]
  have h0 := wordFrom_replicate_zero 256 0 (by omega)
  have h32 := wordFrom_replicate_zero 256 32 (by omega)
  have h64 := wordFrom_replicate_zero 256 64 (by omega)
  have h96 := wordFrom_replicate_zero 256 96 (by omega)
  rw [h0, h32, h64, h96]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 0 128 224 _ (by omega)]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 0 128 192 _ (by omega)]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 0 128 160 _ (by omega)]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 0 128 128 _ (by omega)]
  exact fourZeroWords yst.memory

/-- The both-infinity return path preserves the exact first canonical point
window loaded by the source, independently of the initial memory contents. -/
theorem mainBothInfinity_returned_inputWindow (yst : EvmState)
    (input : ByteArray) (hcalldata : yst.env.calldata = input.toList) :
    (mainBothInfinityReturnState yst).halted =
      some (HaltKind.ret,
        (EvmSemantics.MachineState.readPadded input 0 128).toList) := by
  change some (HaltKind.ret,
    readBytes (mainValidatedState yst).memory 0 128) = _
  rw [mainValidatedState_readOutput, mainDecodedState_memory]
  repeat' rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 0 128 224 _ (by omega)]
  repeat' rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 0 128 192 _ (by omega)]
  repeat' rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 0 128 160 _ (by omega)]
  repeat' rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 0 128 128 _ (by omega)]
  simp only [mainInputWord, hcalldata]
  rw [show 128 = 32 + 96 by omega,
    Challenge.EvmProof.ModexpMemory.readBytes_add,
    Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
      _ 0 32 96 _ (by omega),
    Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
      _ 0 32 64 _ (by omega),
    Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
      _ 0 32 32 _ (by omega),
    Challenge.EvmProof.ModexpMemory.readBytes_storeWord_wordFrom,
    show 96 = 32 + 64 by omega,
    Challenge.EvmProof.ModexpMemory.readBytes_add,
    Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
      _ 32 32 96 _ (by omega),
    Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
      _ 32 32 64 _ (by omega),
    Challenge.EvmProof.ModexpMemory.readBytes_storeWord_wordFrom,
    show 64 = 32 + 32 by omega,
    Challenge.EvmProof.ModexpMemory.readBytes_add,
    Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
      _ 64 32 96 _ (by omega),
    Challenge.EvmProof.ModexpMemory.readBytes_storeWord_wordFrom,
    Challenge.EvmProof.ModexpMemory.readBytes_storeWord_wordFrom]
  rw [← Challenge.EvmProof.Bytes.readPadded_toList_add input 64 32 32,
    ← Challenge.EvmProof.Bytes.readPadded_toList_add input 32 32 64,
    ← Challenge.EvmProof.Bytes.readPadded_toList_add input 0 32 96]

private theorem natToBytesPadded_zero (width : Nat) :
    EvmSemantics.Data.Bytes.natToBytesPadded 0 width =
      ByteArray.mk (Array.replicate width 0) := by
  apply ByteArray.ext_getElem
  · rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
    exact Array.size_replicate.symm
  · intro i hiLeft hiRight
    have hi : i < width := by
      rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size] at hiLeft
      exact hiLeft
    rw [← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hiLeft]
    rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_getElem?_getD
      _ _ _ hi]
    norm_num
    rw [← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hiRight]
    change 0 = (Array.replicate width 0)[i]?.getD 0
    rw [Array.getElem?_eq_getElem (by simpa using hi)]
    simp

/-- The local canonical G1 infinity encoding is exactly 128 zero bytes. -/
theorem encodeG1_infinity_toList :
    (Challenge.Bls12381.ProofSupport.Codec.encodeG1
      (.infinity : EvmSemantics.Crypto.Bls12381.Point)).toList =
      List.replicate 128 0 := by
  unfold Challenge.Bls12381.ProofSupport.Codec.encodeG1
    EvmSemantics.Crypto.Bls12381G1Add.encodePoint
    EvmSemantics.Crypto.Bls12381Codec.encodeFp
  change (EvmSemantics.Data.Bytes.natToBytesPadded 0 64 ++
    EvmSemantics.Data.Bytes.natToBytesPadded 0 64).toList = _
  rw [natToBytesPadded_zero, YulEvmCompiler.ByteArray.toList_eq_data,
    ByteArray.data_append, Array.toList_append]
  simp

/-- On canonical both-infinity calldata, the exact source output is 128 zero
bytes. -/
theorem mainBothInfinity_returned_zero_bytes (yst : EvmState)
    (hcalldata : yst.env.calldata = List.replicate 256 0) :
    (mainBothInfinityReturnState yst).halted =
      some (HaltKind.ret, List.replicate 128 0) := by
  change some (HaltKind.ret,
    readBytes (mainValidatedState yst).memory 0 128) = _
  rw [mainValidatedState_readOutput,
    mainDecodedState_readOutput_zero yst hcalldata]

/-- On the canonical both-infinity calldata, the exact returned source bytes
are the local EIP codec's canonical infinity encoding. -/
theorem mainBothInfinity_returned_infinity (yst : EvmState)
    (hcalldata : yst.env.calldata = List.replicate 256 0) :
    (mainBothInfinityReturnState yst).halted =
      some (HaltKind.ret,
        Challenge.Bls12381.ProofSupport.Codec.encodeG1
          (.infinity : EvmSemantics.Crypto.Bls12381.Point) |>.toList) := by
  rw [mainBothInfinity_returned_zero_bytes yst hcalldata,
    encodeG1_infinity_toList]

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
