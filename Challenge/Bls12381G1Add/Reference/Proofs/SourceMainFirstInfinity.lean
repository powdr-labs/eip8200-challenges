import Challenge.Bls12381G1Add.Reference.Proofs.SourceMainBothInfinity

set_option warningAsError true

/-! # Frozen G1ADD first-infinity identity branch -/

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

/-- The source statement that returns the second point when the first point is
infinity. -/
def mainFirstInfinityStmt : Stmt Op := mainPointScopeBody[5]!

private def mainCopySecondCall : Expr Op :=
  .call "\x0012"
    [.builtin .mload [.lit (.number 128)],
      .builtin .mload [.lit (.number 160)],
      .builtin .mload [.lit (.number 192)],
      .builtin .mload [.lit (.number 224)]]

/-- State after the source evaluates the four second-point loads from right to
left. -/
def mainFirstInfinityArgsState (yst : EvmState) : EvmState :=
  afterFourLoads (mainValidatedState yst) 128 160 192 224

/-- Exact four-`MSTORE` implementation of the frozen `storePoint` helper. -/
def mainStorePointState (yst : EvmState) (xHi xLo yHi yLo : U256) : EvmState :=
  let s0 := { touchMemory yst 0 32 with
    memory := storeWord yst.memory 0 xHi }
  let s1 := { touchMemory s0 32 32 with
    memory := storeWord s0.memory 32 xLo }
  let s2 := { touchMemory s1 64 32 with
    memory := storeWord s1.memory 64 yHi }
  { touchMemory s2 96 32 with
    memory := storeWord s2.memory 96 yLo }

/-- State after copying the second decoded point to the return window. -/
def mainFirstInfinityCopyState (yst : EvmState) : EvmState :=
  mainStorePointState (mainFirstInfinityArgsState yst)
    (mainDecodedWord yst 128) (mainDecodedWord yst 160)
    (mainDecodedWord yst 192) (mainDecodedWord yst 224)

/-- Exact state produced by the branch's `return(0, 128)`. -/
def mainFirstInfinityReturnState (yst : EvmState) : EvmState :=
  { touchMemory (mainFirstInfinityCopyState yst) 0 128 with
    halted := some (.ret,
      readBytes (mainFirstInfinityCopyState yst).memory 0 128) }

private theorem mainFirstInfinityStmt_shape : mainFirstInfinityStmt =
    .cond (.var "\x0096")
      [.exprStmt mainCopySecondCall,
       .exprStmt
        (.builtin .ret [.lit (.number 0), .lit (.number 128)])] := by
  rfl

/-- Point validation preserves every pre-scratch decoded input word. -/
theorem mainValidatedState_loadWord (yst : EvmState) (offset : Nat)
    (hend : offset + 32 ≤ 1024) :
    loadWord (mainValidatedState yst).memory offset =
      mainDecodedWord yst offset := by
  unfold mainValidatedState mainCurve2ArgsState mainAfterCurve1
    mainCurve1ArgsState onCurveFinalState onCurveState2 onCurveState1
  repeat' rw [fpMulFinalState_loadWord_before_scratch _ _ _ _ _ _ hend]
  simp [afterFourLoads, mainAfterInf2Reads, mainAfterInf1Reads,
    mainAfterCanonicalReads, mainAfterPaddingReads]
  repeat' rw [fpMulFinalState_loadWord_before_scratch _ _ _ _ _ _ hend]
  rfl

private theorem eval_mainCopySecondArgs
    (funs : FunEnv Challenge.EvmProof.modexpExec.toDialect) (yst : EvmState) :
    Interp.evalArgs Challenge.EvmProof.modexpExec 64 funs
      (mainPointEnv yst) (mainValidatedState yst)
      [.builtin .mload [.lit (.number 128)],
        .builtin .mload [.lit (.number 160)],
        .builtin .mload [.lit (.number 192)],
        .builtin .mload [.lit (.number 224)]] =
      .ok (.vals
        [mainDecodedWord yst 128, mainDecodedWord yst 160,
          mainDecodedWord yst 192, mainDecodedWord yst 224]
        (mainFirstInfinityArgsState yst)) := by
  simp [Interp.evalArgs, Interp.evalExpr, mainFirstInfinityArgsState,
    afterFourLoads, mainValidatedState_loadWord,
    Challenge.EvmProof.modexpExec, Challenge.EvmProof.modexpBuiltinFn,
    stepOp, EVM.litValue]

/-- Exact source execution of the frozen four-word `storePoint` helper. -/
theorem eval_storePoint (xHi xLo yHi yLo : U256) (yst : EvmState) :
    Interp.evalExpr Challenge.EvmProof.modexpExec 64 mainFuns
      [("\x0092", xHi), ("\x0093", xLo),
        ("\x0094", yHi), ("\x0095", yLo)] yst
      (.call "\x0012"
        [.var "\x0092", .var "\x0093", .var "\x0094", .var "\x0095"]) =
      .ok (.vals [] (mainStorePointState yst xHi xLo yHi yLo)) := by
  rw [Interp.evalExpr]
  rfl

private theorem eval_mainCopySecondCall (yst : EvmState) :
    Interp.evalExpr Challenge.EvmProof.modexpExec 65 ([] :: mainFuns)
      (mainPointEnv yst) (mainValidatedState yst) mainCopySecondCall =
      .ok (.vals [] (mainFirstInfinityCopyState yst)) := by
  have hargs := eval_mainCopySecondArgs ([] :: mainFuns) yst
  have hargs' :
      Interp.evalArgs Challenge.EvmProof.modexpExec 64 ([] :: mainFuns)
          (mainPointEnv yst) (mainValidatedState yst)
          [.builtin .mload [.lit (.number 128)],
            .builtin .mload [.lit (.number 160)],
            .builtin .mload [.lit (.number 192)],
            .builtin .mload [.lit (.number 224)]] =
        Interp.evalArgs Challenge.EvmProof.modexpExec 64 mainFuns
          [("\x0092", mainDecodedWord yst 128),
            ("\x0093", mainDecodedWord yst 160),
            ("\x0094", mainDecodedWord yst 192),
            ("\x0095", mainDecodedWord yst 224)]
          (mainFirstInfinityArgsState yst)
          [.var "\x0092", .var "\x0093", .var "\x0094", .var "\x0095"] := by
    rw [hargs]
    rfl
  have hlookup : lookupFun ([] :: mainFuns) "\x0012" =
      lookupFun mainFuns "\x0012" := rfl
  rw [mainCopySecondCall,
    Interp.evalExpr_call_of_evalArgs_lookup_eq hargs' hlookup]
  exact eval_storePoint _ _ _ _ _

private theorem sound_evalExpr {n funs V st expr result}
    (h : Interp.evalExpr Challenge.EvmProof.modexpExec n funs V st expr =
      .ok result) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect funs V st expr result :=
  (Interp.sound_all_of
    (E := Challenge.EvmProof.modexpExec)
    (fun _ _ _ _ hbuiltin =>
      Challenge.EvmProof.modexpBuiltinFn_sound hbuiltin) n).1
    _ _ _ _ _ h

/-- Exact source execution of the first-infinity identity branch. -/
theorem step_mainFirstInfinity_return (yst : EvmState)
    (hfirst : mainInf1 yst ≠ 0) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect mainFuns
      (mainPointEnv yst) (mainValidatedState yst) mainFirstInfinityStmt
      (mainPointEnv yst) (mainFirstInfinityReturnState yst) .halt := by
  rw [mainFirstInfinityStmt_shape]
  have hcondition : EvalExpr Challenge.EvmProof.modexpExec.toDialect mainFuns
      (mainPointEnv yst) (mainValidatedState yst) (.var "\x0096")
      (.vals [mainInf1 yst] (mainValidatedState yst)) := Step.var (by rfl)
  have hcall : EvalExpr Challenge.EvmProof.modexpExec.toDialect ([] :: mainFuns)
      (mainPointEnv yst) (mainValidatedState yst) mainCopySecondCall
      (.vals [] (mainFirstInfinityCopyState yst)) :=
    sound_evalExpr (eval_mainCopySecondCall yst)
  have hzero : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: mainFuns) (mainPointEnv yst) (mainFirstInfinityCopyState yst)
      (.lit (.number 0))
      (.vals [0] (mainFirstInfinityCopyState yst)) := Step.lit
  have hsize : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: mainFuns) (mainPointEnv yst) (mainFirstInfinityCopyState yst)
      (.lit (.number 128))
      (.vals [128] (mainFirstInfinityCopyState yst)) := Step.lit
  have hret : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: mainFuns) (mainPointEnv yst) (mainFirstInfinityCopyState yst)
      (.builtin .ret [.lit (.number 0), .lit (.number 128)])
      (.halt (mainFirstInfinityReturnState yst)) := by
    exact Step.builtinHalt
      (Step.argsCons (Step.argsCons Step.argsNil hsize) hzero) rfl
  have hseq : ExecStmts Challenge.EvmProof.modexpExec.toDialect
      ([] :: mainFuns) (mainPointEnv yst) (mainValidatedState yst)
      [.exprStmt mainCopySecondCall,
       .exprStmt
        (.builtin .ret [.lit (.number 0), .lit (.number 128)])]
      (mainPointEnv yst) (mainFirstInfinityReturnState yst) .halt := by
    exact Step.seqCons (Step.exprStmt hcall)
      (Step.seqStop (Step.exprStmtHalt hret) (by decide))
  have hseq' : ExecStmts Challenge.EvmProof.modexpExec.toDialect
      (hoist Challenge.EvmProof.modexpExec.toDialect
        [.exprStmt mainCopySecondCall,
         .exprStmt
          (.builtin .ret [.lit (.number 0), .lit (.number 128)])] :: mainFuns)
      (mainPointEnv yst) (mainValidatedState yst)
      [.exprStmt mainCopySecondCall,
       .exprStmt
        (.builtin .ret [.lit (.number 0), .lit (.number 128)])]
      (mainPointEnv yst) (mainFirstInfinityReturnState yst) .halt := by
    simpa [hoist] using hseq
  have hblock : ExecStmt Challenge.EvmProof.modexpExec.toDialect mainFuns
      (mainPointEnv yst) (mainValidatedState yst)
      (.block
        [.exprStmt mainCopySecondCall,
         .exprStmt
          (.builtin .ret [.lit (.number 0), .lit (.number 128)])])
      (mainPointEnv yst) (mainFirstInfinityReturnState yst) .halt := by
    have hblock' := Step.block
      (D := Challenge.EvmProof.modexpExec.toDialect) hseq'
    simpa [restore] using hblock'
  exact Step.ifTrue hcondition hfirst hblock

private theorem mainDecodedState_memory_forFirst (yst : EvmState) :
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

private theorem mainDecodedState_read128 (yst : EvmState) (input : ByteArray)
    (hcalldata : yst.env.calldata = input.toList) :
    readBytes (mainDecodedState yst).memory 128 32 =
      (EvmSemantics.MachineState.readPadded input 128 32).toList := by
  rw [mainDecodedState_memory_forFirst]
  simp only [mainInputWord, hcalldata]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 128 32 224 _ (by omega)]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 128 32 192 _ (by omega)]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 128 32 160 _ (by omega)]
  exact Challenge.EvmProof.ModexpMemory.readBytes_storeWord_wordFrom
    _ 128 128 input

private theorem mainDecodedState_read160 (yst : EvmState) (input : ByteArray)
    (hcalldata : yst.env.calldata = input.toList) :
    readBytes (mainDecodedState yst).memory 160 32 =
      (EvmSemantics.MachineState.readPadded input 160 32).toList := by
  rw [mainDecodedState_memory_forFirst]
  simp only [mainInputWord, hcalldata]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 160 32 224 _ (by omega)]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 160 32 192 _ (by omega)]
  exact Challenge.EvmProof.ModexpMemory.readBytes_storeWord_wordFrom
    _ 160 160 input

private theorem mainDecodedState_read192 (yst : EvmState) (input : ByteArray)
    (hcalldata : yst.env.calldata = input.toList) :
    readBytes (mainDecodedState yst).memory 192 32 =
      (EvmSemantics.MachineState.readPadded input 192 32).toList := by
  rw [mainDecodedState_memory_forFirst]
  simp only [mainInputWord, hcalldata]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 192 32 224 _ (by omega)]
  exact Challenge.EvmProof.ModexpMemory.readBytes_storeWord_wordFrom
    _ 192 192 input

private theorem mainDecodedState_read224 (yst : EvmState) (input : ByteArray)
    (hcalldata : yst.env.calldata = input.toList) :
    readBytes (mainDecodedState yst).memory 224 32 =
      (EvmSemantics.MachineState.readPadded input 224 32).toList := by
  rw [mainDecodedState_memory_forFirst]
  simp only [mainInputWord, hcalldata]
  exact Challenge.EvmProof.ModexpMemory.readBytes_storeWord_wordFrom
    _ 224 224 input

private theorem loadWord_eq_wordFrom_of_readBytes
    (memory : Nat → UInt8) (offset source : Nat) (input : ByteArray)
    (hbytes : readBytes memory offset 32 =
      (EvmSemantics.MachineState.readPadded input source 32).toList) :
    loadWord memory offset = wordFrom input.toList source := by
  have hload : loadWord memory offset =
      (readBytes memory offset 32).foldl
        (fun (acc : U256) byte =>
          (acc <<< (8 : Nat)) ||| BitVec.ofNat 256 byte.toNat) 0 := by
    unfold loadWord readBytes
    rw [List.foldl_map]
  rw [hload, hbytes,
    Challenge.EvmProof.Bytes.readPadded_toList]
  unfold wordFrom
  rw [List.foldl_map]

private theorem mainDecodedWord128_eq (yst : EvmState) (input : ByteArray)
    (hcalldata : yst.env.calldata = input.toList) :
    mainDecodedWord yst 128 = wordFrom input.toList 128 := by
  unfold mainDecodedWord
  exact loadWord_eq_wordFrom_of_readBytes _ 128 128 input
    (mainDecodedState_read128 yst input hcalldata)

private theorem mainDecodedWord160_eq (yst : EvmState) (input : ByteArray)
    (hcalldata : yst.env.calldata = input.toList) :
    mainDecodedWord yst 160 = wordFrom input.toList 160 := by
  unfold mainDecodedWord
  exact loadWord_eq_wordFrom_of_readBytes _ 160 160 input
    (mainDecodedState_read160 yst input hcalldata)

private theorem mainDecodedWord192_eq (yst : EvmState) (input : ByteArray)
    (hcalldata : yst.env.calldata = input.toList) :
    mainDecodedWord yst 192 = wordFrom input.toList 192 := by
  unfold mainDecodedWord
  exact loadWord_eq_wordFrom_of_readBytes _ 192 192 input
    (mainDecodedState_read192 yst input hcalldata)

private theorem mainDecodedWord224_eq (yst : EvmState) (input : ByteArray)
    (hcalldata : yst.env.calldata = input.toList) :
    mainDecodedWord yst 224 = wordFrom input.toList 224 := by
  unfold mainDecodedWord
  exact loadWord_eq_wordFrom_of_readBytes _ 224 224 input
    (mainDecodedState_read224 yst input hcalldata)

private theorem mainFirstInfinityCopyState_memory (yst : EvmState) :
    (mainFirstInfinityCopyState yst).memory =
      storeWord
        (storeWord
          (storeWord
            (storeWord (mainFirstInfinityArgsState yst).memory 0
              (mainDecodedWord yst 128))
            32 (mainDecodedWord yst 160))
          64 (mainDecodedWord yst 192))
        96 (mainDecodedWord yst 224) := by
  rfl

private theorem mainFirstInfinityCopyState_readOutput (yst : EvmState)
    (input : ByteArray) (hcalldata : yst.env.calldata = input.toList) :
    readBytes (mainFirstInfinityCopyState yst).memory 0 128 =
      (EvmSemantics.MachineState.readPadded input 128 128).toList := by
  rw [mainFirstInfinityCopyState_memory,
    mainDecodedWord128_eq yst input hcalldata,
    mainDecodedWord160_eq yst input hcalldata,
    mainDecodedWord192_eq yst input hcalldata,
    mainDecodedWord224_eq yst input hcalldata]
  rw [show 128 = 32 + 96 by omega,
    Challenge.EvmProof.ModexpMemory.readBytes_add]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 0 32 96 _ (by omega)]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 0 32 64 _ (by omega)]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 0 32 32 _ (by omega)]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_wordFrom]
  rw [show 96 = 32 + 64 by omega,
    Challenge.EvmProof.ModexpMemory.readBytes_add]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 32 32 96 _ (by omega)]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 32 32 64 _ (by omega)]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_wordFrom]
  rw [show 64 = 32 + 32 by omega,
    Challenge.EvmProof.ModexpMemory.readBytes_add]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_disjoint
    _ 64 32 96 _ (by omega)]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_wordFrom]
  rw [Challenge.EvmProof.ModexpMemory.readBytes_storeWord_wordFrom]
  rw [← Challenge.EvmProof.Bytes.readPadded_toList_add input 192 32 32]
  rw [← Challenge.EvmProof.Bytes.readPadded_toList_add input 160 32 64]
  rw [← Challenge.EvmProof.Bytes.readPadded_toList_add input 128 32 96]

private theorem decodeG1_right_size {input : ByteArray}
    {right : EvmSemantics.Crypto.Bls12381.Point}
    (hright : Challenge.Bls12381.ProofSupport.Codec.decodeG1 input 128 =
      some right) : 128 + 128 ≤ input.size := by
  obtain ⟨x, y, _hx, hy, _⟩ :=
    Challenge.Bls12381.ProofSupport.Codec.decodeG1_success_cases hright
  have hsize :=
    (Challenge.Bls12381.ProofSupport.Codec.decodeFp_eq_some_iff
      input (128 + Challenge.Bls12381.ProofSupport.Codec.fpBytes) y).mp hy |>.1
  simpa [Challenge.Bls12381.ProofSupport.Codec.fpBytes] using hsize

/-- The first-infinity branch copies the exact padded 128-byte calldata
window of the second point into returndata. -/
theorem mainFirstInfinity_returned_inputWindow (yst : EvmState)
    (input : ByteArray) (hcalldata : yst.env.calldata = input.toList) :
    (mainFirstInfinityReturnState yst).halted =
      some (HaltKind.ret,
        (EvmSemantics.MachineState.readPadded input 128 128).toList) := by
  change some (HaltKind.ret,
    readBytes (mainFirstInfinityCopyState yst).memory 0 128) = _
  rw [mainFirstInfinityCopyState_readOutput yst input hcalldata]

/-- The first-infinity branch returns the exact canonical encoding of the
other decoded point. -/
theorem mainFirstInfinity_returned_other (yst : EvmState) (input : ByteArray)
    (hcalldata : yst.env.calldata = input.toList)
    (right : EvmSemantics.Crypto.Bls12381.Point)
    (hright : Challenge.Bls12381.ProofSupport.Codec.decodeG1 input 128 =
      some right) :
    (mainFirstInfinityReturnState yst).halted =
      some (HaltKind.ret,
        (Challenge.Bls12381.ProofSupport.Codec.encodeG1 right).toList) := by
  change some (HaltKind.ret,
    readBytes (mainFirstInfinityCopyState yst).memory 0 128) = _
  rw [mainFirstInfinityCopyState_readOutput yst input hcalldata,
    Challenge.EvmProof.Bytes.readPadded_eq_extract input 128 128
      (decodeG1_right_size hright)]
  have hencode :=
    Challenge.Bls12381.ProofSupport.Codec.encodeG1_decodeG1 hright
  rw [Challenge.Bls12381.ProofSupport.Codec.g1Bytes] at hencode
  rw [← hencode]

/-- The returned point is the local lawful-affine identity result, not a
pinned inverse-dependent curve operation. -/
theorem mainFirstInfinity_returned_affineIdentity (yst : EvmState)
    (input : ByteArray) (hcalldata : yst.env.calldata = input.toList)
    (right : EvmSemantics.Crypto.Bls12381.Point)
    (hright : Challenge.Bls12381.ProofSupport.Codec.decodeG1 input 128 =
      some right) :
    (mainFirstInfinityReturnState yst).halted =
      some (HaltKind.ret,
        (Challenge.Bls12381.ProofSupport.Codec.encodeG1
          (Challenge.Bls12381.ProofSupport.G1Affine.toWire
            (Challenge.Bls12381.ProofSupport.G1Affine.add
              (Challenge.Bls12381.ProofSupport.G1Affine.ofWire
                (.infinity : EvmSemantics.Crypto.Bls12381.Point))
              (Challenge.Bls12381.ProofSupport.G1Affine.ofWire right)))).toList) := by
  rw [mainFirstInfinity_returned_other yst input hcalldata right hright]
  congr 3
  change Challenge.Bls12381.ProofSupport.Codec.encodeG1 right =
    Challenge.Bls12381.ProofSupport.Codec.encodeG1
      (Challenge.Bls12381.ProofSupport.G1Affine.toWire
        (Challenge.Bls12381.ProofSupport.G1Affine.ofWire right))
  rw [Challenge.Bls12381.ProofSupport.G1Affine.toWire_ofWire]

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
