import Challenge.Bls12381G2Add.Reference.Proofs.SourceFp2MulVSum

set_option warningAsError true
/-! # Imaginary component of frozen G2ADD `fp2Mul` -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
open YulSemantics YulSemantics.EVM
private def mstoreState (yst : EvmState) (offset value : U256) : EvmState :=
  { touchMemory yst offset.toNat 32 with memory := storeWord yst.memory offset.toNat value }
def fp2MulAfterImagReads (yst : EvmState) (out a b : U256) : EvmState :=
  fp2AddReadState (fp2MulAfterVSumStores yst out a b)
    (BitVec.ofNat 256 1792) (BitVec.ofNat 256 1824)
    (BitVec.ofNat 256 1856) (BitVec.ofNat 256 1888)
def fp2MulImag (yst : EvmState) (out a b : U256) : U256 × U256 :=
  let s := fp2MulAfterVSumStores yst out a b
  fpSubValue (loadWord s.memory 1792) (loadWord s.memory 1824)
    (loadWord s.memory 1856) (loadWord s.memory 1888)
def fp2MulImagEnv (yst : EvmState) (out a b : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  [("\x00113", (fp2MulImag yst out a b).1), ("\x00114", (fp2MulImag yst out a b).2)] ++
    fp2MulInitialEnv out a b
def fp2MulAfterImagHigh (yst : EvmState) (out a b : U256) : EvmState :=
  mstoreState (fp2MulAfterImagReads yst out a b) (out + BitVec.ofNat 256 64)
    (fp2MulImag yst out a b).1
def fp2MulFinalState (yst : EvmState) (out a b : U256) : EvmState :=
  mstoreState (fp2MulAfterImagHigh yst out a b) (out + BitVec.ofNat 256 96)
    (fp2MulImag yst out a b).2

private def fp2MulImagCall : Expr Op := .call "\x005"
  [.builtin .mload [.lit (.number 1792)], .builtin .mload [.lit (.number 1824)],
    .builtin .mload [.lit (.number 1856)], .builtin .mload [.lit (.number 1888)]]
private theorem fp2MulStmt21_shape : fp2MulStmt21 =
    .assign ["\x00113", "\x00114"] fp2MulImagCall := by rfl
private theorem eval_fp2MulImagCall (yst : EvmState) (out a b : U256) :
    Interp.evalExpr Challenge.EvmProof.modexpExec 64 fp2MulBodyFuns
      (fp2MulVSumEnv yst out a b) (fp2MulAfterVSumStores yst out a b)
      fp2MulImagCall =
    .ok (.vals [(fp2MulImag yst out a b).1, (fp2MulImag yst out a b).2]
      (fp2MulAfterImagReads yst out a b)) := by
  let s := fp2MulAfterVSumStores yst out a b
  have hargs : Interp.evalArgs Challenge.EvmProof.modexpExec 63 fp2MulBodyFuns
      (fp2MulVSumEnv yst out a b) s
      [.builtin .mload [.lit (.number 1792)], .builtin .mload [.lit (.number 1824)],
        .builtin .mload [.lit (.number 1856)], .builtin .mload [.lit (.number 1888)]] =
    Interp.evalArgs Challenge.EvmProof.modexpExec 63 fp2Funs
      [("ahi", loadWord s.memory 1792), ("alo", loadWord s.memory 1824),
        ("bhi", loadWord s.memory 1856), ("blo", loadWord s.memory 1888)]
      (fp2MulAfterImagReads yst out a b)
      [.var "ahi", .var "alo", .var "bhi", .var "blo"] := by
    simp [Interp.evalArgs, Interp.evalExpr, fp2MulAfterImagReads,
      fp2AddReadState, s, Challenge.EvmProof.modexpExec,
      Challenge.EvmProof.modexpBuiltinFn, stepOp, EVM.litValue, VEnv.get]
  have hlookup : lookupFun fp2MulBodyFuns "\x005" = lookupFun fp2Funs "\x005" := by rfl
  rw [fp2MulImagCall, Interp.evalExpr_call_of_evalArgs_lookup_eq
    (fn := "\x005") hargs hlookup]
  rw [show fp2Funs = [hoist Challenge.EvmProof.modexpExec.toDialect
    Compilation.referenceCompiledBlock] by rfl, eval_fpSub]
  rfl
theorem exec_fp2MulStmt21 (yst : EvmState) (out a b : U256) :
    Interp.execStmt Challenge.EvmProof.modexpExec 65 fp2MulBodyFuns
      (fp2MulVSumEnv yst out a b) (fp2MulAfterVSumStores yst out a b)
      fp2MulStmt21 =
    .ok (fp2MulImagEnv yst out a b, fp2MulAfterImagReads yst out a b, .normal) := by
  rw [fp2MulStmt21_shape, Interp.execStmt, eval_fp2MulImagCall]
  rfl
private theorem fp2MulStmt22_shape : fp2MulStmt22 =
    .exprStmt (.builtin .mstore
      [.builtin .add [.var "\x00110", .lit (.number 64)],
        .var "\x00113"]) := by rfl
private theorem exec_fp2MulStmt22 (yst : EvmState) (out a b : U256) :
    Interp.execStmt Challenge.EvmProof.modexpExec 15 fp2MulBodyFuns
      (fp2MulImagEnv yst out a b) (fp2MulAfterImagReads yst out a b)
      fp2MulStmt22 =
    .ok (fp2MulImagEnv yst out a b, fp2MulAfterImagHigh yst out a b,
      .normal) := by
  have hout : VEnv.get (fp2MulImagEnv yst out a b) "\x00110" = some out := by rfl
  have hval : VEnv.get (fp2MulImagEnv yst out a b) "\x00113" =
      some (fp2MulImag yst out a b).1 := by rfl
  rw [fp2MulStmt22_shape, Interp.execStmt]
  simp [Interp.evalExpr, Interp.evalArgs, hout, hval,
    Challenge.EvmProof.modexpExec, Challenge.EvmProof.modexpBuiltinFn,
    stepOp, bin, EVM.litValue, fp2MulAfterImagHigh, mstoreState]
private theorem fp2MulStmt23_shape : fp2MulStmt23 =
    .exprStmt (.builtin .mstore
      [.builtin .add [.var "\x00110", .lit (.number 96)],
        .var "\x00114"]) := by rfl
private theorem exec_fp2MulStmt23Tail (yst : EvmState) (out a b : U256) :
    Interp.execStmts Challenge.EvmProof.modexpExec 15 fp2MulBodyFuns
      (fp2MulImagEnv yst out a b) (fp2MulAfterImagHigh yst out a b)
      [fp2MulStmt23] =
    .ok (fp2MulImagEnv yst out a b, fp2MulFinalState yst out a b,
      .normal) := by
  have hout : VEnv.get (fp2MulImagEnv yst out a b) "\x00110" = some out := by rfl
  have hval : VEnv.get (fp2MulImagEnv yst out a b) "\x00114" =
      some (fp2MulImag yst out a b).2 := by rfl
  rw [Interp.execStmts, fp2MulStmt23_shape, Interp.execStmt]
  simp [Interp.execStmts, Interp.evalExpr, Interp.evalArgs, hout, hval,
    Challenge.EvmProof.modexpExec, Challenge.EvmProof.modexpBuiltinFn,
    stepOp, bin, EVM.litValue, fp2MulFinalState, mstoreState]
theorem exec_fp2MulImagStores (yst : EvmState) (out a b : U256) :
    Interp.execStmts Challenge.EvmProof.modexpExec 16 fp2MulBodyFuns
      (fp2MulImagEnv yst out a b) (fp2MulAfterImagReads yst out a b)
      [fp2MulStmt22, fp2MulStmt23] =
    .ok (fp2MulImagEnv yst out a b, fp2MulFinalState yst out a b, .normal) := by
  exact Interp.execStmts_cons_normal
    (exec_fp2MulStmt22 yst out a b) (exec_fp2MulStmt23Tail yst out a b)
end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
