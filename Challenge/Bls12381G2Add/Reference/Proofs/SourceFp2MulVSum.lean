import Challenge.Bls12381G2Add.Reference.Proofs.SourceFp2MulCross

set_option warningAsError true
/-! # Sum of component products in frozen G2ADD `fp2Mul` -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
open YulSemantics YulSemantics.EVM

private def mstoreState (yst : EvmState) (offset : Nat) (value : U256) : EvmState :=
  { touchMemory yst offset 32 with memory := storeWord yst.memory offset value }
def fp2MulAfterVSumReads (yst : EvmState) (out a b : U256) : EvmState :=
  fp2AddReadState (fp2MulAfterCrossStores yst out a b)
    (BitVec.ofNat 256 1536) (BitVec.ofNat 256 1568)
    (BitVec.ofNat 256 1600) (BitVec.ofNat 256 1632)
def fp2MulVSum (yst : EvmState) (out a b : U256) : U256 × U256 :=
  let s := fp2MulAfterCrossStores yst out a b
  fpAddValue (loadWord s.memory 1536) (loadWord s.memory 1568)
    (loadWord s.memory 1600) (loadWord s.memory 1632)
def fp2MulVSumEnv (yst : EvmState) (out a b : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  [("\x00113", (fp2MulVSum yst out a b).1), ("\x00114", (fp2MulVSum yst out a b).2)] ++
    fp2MulInitialEnv out a b
def fp2MulAfterVSumHigh (yst : EvmState) (out a b : U256) : EvmState :=
  mstoreState (fp2MulAfterVSumReads yst out a b) 1856 (fp2MulVSum yst out a b).1
def fp2MulAfterVSumStores (yst : EvmState) (out a b : U256) : EvmState :=
  mstoreState (fp2MulAfterVSumHigh yst out a b) 1888 (fp2MulVSum yst out a b).2

private def fp2MulVSumCall : Expr Op := .call "\x004"
  [.builtin .mload [.lit (.number 1536)], .builtin .mload [.lit (.number 1568)],
    .builtin .mload [.lit (.number 1600)], .builtin .mload [.lit (.number 1632)]]
private theorem fp2MulStmt18_shape : fp2MulStmt18 =
    .assign ["\x00113", "\x00114"] fp2MulVSumCall := by rfl
private theorem eval_fp2MulVSumCall (yst : EvmState) (out a b : U256) :
    Interp.evalExpr Challenge.EvmProof.modexpExec 64 fp2MulBodyFuns
      (fp2MulCrossEnv yst out a b) (fp2MulAfterCrossStores yst out a b)
      fp2MulVSumCall =
    .ok (.vals [(fp2MulVSum yst out a b).1, (fp2MulVSum yst out a b).2]
      (fp2MulAfterVSumReads yst out a b)) := by
  let s := fp2MulAfterCrossStores yst out a b
  have hargs : Interp.evalArgs Challenge.EvmProof.modexpExec 63 fp2MulBodyFuns
      (fp2MulCrossEnv yst out a b) s
      [.builtin .mload [.lit (.number 1536)], .builtin .mload [.lit (.number 1568)],
        .builtin .mload [.lit (.number 1600)], .builtin .mload [.lit (.number 1632)]] =
    Interp.evalArgs Challenge.EvmProof.modexpExec 63 fp2Funs
      [("ahi", loadWord s.memory 1536), ("alo", loadWord s.memory 1568),
        ("bhi", loadWord s.memory 1600), ("blo", loadWord s.memory 1632)]
      (fp2MulAfterVSumReads yst out a b)
      [.var "ahi", .var "alo", .var "bhi", .var "blo"] := by
    simp [Interp.evalArgs, Interp.evalExpr, fp2MulAfterVSumReads,
      fp2AddReadState, s, Challenge.EvmProof.modexpExec,
      Challenge.EvmProof.modexpBuiltinFn, stepOp, EVM.litValue, VEnv.get]
  have hlookup : lookupFun fp2MulBodyFuns "\x004" = lookupFun fp2Funs "\x004" := by rfl
  rw [fp2MulVSumCall, Interp.evalExpr_call_of_evalArgs_lookup_eq
    (fn := "\x004") hargs hlookup]
  rw [show fp2Funs = [hoist Challenge.EvmProof.modexpExec.toDialect
    Compilation.referenceCompiledBlock] by rfl, eval_fpAdd]
  rfl
theorem exec_fp2MulStmt18 (yst : EvmState) (out a b : U256) :
    Interp.execStmt Challenge.EvmProof.modexpExec 65 fp2MulBodyFuns
      (fp2MulCrossEnv yst out a b) (fp2MulAfterCrossStores yst out a b)
      fp2MulStmt18 =
    .ok (fp2MulVSumEnv yst out a b, fp2MulAfterVSumReads yst out a b, .normal) := by
  rw [fp2MulStmt18_shape, Interp.execStmt, eval_fp2MulVSumCall]
  rfl
theorem exec_fp2MulVSumStores (yst : EvmState) (out a b : U256) :
    Interp.execStmts Challenge.EvmProof.modexpExec 16 fp2MulBodyFuns
      (fp2MulVSumEnv yst out a b) (fp2MulAfterVSumReads yst out a b)
      [fp2MulStmt19, fp2MulStmt20] =
    .ok (fp2MulVSumEnv yst out a b, fp2MulAfterVSumStores yst out a b, .normal) := by rfl
end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
