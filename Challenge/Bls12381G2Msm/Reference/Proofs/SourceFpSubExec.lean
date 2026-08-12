import Challenge.Bls12381G2Msm.Reference.Proofs.SourceFpSubDefs

set_option warningAsError true

/-! Staged execution of the frozen G2MSM `fpSub` body. -/

namespace Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM
open Challenge.EvmProof

theorem exec_fpSubStmt0 (ahi alo bhi blo : U256) (yst : EvmState) :
    Interp.execStmt modexpExec 61 fpSubBodyFuns
      (fpSubInitialEnv ahi alo bhi blo) yst fpSubStmt0 =
    .ok (fpSubLowEnv ahi alo bhi blo, yst, .normal) := by
  rfl

theorem exec_fpSubStmt1 (ahi alo bhi blo : U256) (yst : EvmState) :
    Interp.execStmt modexpExec 60 fpSubBodyFuns
      (fpSubLowEnv ahi alo bhi blo) yst fpSubStmt1 =
    .ok (fpSubRawEnv ahi alo bhi blo, yst, .normal) := by
  rfl

theorem exec_fpSubStmt2 (ahi alo bhi blo : U256) (yst : EvmState) :
    Interp.execStmt modexpExec 59 fpSubBodyFuns
      (fpSubRawEnv ahi alo bhi blo) yst fpSubStmt2 =
    .ok (fpSubPreBranchEnv ahi alo bhi blo, yst, .normal) := by
  rfl

theorem eval_fpSubCondition (ahi alo bhi blo : U256) (yst : EvmState) :
    Interp.evalExpr modexpExec 57 fpSubBodyFuns
      (fpSubPreBranchEnv ahi alo bhi blo) yst
      (.builtin .gt [.var "\x0060", .var "\x0062"]) =
    .ok (.vals [b2w (BitVec.ult fpModulusHiValue
      (fpSubRawHighValue ahi alo bhi blo))] yst) := by
  rfl

theorem exec_fpSubStmt3_keep (ahi alo bhi blo : U256) (yst : EvmState)
    (hkeep : BitVec.ult fpModulusHiValue
      (fpSubRawHighValue ahi alo bhi blo) = false) :
    Interp.execStmt modexpExec 58 fpSubBodyFuns
      (fpSubPreBranchEnv ahi alo bhi blo) yst fpSubStmt3 =
    .ok (fpSubPreBranchEnv ahi alo bhi blo, yst, .normal) := by
  unfold fpSubStmt3
  rw [Interp.execStmt, eval_fpSubCondition]
  simp [Dialect.zero, b2w, litValue, hkeep]

theorem exec_fpSubStmt3_repair (ahi alo bhi blo : U256) (yst : EvmState)
    (hrepair : BitVec.ult fpModulusHiValue
      (fpSubRawHighValue ahi alo bhi blo) = true) :
    Interp.execStmt modexpExec 58 fpSubBodyFuns
      (fpSubPreBranchEnv ahi alo bhi blo) yst fpSubStmt3 =
    .ok (fpSubRepairedEnv ahi alo bhi blo, yst, .normal) := by
  unfold fpSubStmt3
  rw [Interp.execStmt, eval_fpSubCondition]
  simp only [Result.ok_bind, Dialect.zero, b2w, hrepair, litValue]
  simp [Interp.execStmt, Interp.execStmts, Interp.evalExpr, Interp.evalArgs,
    modexpExec, modexpBuiltinFn, stepOp, bin, litValue,
    VEnv.get, VEnv.setMany, VEnv.set, restore,
    fpSubPreBranchEnv, fpSubRawEnv, fpSubLowEnv, fpSubInitialEnv,
    fpSubRepairedEnv, fpSubRepairedHighValue, fpSubRepairedLowValue,
    fpModulusHiValue, fpModulusLoValue,
    Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpModulusHiValue,
    Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpModulusLoValue]

end Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics
