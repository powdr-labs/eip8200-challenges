import Challenge.Bls12381G2Msm.Reference.Proofs.SourceFpAddDefs

set_option warningAsError true

/-! Staged execution of the frozen G2MSM `fpAdd` body. -/

namespace Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM
open Challenge.EvmProof

theorem exec_fpAddStmt0 (ahi alo bhi blo : U256) (yst : EvmState) :
    Interp.execStmt modexpExec 61 fpAddBodyFuns
      (fpAddInitialEnv ahi alo bhi blo) yst fpAddStmt0 =
    .ok (fpAddLowEnv ahi alo bhi blo, yst, .normal) := by
  rfl

theorem exec_fpAddStmt1 (ahi alo bhi blo : U256) (yst : EvmState) :
    Interp.execStmt modexpExec 60 fpAddBodyFuns
      (fpAddLowEnv ahi alo bhi blo) yst fpAddStmt1 =
    .ok (fpAddHighEnv ahi alo bhi blo, yst, .normal) := by
  rfl

theorem eval_fpAddCondition (ahi alo bhi blo : U256) (yst : EvmState) :
    Interp.evalExpr modexpExec 58 fpAddBodyFuns
      (fpAddHighEnv ahi alo bhi blo) yst
      (.call "\x000" [.var "\x0051", .var "\x0052"]) =
    .ok (.vals [fpGeModulusValue (fpAddHighValue ahi alo bhi blo)
      (fpAddLowValue alo blo)] yst) := by
  rw [Interp.evalExpr]
  rfl

theorem exec_fpAddStmt2_keep (ahi alo bhi blo : U256) (yst : EvmState)
    (hkeep : fpGeModulusValue (fpAddHighValue ahi alo bhi blo)
      (fpAddLowValue alo blo) = 0) :
    Interp.execStmt modexpExec 59 fpAddBodyFuns
      (fpAddHighEnv ahi alo bhi blo) yst fpAddStmt2 =
    .ok (fpAddHighEnv ahi alo bhi blo, yst, .normal) := by
  unfold fpAddStmt2
  rw [Interp.execStmt, eval_fpAddCondition]
  simp [Dialect.zero, litValue, hkeep]

theorem exec_fpAddStmt2_correct (ahi alo bhi blo : U256) (yst : EvmState)
    (hcorrect : fpGeModulusValue (fpAddHighValue ahi alo bhi blo)
      (fpAddLowValue alo blo) ≠ 0) :
    Interp.execStmt modexpExec 59 fpAddBodyFuns
      (fpAddHighEnv ahi alo bhi blo) yst fpAddStmt2 =
    .ok (fpAddCorrectEnv ahi alo bhi blo, yst, .normal) := by
  unfold fpAddStmt2
  rw [Interp.execStmt, eval_fpAddCondition]
  simp only [Result.ok_bind, Dialect.zero, litValue]
  rw [if_neg (show fpGeModulusValue (fpAddHighValue ahi alo bhi blo)
    (fpAddLowValue alo blo) ≠ (0#256) from hcorrect)]
  simp [Interp.execStmt, Interp.execStmts, Interp.evalExpr, Interp.evalArgs,
    modexpExec, modexpBuiltinFn, stepOp, bin, litValue,
    VEnv.get, VEnv.setMany, VEnv.set, restore,
    fpAddHighEnv, fpAddLowEnv, fpAddInitialEnv, fpAddCorrectEnv,
    fpAddCorrectHighValue, fpAddCorrectLowValue,
    fpModulusHiValue, fpModulusLoValue,
    Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpModulusHiValue,
    Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpModulusLoValue]

end Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics
