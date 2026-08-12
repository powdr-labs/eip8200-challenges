import Challenge.Bls12381G1Msm.Reference.Proofs.SourceFpAddKeep

set_option warningAsError true

/-! Modulus-correction branch of the staged G1MSM `fpAdd` helper. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM
open Challenge.EvmProof

theorem exec_fpAddStmt2_correct (ahi alo bhi blo : U256) (yst : EvmState)
    (hcorrect : fpGeModulusValue (fpAddHighValue ahi alo bhi blo)
      (fpAddLowValue alo blo) ≠ 0) :
    Interp.execStmt modexpExec 33 fpAddBodyFuns
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
    fpAddHighEnv, fpAddCorrectEnv, fpAddCorrectHighValue,
    fpAddCorrectLowValue, fpAddLowValue]

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
