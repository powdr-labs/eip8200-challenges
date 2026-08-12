import Challenge.Bls12381G1Msm.Reference.Proofs.SourceFpAddCondition

set_option warningAsError true

/-! No-correction branch of the staged G1MSM `fpAdd` helper. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM
open Challenge.EvmProof

theorem exec_fpAddStmt2_keep (ahi alo bhi blo : U256) (yst : EvmState)
    (hkeep : fpGeModulusValue (fpAddHighValue ahi alo bhi blo)
      (fpAddLowValue alo blo) = 0) :
    Interp.execStmt modexpExec 33 fpAddBodyFuns
      (fpAddHighEnv ahi alo bhi blo) yst fpAddStmt2 =
    .ok (fpAddHighEnv ahi alo bhi blo, yst, .normal) := by
  unfold fpAddStmt2
  rw [Interp.execStmt, eval_fpAddCondition]
  simp [Dialect.zero, litValue, hkeep]

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
