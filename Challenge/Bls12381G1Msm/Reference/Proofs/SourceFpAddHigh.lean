import Challenge.Bls12381G1Msm.Reference.Proofs.SourceFpAddStart

set_option warningAsError true

/-! High-word staged assignment of the frozen G1MSM `fpAdd` helper. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM
open Challenge.EvmProof

theorem exec_fpAddStmt1 (ahi alo bhi blo : U256) (yst : EvmState) :
    Interp.execStmt modexpExec 16 fpAddBodyFuns
      (fpAddLowEnv ahi alo bhi blo) yst fpAddStmt1 =
    .ok (fpAddHighEnv ahi alo bhi blo, yst, .normal) := by
  rfl

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
