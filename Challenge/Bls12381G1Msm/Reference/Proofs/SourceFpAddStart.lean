import Challenge.Bls12381G1Msm.Reference.Proofs.SourceFpAddDefs

set_option warningAsError true

/-! First staged assignment of the frozen G1MSM `fpAdd` helper. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM
open Challenge.EvmProof

theorem exec_fpAddStmt0 (ahi alo bhi blo : U256) (yst : EvmState) :
    Interp.execStmt modexpExec 16 fpAddBodyFuns
      (fpAddInitialEnv ahi alo bhi blo) yst fpAddStmt0 =
    .ok (fpAddLowEnv ahi alo bhi blo, yst, .normal) := by
  rfl

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
