import Challenge.Bls12381G1Add.Reference.Proofs.SourceFpInvResultDefs

set_option warningAsError true

/-! # Frozen G1ADD `fpInv` input stores -/

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

/-- The first six source statements build the exact fixed-size MODEXP input. -/
theorem exec_fpInvStores (hi lo : U256) (yst : EvmState) :
    Interp.execStmts Challenge.EvmProof.modexpExec 66 fpInvBodyFuns
      (fpInvInitialEnv hi lo) yst
      [fpInvStmt0, fpInvStmt1, fpInvStmt2, fpInvStmt3, fpInvStmt4,
        fpInvStmt5] =
    .ok (fpInvInitialEnv hi lo, fpInvInputState yst hi lo, .normal) := by
  rfl

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
