import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddPrefix
import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddFinitePrefix
import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalXSubLeftPrefixRepair

set_option warningAsError true

/-! Opaque execution boundary through the two finite-point identity tests. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def pointAddFiniteEntryCode : Block Op := pointAddBody.take 5

theorem pointAddFiniteEntryCode_eq : pointAddFiniteEntryCode =
    [pointAddStmt0, pointAddStmt1, pointAddStmt2,
     pointAddStmt3, pointAddStmt4] := by rfl

theorem step_pointAddFiniteEntry (yst : EvmState) (out left right : U256)
    (hleft : pointAddLeftInfinityValue yst out left right = 0)
    (hright : pointAddRightInfinityValue yst out left right = 0) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddInitialEnv out left right) yst pointAddFiniteEntryCode
      (pointAddInitialEnv out left right)
      (pointAddFiniteState yst out left right) .normal := by
  rw [pointAddFiniteEntryCode_eq]
  exact step_pointAddUnequal_appendNormal
    (step_pointAddPrefix yst out left right)
    (step_pointAddFinitePrefix yst out left right hleft hright)

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
