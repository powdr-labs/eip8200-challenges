import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddLeftInfinity
import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddRightInfinity
import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddFinitePrefix
import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalXSubLeftPrefixRepair

set_option warningAsError true

/-! Complete frozen point-add execution for the two infinity identity branches. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

theorem step_pointAddFullLeftInfinity (yst : EvmState)
    (out left right : U256)
    (hinfinity : pointAddLeftInfinityValue yst out left right ≠ 0) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddInitialEnv out left right) yst pointAddBody
      (pointAddInitialEnv out left right)
      (pointAddLeftCopyState yst out left right) .leave := by
  have htail : ExecStmts Challenge.EvmProof.modexpExec.toDialect
      pointAddBodyFuns (pointAddInitialEnv out left right)
      (pointAddPrefixState yst out left right) pointAddAfterPrefix
      (pointAddInitialEnv out left right)
      (pointAddLeftCopyState yst out left right) .leave := by
    rw [pointAddAfterPrefix,
      show pointAddBody.drop 3 = pointAddStmt3 :: pointAddBody.drop 4 by rfl]
    exact Step.seqStop
      (step_pointAddLeftInfinity yst out left right hinfinity) (by decide)
  rw [show pointAddBody = pointAddBody.take 3 ++ pointAddAfterPrefix by
    exact (List.take_append_drop 3 pointAddBody).symm]
  exact step_pointAddUnequal_appendNormal
    (step_pointAddPrefix yst out left right) htail

theorem step_pointAddFullRightInfinity (yst : EvmState)
    (out left right : U256)
    (hleftFinite : pointAddLeftInfinityValue yst out left right = 0)
    (hrightInfinity : pointAddRightInfinityValue yst out left right ≠ 0) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddInitialEnv out left right) yst pointAddBody
      (pointAddInitialEnv out left right)
      (pointAddRightCopyState yst out left right) .leave := by
  have htail : ExecStmts Challenge.EvmProof.modexpExec.toDialect
      pointAddBodyFuns (pointAddInitialEnv out left right)
      (pointAddPrefixState yst out left right) pointAddAfterPrefix
      (pointAddInitialEnv out left right)
      (pointAddRightCopyState yst out left right) .leave := by
    rw [pointAddAfterPrefix,
      show pointAddBody.drop 3 =
        pointAddStmt3 :: pointAddStmt4 :: pointAddBody.drop 5 by rfl]
    exact Step.seqCons
      (step_pointAddLeftInfinityFalse yst out left right hleftFinite)
      (Step.seqStop
        (step_pointAddRightInfinity yst out left right hrightInfinity)
        (by decide))
  rw [show pointAddBody = pointAddBody.take 3 ++ pointAddAfterPrefix by
    exact (List.take_append_drop 3 pointAddBody).symm]
  exact step_pointAddUnequal_appendNormal
    (step_pointAddPrefix yst out left right) htail

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
