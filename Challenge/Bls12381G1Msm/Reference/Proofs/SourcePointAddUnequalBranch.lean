import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalNumeratorFull
import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalAfterNumerator

set_option warningAsError true

/-! Relational composition of the complete unequal-x point-add body. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def pointAddUnequalBranchCode : Block Op :=
  [pointAddUnequalNumeratorInitStmt, pointAddUnequalNumeratorStmt] ++
    pointAddUnequalAfterNumeratorCode

theorem pointAddUnequalBranchCode_eq :
    pointAddUnequalBranchCode = pointAddUnequalCode := by rfl

theorem step_pointAddUnequalBranch (yst : EvmState)
    (out left right : U256)
    (hhi : (pointAddUnequalDenominatorResult yst out left right).1.toNat <
      2 ^ 128)
    (hstate : pointAddUnequalDenominatorInputsState yst out left right =
      pointAddUnequalNumeratorInputsState yst out left right) :
    ∃ Vend stend,
      ExecStmts Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
        (pointAddInitialEnv out left right) (pointAddXEqState yst out left right)
        pointAddUnequalBranchCode Vend stend .normal := by
  obtain ⟨Vend, stend, hafter⟩ :=
    step_pointAddUnequalAfterNumerator yst out left right hhi hstate
  refine ⟨Vend, stend, ?_⟩
  rw [pointAddUnequalBranchCode]
  exact step_pointAddUnequal_appendNormal
    (step_pointAddUnequalNumerator yst out left right) hafter

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
