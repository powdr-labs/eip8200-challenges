import Challenge.Bls12381G2Msm.Reference.Proofs.SourcePointAddUnequalBranch

set_option warningAsError true

/-! Frozen common postlude of finite G2MSM `pointAdd`. -/

namespace Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def pointAddPostBody : Block Op :=
  [pointAddStmt7, pointAddStmt8, pointAddStmt9, pointAddStmt10,
    pointAddStmt11, pointAddStmt12, pointAddStmt13]

theorem pointAddPostBody_eq : pointAddBody =
    [pointAddStmt0, pointAddStmt1, pointAddStmt2, pointAddStmt3,
      pointAddStmt4, pointAddStmt5, pointAddStmt6] ++ pointAddPostBody := by rfl

end Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics
