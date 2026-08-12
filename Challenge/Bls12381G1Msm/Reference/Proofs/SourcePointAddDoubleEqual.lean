import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddDoubleBranch
import Challenge.Bls12381G1Msm.Reference.Proofs.SourceFunEnvInsert

set_option warningAsError true

/-! Relational wrapper for the complete equal-x, non-vertical doubling branch. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

theorem step_pointAddDoubleEqual (yst : EvmState) (out left right : U256)
    (hxeq : pointAddXEqValue yst out left right ≠ 0)
    (hzero : pointAddYZeroValue yst out left right = 0)
    (hhi : (pointAddDoubleDenResult yst out left right).1.toNat < 2 ^ 128) :
    ∃ Vend stend,
      ExecStmt Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
        (pointAddInitialEnv out left right) (pointAddFiniteState yst out left right)
        pointAddStmt5 Vend stend .leave := by
  obtain ⟨Vend, stend, hbranch⟩ :=
    step_pointAddDoubleBranch yst out left right hzero hhi
  have hbranch' : ExecStmts Challenge.EvmProof.modexpExec.toDialect
      ([] :: pointAddBodyFuns) (pointAddInitialEnv out left right)
      (pointAddXEqState yst out left right) pointAddXEqMainBody Vend stend
      .normal :=
    step_funEnvInsert hbranch (.here pointAddBodyFuns)
  have hbranch'' : ExecStmts Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) (pointAddInitialEnv out left right)
      (pointAddXEqState yst out left right) pointAddXEqMainBody Vend stend
      .normal :=
    step_funEnvInsert hbranch' (.here ([] :: pointAddBodyFuns))
  have hmain : ExecStmt Challenge.EvmProof.modexpExec.toDialect
      ([] :: pointAddBodyFuns) (pointAddInitialEnv out left right)
      (pointAddXEqState yst out left right) pointAddXEqMainStmt
      (restore (pointAddInitialEnv out left right) Vend) stend .normal := by
    rw [pointAddXEqMainStmt_eq]
    exact Step.block hbranch''
  have hbody : ExecStmt Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddInitialEnv out left right) (pointAddXEqState yst out left right)
      (.block pointAddXEqBody)
      (restore (pointAddInitialEnv out left right)
        (restore (pointAddInitialEnv out left right) Vend)) stend .leave := by
    rw [pointAddXEqBody_eq]
    exact Step.block
      (Step.seqCons hmain (Step.seqStop Step.leave (by decide)))
  refine ⟨restore (pointAddInitialEnv out left right)
    (restore (pointAddInitialEnv out left right) Vend), stend, ?_⟩
  rw [pointAddStmt5_eq]
  exact Step.ifTrue (step_pointAddXEq yst out left right) hxeq hbody

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
