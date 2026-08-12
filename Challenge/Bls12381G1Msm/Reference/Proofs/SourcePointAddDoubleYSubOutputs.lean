import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddDoubleYSubRepair
import Challenge.Bls12381G1Msm.Reference.Proofs.SourceAssignVar

set_option warningAsError true

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def pointAddDoubleYSubHighOutEnv (ctx : PointAddDoubleYSubContext) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  VEnv.set (pointAddDoubleYSubSelectedEnv ctx) "\x00126"
    (pointAddDoubleYSubResult ctx).1
def pointAddDoubleYSubWorkEnv (ctx : PointAddDoubleYSubContext) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  VEnv.set (pointAddDoubleYSubHighOutEnv ctx) "\x00127"
    (pointAddDoubleYSubResult ctx).2

theorem step_pointAddDoubleYSubOutHiGeneric (ctx : PointAddDoubleYSubContext) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect
      ([] :: pointAddBodyFuns) (pointAddDoubleYSubSelectedEnv ctx)
      (pointAddDoubleYSubRawState ctx) pointAddDoubleYSubOutHiStmt
      (pointAddDoubleYSubHighOutEnv ctx) (pointAddDoubleYSubRawState ctx)
      .normal := by
  rw [pointAddDoubleYSubOutHiStmt_eq]
  exact step_assignVar (pointAddDoubleYSubSelectedEnv_hi ctx)

private theorem highOutEnv_lo (ctx : PointAddDoubleYSubContext) :
    VEnv.get (pointAddDoubleYSubHighOutEnv ctx) "fc0_50" =
      some (pointAddDoubleYSubResult ctx).2 := by
  rw [pointAddDoubleYSubHighOutEnv, venv_get_set_ne _ _ _ _ (by decide)]
  exact pointAddDoubleYSubSelectedEnv_lo ctx

theorem step_pointAddDoubleYSubOutLoGeneric (ctx : PointAddDoubleYSubContext) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect
      ([] :: pointAddBodyFuns) (pointAddDoubleYSubHighOutEnv ctx)
      (pointAddDoubleYSubRawState ctx) pointAddDoubleYSubOutLoStmt
      (pointAddDoubleYSubWorkEnv ctx) (pointAddDoubleYSubRawState ctx)
      .normal := by
  rw [pointAddDoubleYSubOutLoStmt_eq]
  exact step_assignVar (highOutEnv_lo ctx)

theorem step_pointAddDoubleYSubOutputsGeneric (ctx : PointAddDoubleYSubContext) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect
      ([] :: pointAddBodyFuns) (pointAddDoubleYSubSelectedEnv ctx)
      (pointAddDoubleYSubRawState ctx)
      [pointAddDoubleYSubOutHiStmt, pointAddDoubleYSubOutLoStmt]
      (pointAddDoubleYSubWorkEnv ctx) (pointAddDoubleYSubRawState ctx) .normal :=
  Step.seqCons (step_pointAddDoubleYSubOutHiGeneric ctx)
    (Step.seqCons (step_pointAddDoubleYSubOutLoGeneric ctx) Step.seqNil)

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
