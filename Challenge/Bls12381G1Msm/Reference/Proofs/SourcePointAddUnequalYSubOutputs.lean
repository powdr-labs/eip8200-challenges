import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalYSubRepair
import Challenge.Bls12381G1Msm.Reference.Proofs.SourceAssignVar

set_option warningAsError true

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def pointAddUnequalYSubHighOutEnv (ctx : PointAddUnequalYSubContext) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  VEnv.set (pointAddUnequalYSubSelectedEnv ctx) "\x00140"
    (pointAddUnequalYSubResult ctx).1
def pointAddUnequalYSubWorkEnv (ctx : PointAddUnequalYSubContext) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  VEnv.set (pointAddUnequalYSubHighOutEnv ctx) "\x00141"
    (pointAddUnequalYSubResult ctx).2

theorem step_pointAddUnequalYSubOutHiGeneric (ctx : PointAddUnequalYSubContext) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect
      ([] :: pointAddBodyFuns) (pointAddUnequalYSubSelectedEnv ctx)
      (pointAddUnequalYSubRawState ctx) pointAddUnequalYSubOutHiStmt
      (pointAddUnequalYSubHighOutEnv ctx) (pointAddUnequalYSubRawState ctx)
      .normal := by
  rw [pointAddUnequalYSubOutHiStmt_eq]
  exact step_assignVar (pointAddUnequalYSubSelectedEnv_hi ctx)

private theorem highOutEnv_lo (ctx : PointAddUnequalYSubContext) :
    VEnv.get (pointAddUnequalYSubHighOutEnv ctx) "fc0_103" =
      some (pointAddUnequalYSubResult ctx).2 := by
  rw [pointAddUnequalYSubHighOutEnv, venv_get_set_ne _ _ _ _ (by decide)]
  exact pointAddUnequalYSubSelectedEnv_lo ctx

theorem step_pointAddUnequalYSubOutLoGeneric (ctx : PointAddUnequalYSubContext) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect
      ([] :: pointAddBodyFuns) (pointAddUnequalYSubHighOutEnv ctx)
      (pointAddUnequalYSubRawState ctx) pointAddUnequalYSubOutLoStmt
      (pointAddUnequalYSubWorkEnv ctx) (pointAddUnequalYSubRawState ctx)
      .normal := by
  rw [pointAddUnequalYSubOutLoStmt_eq]
  exact step_assignVar (highOutEnv_lo ctx)

theorem step_pointAddUnequalYSubOutputsGeneric (ctx : PointAddUnequalYSubContext) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect
      ([] :: pointAddBodyFuns) (pointAddUnequalYSubSelectedEnv ctx)
      (pointAddUnequalYSubRawState ctx)
      [pointAddUnequalYSubOutHiStmt, pointAddUnequalYSubOutLoStmt]
      (pointAddUnequalYSubWorkEnv ctx) (pointAddUnequalYSubRawState ctx) .normal :=
  Step.seqCons (step_pointAddUnequalYSubOutHiGeneric ctx)
    (Step.seqCons (step_pointAddUnequalYSubOutLoGeneric ctx) Step.seqNil)

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
