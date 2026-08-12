import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalDeltaRepair
import Challenge.Bls12381G1Msm.Reference.Proofs.SourceAssignVar

set_option warningAsError true

/-! Output assignments for the generic delta subtraction. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def pointAddUnequalDeltaHighOutEnv (ctx : PointAddUnequalDeltaContext) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  VEnv.set (pointAddUnequalDeltaSelectedEnv ctx) "\x00138"
    (pointAddUnequalDeltaResult ctx).1

def pointAddUnequalDeltaWorkEnv (ctx : PointAddUnequalDeltaContext) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  VEnv.set (pointAddUnequalDeltaHighOutEnv ctx) "\x00139"
    (pointAddUnequalDeltaResult ctx).2

theorem step_pointAddUnequalDeltaOutHiGeneric
    (ctx : PointAddUnequalDeltaContext) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect
      ([] :: pointAddBodyFuns) (pointAddUnequalDeltaSelectedEnv ctx)
      (pointAddUnequalDeltaRawState ctx) pointAddUnequalDeltaOutHiStmt
      (pointAddUnequalDeltaHighOutEnv ctx)
      (pointAddUnequalDeltaRawState ctx) .normal := by
  rw [pointAddUnequalDeltaOutHiStmt_eq]
  exact step_assignVar (pointAddUnequalDeltaSelectedEnv_hi ctx)

private theorem highOutEnv_lo (ctx : PointAddUnequalDeltaContext) :
    VEnv.get (pointAddUnequalDeltaHighOutEnv ctx) "fc0_96" =
      some (pointAddUnequalDeltaResult ctx).2 := by
  rw [pointAddUnequalDeltaHighOutEnv,
    venv_get_set_ne _ _ _ _ (by decide)]
  exact pointAddUnequalDeltaSelectedEnv_lo ctx

theorem step_pointAddUnequalDeltaOutLoGeneric
    (ctx : PointAddUnequalDeltaContext) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect
      ([] :: pointAddBodyFuns) (pointAddUnequalDeltaHighOutEnv ctx)
      (pointAddUnequalDeltaRawState ctx) pointAddUnequalDeltaOutLoStmt
      (pointAddUnequalDeltaWorkEnv ctx)
      (pointAddUnequalDeltaRawState ctx) .normal := by
  rw [pointAddUnequalDeltaOutLoStmt_eq]
  exact step_assignVar (highOutEnv_lo ctx)

theorem step_pointAddUnequalDeltaOutputsGeneric
    (ctx : PointAddUnequalDeltaContext) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect
      ([] :: pointAddBodyFuns) (pointAddUnequalDeltaSelectedEnv ctx)
      (pointAddUnequalDeltaRawState ctx)
      [pointAddUnequalDeltaOutHiStmt, pointAddUnequalDeltaOutLoStmt]
      (pointAddUnequalDeltaWorkEnv ctx)
      (pointAddUnequalDeltaRawState ctx) .normal :=
  Step.seqCons (step_pointAddUnequalDeltaOutHiGeneric ctx)
    (Step.seqCons (step_pointAddUnequalDeltaOutLoGeneric ctx) Step.seqNil)

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
