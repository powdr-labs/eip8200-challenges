import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddDoubleDeltaRepair
import Challenge.Bls12381G1Msm.Reference.Proofs.SourceAssignVar

set_option warningAsError true

/-! Output assignments for the generic delta subtraction. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def pointAddDoubleDeltaHighOutEnv (ctx : PointAddDoubleDeltaContext) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  VEnv.set (pointAddDoubleDeltaSelectedEnv ctx) "\x00124"
    (pointAddDoubleDeltaResult ctx).1

def pointAddDoubleDeltaWorkEnv (ctx : PointAddDoubleDeltaContext) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  VEnv.set (pointAddDoubleDeltaHighOutEnv ctx) "\x00125"
    (pointAddDoubleDeltaResult ctx).2

theorem step_pointAddDoubleDeltaOutHiGeneric
    (ctx : PointAddDoubleDeltaContext) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect
      ([] :: pointAddBodyFuns) (pointAddDoubleDeltaSelectedEnv ctx)
      (pointAddDoubleDeltaRawState ctx) pointAddDoubleDeltaOutHiStmt
      (pointAddDoubleDeltaHighOutEnv ctx)
      (pointAddDoubleDeltaRawState ctx) .normal := by
  rw [pointAddDoubleDeltaOutHiStmt_eq]
  exact step_assignVar (pointAddDoubleDeltaSelectedEnv_hi ctx)

private theorem highOutEnv_lo (ctx : PointAddDoubleDeltaContext) :
    VEnv.get (pointAddDoubleDeltaHighOutEnv ctx) "fc0_43" =
      some (pointAddDoubleDeltaResult ctx).2 := by
  rw [pointAddDoubleDeltaHighOutEnv,
    venv_get_set_ne _ _ _ _ (by decide)]
  exact pointAddDoubleDeltaSelectedEnv_lo ctx

theorem step_pointAddDoubleDeltaOutLoGeneric
    (ctx : PointAddDoubleDeltaContext) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect
      ([] :: pointAddBodyFuns) (pointAddDoubleDeltaHighOutEnv ctx)
      (pointAddDoubleDeltaRawState ctx) pointAddDoubleDeltaOutLoStmt
      (pointAddDoubleDeltaWorkEnv ctx)
      (pointAddDoubleDeltaRawState ctx) .normal := by
  rw [pointAddDoubleDeltaOutLoStmt_eq]
  exact step_assignVar (highOutEnv_lo ctx)

theorem step_pointAddDoubleDeltaOutputsGeneric
    (ctx : PointAddDoubleDeltaContext) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect
      ([] :: pointAddBodyFuns) (pointAddDoubleDeltaSelectedEnv ctx)
      (pointAddDoubleDeltaRawState ctx)
      [pointAddDoubleDeltaOutHiStmt, pointAddDoubleDeltaOutLoStmt]
      (pointAddDoubleDeltaWorkEnv ctx)
      (pointAddDoubleDeltaRawState ctx) .normal :=
  Step.seqCons (step_pointAddDoubleDeltaOutHiGeneric ctx)
    (Step.seqCons (step_pointAddDoubleDeltaOutLoGeneric ctx) Step.seqNil)

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
