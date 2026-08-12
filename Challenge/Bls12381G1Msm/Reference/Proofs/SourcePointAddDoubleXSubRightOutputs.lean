import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddDoubleXSubRightRepair
import Challenge.Bls12381G1Msm.Reference.Proofs.SourceAssignVar

set_option warningAsError true

/-! Generic output assignments of the second point-double x subtraction. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def pointAddDoubleXSubRightHighOutEnv (ctx : PointAddDoubleXSubRightContext) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  VEnv.set (pointAddDoubleXSubRightSelectedEnv ctx) "\x00122"
    (pointAddDoubleXSubRightResult ctx).1

def pointAddDoubleXSubRightWorkEnv (ctx : PointAddDoubleXSubRightContext) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  VEnv.set (pointAddDoubleXSubRightHighOutEnv ctx) "\x00123"
    (pointAddDoubleXSubRightResult ctx).2

theorem step_pointAddDoubleXSubRightOutHiGeneric
    (ctx : PointAddDoubleXSubRightContext) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect
      ([] :: pointAddBodyFuns) (pointAddDoubleXSubRightSelectedEnv ctx)
      (pointAddDoubleXSubRightRawState ctx) pointAddDoubleXSubRightOutHiStmt
      (pointAddDoubleXSubRightHighOutEnv ctx)
      (pointAddDoubleXSubRightRawState ctx) .normal := by
  rw [pointAddDoubleXSubRightOutHiStmt_eq]
  exact step_assignVar (pointAddDoubleXSubRightSelectedEnv_hi ctx)

private theorem highOutEnv_lo (ctx : PointAddDoubleXSubRightContext) :
    VEnv.get (pointAddDoubleXSubRightHighOutEnv ctx) "fc0_36" =
      some (pointAddDoubleXSubRightResult ctx).2 := by
  rw [pointAddDoubleXSubRightHighOutEnv,
    venv_get_set_ne _ _ _ _ (by decide)]
  exact pointAddDoubleXSubRightSelectedEnv_lo ctx

theorem step_pointAddDoubleXSubRightOutLoGeneric
    (ctx : PointAddDoubleXSubRightContext) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect
      ([] :: pointAddBodyFuns) (pointAddDoubleXSubRightHighOutEnv ctx)
      (pointAddDoubleXSubRightRawState ctx) pointAddDoubleXSubRightOutLoStmt
      (pointAddDoubleXSubRightWorkEnv ctx)
      (pointAddDoubleXSubRightRawState ctx) .normal := by
  rw [pointAddDoubleXSubRightOutLoStmt_eq]
  exact step_assignVar (highOutEnv_lo ctx)

theorem step_pointAddDoubleXSubRightOutputsGeneric
    (ctx : PointAddDoubleXSubRightContext) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect
      ([] :: pointAddBodyFuns) (pointAddDoubleXSubRightSelectedEnv ctx)
      (pointAddDoubleXSubRightRawState ctx)
      [pointAddDoubleXSubRightOutHiStmt, pointAddDoubleXSubRightOutLoStmt]
      (pointAddDoubleXSubRightWorkEnv ctx)
      (pointAddDoubleXSubRightRawState ctx) .normal :=
  Step.seqCons (step_pointAddDoubleXSubRightOutHiGeneric ctx)
    (Step.seqCons (step_pointAddDoubleXSubRightOutLoGeneric ctx) Step.seqNil)

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
