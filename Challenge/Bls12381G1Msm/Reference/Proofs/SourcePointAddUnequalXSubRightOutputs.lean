import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalXSubRightRepair
import Challenge.Bls12381G1Msm.Reference.Proofs.SourceAssignVar

set_option warningAsError true

/-! Generic output assignments of the second unequal-point x subtraction. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def pointAddUnequalXSubRightHighOutEnv (ctx : PointAddUnequalXSubRightContext) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  VEnv.set (pointAddUnequalXSubRightSelectedEnv ctx) "\x00136"
    (pointAddUnequalXSubRightResult ctx).1

def pointAddUnequalXSubRightWorkEnv (ctx : PointAddUnequalXSubRightContext) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  VEnv.set (pointAddUnequalXSubRightHighOutEnv ctx) "\x00137"
    (pointAddUnequalXSubRightResult ctx).2

theorem step_pointAddUnequalXSubRightOutHiGeneric
    (ctx : PointAddUnequalXSubRightContext) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect
      ([] :: pointAddBodyFuns) (pointAddUnequalXSubRightSelectedEnv ctx)
      (pointAddUnequalXSubRightRawState ctx) pointAddUnequalXSubRightOutHiStmt
      (pointAddUnequalXSubRightHighOutEnv ctx)
      (pointAddUnequalXSubRightRawState ctx) .normal := by
  rw [pointAddUnequalXSubRightOutHiStmt_eq]
  exact step_assignVar (pointAddUnequalXSubRightSelectedEnv_hi ctx)

private theorem highOutEnv_lo (ctx : PointAddUnequalXSubRightContext) :
    VEnv.get (pointAddUnequalXSubRightHighOutEnv ctx) "fc0_89" =
      some (pointAddUnequalXSubRightResult ctx).2 := by
  rw [pointAddUnequalXSubRightHighOutEnv,
    venv_get_set_ne _ _ _ _ (by decide)]
  exact pointAddUnequalXSubRightSelectedEnv_lo ctx

theorem step_pointAddUnequalXSubRightOutLoGeneric
    (ctx : PointAddUnequalXSubRightContext) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect
      ([] :: pointAddBodyFuns) (pointAddUnequalXSubRightHighOutEnv ctx)
      (pointAddUnequalXSubRightRawState ctx) pointAddUnequalXSubRightOutLoStmt
      (pointAddUnequalXSubRightWorkEnv ctx)
      (pointAddUnequalXSubRightRawState ctx) .normal := by
  rw [pointAddUnequalXSubRightOutLoStmt_eq]
  exact step_assignVar (highOutEnv_lo ctx)

theorem step_pointAddUnequalXSubRightOutputsGeneric
    (ctx : PointAddUnequalXSubRightContext) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect
      ([] :: pointAddBodyFuns) (pointAddUnequalXSubRightSelectedEnv ctx)
      (pointAddUnequalXSubRightRawState ctx)
      [pointAddUnequalXSubRightOutHiStmt, pointAddUnequalXSubRightOutLoStmt]
      (pointAddUnequalXSubRightWorkEnv ctx)
      (pointAddUnequalXSubRightRawState ctx) .normal :=
  Step.seqCons (step_pointAddUnequalXSubRightOutHiGeneric ctx)
    (Step.seqCons (step_pointAddUnequalXSubRightOutLoGeneric ctx) Step.seqNil)

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
