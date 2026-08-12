import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddDoubleXSubRightLoads
import Challenge.Bls12381G1Msm.Reference.Proofs.SourceVEnvRestore

set_option warningAsError true

/-! Generic variable-read stages of the second point-double x subtraction. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def pointAddDoubleXSubRightLoVarEnv (ctx : PointAddDoubleXSubRightContext) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  ("fc0_39", ctx.x3Lo) :: pointAddDoubleXSubRightHiEnv ctx

def pointAddDoubleXSubRightHiVarEnv (ctx : PointAddDoubleXSubRightContext) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  ("fc0_40", ctx.x3Hi) :: pointAddDoubleXSubRightLoVarEnv ctx

private theorem pointAddDoubleXSubRightHiEnv_lo
    (ctx : PointAddDoubleXSubRightContext) :
    VEnv.get (pointAddDoubleXSubRightHiEnv ctx) "\x00123" =
      some ctx.x3Lo := by
  rw [pointAddDoubleXSubRightHiEnv, pointAddDoubleXSubRightLoEnv,
    pointAddDoubleXSubRightInitialEnv]
  rw [venv_get_cons_ne _ _ _ _ (by decide)]
  rw [venv_get_cons_ne _ _ _ _ (by decide)]
  rw [venv_get_append_of_names_ne _ _ _ (by simp [bindZeros])]
  exact ctx.env_lo

theorem step_pointAddDoubleXSubRightLoVarGeneric
    (ctx : PointAddDoubleXSubRightContext) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) (pointAddDoubleXSubRightHiEnv ctx)
      (pointAddDoubleXSubRightRawState ctx) pointAddDoubleXSubRightRawStmt2
      (pointAddDoubleXSubRightLoVarEnv ctx)
      (pointAddDoubleXSubRightRawState ctx) .normal := by
  rw [pointAddDoubleXSubRightRawStmt2_eq]
  exact Step.letVal (Step.var (pointAddDoubleXSubRightHiEnv_lo ctx)) rfl

private theorem pointAddDoubleXSubRightLoVarEnv_hi
    (ctx : PointAddDoubleXSubRightContext) :
    VEnv.get (pointAddDoubleXSubRightLoVarEnv ctx) "\x00122" =
      some ctx.x3Hi := by
  rw [pointAddDoubleXSubRightLoVarEnv, pointAddDoubleXSubRightHiEnv,
    pointAddDoubleXSubRightLoEnv, pointAddDoubleXSubRightInitialEnv]
  rw [venv_get_cons_ne _ _ _ _ (by decide)]
  rw [venv_get_cons_ne _ _ _ _ (by decide)]
  rw [venv_get_cons_ne _ _ _ _ (by decide)]
  rw [venv_get_append_of_names_ne _ _ _ (by simp [bindZeros])]
  exact ctx.env_hi

theorem step_pointAddDoubleXSubRightHiVarGeneric
    (ctx : PointAddDoubleXSubRightContext) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) (pointAddDoubleXSubRightLoVarEnv ctx)
      (pointAddDoubleXSubRightRawState ctx) pointAddDoubleXSubRightRawStmt3
      (pointAddDoubleXSubRightHiVarEnv ctx)
      (pointAddDoubleXSubRightRawState ctx) .normal := by
  rw [pointAddDoubleXSubRightRawStmt3_eq]
  exact Step.letVal (Step.var (pointAddDoubleXSubRightLoVarEnv_hi ctx)) rfl

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
