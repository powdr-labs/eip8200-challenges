import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalXSubRightLoads
import Challenge.Bls12381G1Msm.Reference.Proofs.SourceVEnvRestore

set_option warningAsError true

/-! Generic variable-read stages of the second unequal-point x subtraction. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def pointAddUnequalXSubRightLoVarEnv (ctx : PointAddUnequalXSubRightContext) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  ("fc0_92", ctx.x3Lo) :: pointAddUnequalXSubRightHiEnv ctx

def pointAddUnequalXSubRightHiVarEnv (ctx : PointAddUnequalXSubRightContext) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  ("fc0_93", ctx.x3Hi) :: pointAddUnequalXSubRightLoVarEnv ctx

private theorem pointAddUnequalXSubRightHiEnv_lo
    (ctx : PointAddUnequalXSubRightContext) :
    VEnv.get (pointAddUnequalXSubRightHiEnv ctx) "\x00137" =
      some ctx.x3Lo := by
  rw [pointAddUnequalXSubRightHiEnv, pointAddUnequalXSubRightLoEnv,
    pointAddUnequalXSubRightInitialEnv]
  rw [venv_get_cons_ne _ _ _ _ (by decide)]
  rw [venv_get_cons_ne _ _ _ _ (by decide)]
  rw [venv_get_append_of_names_ne _ _ _ (by simp [bindZeros])]
  exact ctx.env_lo

theorem step_pointAddUnequalXSubRightLoVarGeneric
    (ctx : PointAddUnequalXSubRightContext) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) (pointAddUnequalXSubRightHiEnv ctx)
      (pointAddUnequalXSubRightRawState ctx) pointAddUnequalXSubRightRawStmt2
      (pointAddUnequalXSubRightLoVarEnv ctx)
      (pointAddUnequalXSubRightRawState ctx) .normal := by
  rw [pointAddUnequalXSubRightRawStmt2_eq]
  exact Step.letVal (Step.var (pointAddUnequalXSubRightHiEnv_lo ctx)) rfl

private theorem pointAddUnequalXSubRightLoVarEnv_hi
    (ctx : PointAddUnequalXSubRightContext) :
    VEnv.get (pointAddUnequalXSubRightLoVarEnv ctx) "\x00136" =
      some ctx.x3Hi := by
  rw [pointAddUnequalXSubRightLoVarEnv, pointAddUnequalXSubRightHiEnv,
    pointAddUnequalXSubRightLoEnv, pointAddUnequalXSubRightInitialEnv]
  rw [venv_get_cons_ne _ _ _ _ (by decide)]
  rw [venv_get_cons_ne _ _ _ _ (by decide)]
  rw [venv_get_cons_ne _ _ _ _ (by decide)]
  rw [venv_get_append_of_names_ne _ _ _ (by simp [bindZeros])]
  exact ctx.env_hi

theorem step_pointAddUnequalXSubRightHiVarGeneric
    (ctx : PointAddUnequalXSubRightContext) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) (pointAddUnequalXSubRightLoVarEnv ctx)
      (pointAddUnequalXSubRightRawState ctx) pointAddUnequalXSubRightRawStmt3
      (pointAddUnequalXSubRightHiVarEnv ctx)
      (pointAddUnequalXSubRightRawState ctx) .normal := by
  rw [pointAddUnequalXSubRightRawStmt3_eq]
  exact Step.letVal (Step.var (pointAddUnequalXSubRightLoVarEnv_hi ctx)) rfl

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
