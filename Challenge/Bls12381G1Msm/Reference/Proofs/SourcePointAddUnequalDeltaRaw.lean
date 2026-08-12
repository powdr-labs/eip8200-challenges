import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalDeltaWords

set_option warningAsError true

/-! Relational composition of the raw-word prefix of the generic delta subtraction. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def pointAddUnequalDeltaLocalsEnv (ctx : PointAddUnequalDeltaContext) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  [("fc0_100", pointAddUnequalDeltaLeftHi ctx),
   ("fc0_99", pointAddUnequalDeltaLeftLo ctx),
   ("fc0_98", ctx.x3Hi), ("fc0_97", ctx.x3Lo)]

private theorem pointAddUnequalDeltaLeftHiEnv_eq
    (ctx : PointAddUnequalDeltaContext) :
    pointAddUnequalDeltaLeftHiEnv ctx =
      pointAddUnequalDeltaLocalsEnv ctx ++
        pointAddUnequalDeltaInitialEnv ctx := by rfl

private theorem pointAddUnequalDeltaHighEnv_eq
    (ctx : PointAddUnequalDeltaContext) :
    pointAddUnequalDeltaHighEnv ctx =
      pointAddUnequalDeltaLocalsEnv ctx ++ pointAddUnequalDeltaRawEnv ctx := by
  rw [pointAddUnequalDeltaHighEnv, pointAddUnequalDeltaLowEnv,
    pointAddUnequalDeltaLeftHiEnv_eq]
  rw [venv_set_append_of_names_ne _ _ _ _
    (by simp [pointAddUnequalDeltaLocalsEnv])]
  rw [venv_set_append_of_names_ne _ _ _ _
    (by simp [pointAddUnequalDeltaLocalsEnv])]
  rfl

private theorem restore_pointAddUnequalDeltaHighEnv
    (ctx : PointAddUnequalDeltaContext) :
    restore (pointAddUnequalDeltaInitialEnv ctx)
      (pointAddUnequalDeltaHighEnv ctx) = pointAddUnequalDeltaRawEnv ctx := by
  rw [pointAddUnequalDeltaHighEnv_eq]
  apply restore_append_of_length_eq
  simp [pointAddUnequalDeltaInitialEnv, pointAddUnequalDeltaRawEnv, bindZeros]

theorem step_pointAddUnequalDeltaRawBodyGeneric
    (ctx : PointAddUnequalDeltaContext) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) (pointAddUnequalDeltaInitialEnv ctx)
      ctx.state pointAddUnequalDeltaRawBody
      (pointAddUnequalDeltaHighEnv ctx)
      (pointAddUnequalDeltaRawState ctx) .normal := by
  rw [pointAddUnequalDeltaRawBody_eq]
  exact Step.seqCons (step_pointAddUnequalDeltaLoVarGeneric ctx)
    (Step.seqCons (step_pointAddUnequalDeltaHiVarGeneric ctx)
      (Step.seqCons (step_pointAddUnequalDeltaLeftLoGeneric ctx)
        (Step.seqCons (step_pointAddUnequalDeltaLeftHiGeneric ctx)
          (Step.seqCons (step_pointAddUnequalDeltaLowGeneric ctx)
            (Step.seqCons (step_pointAddUnequalDeltaHighGeneric ctx)
              Step.seqNil)))))

theorem step_pointAddUnequalDeltaRawBlockGeneric
    (ctx : PointAddUnequalDeltaContext) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect
      ([] :: pointAddBodyFuns) (pointAddUnequalDeltaInitialEnv ctx)
      ctx.state pointAddUnequalDeltaRawBlockStmt
      (pointAddUnequalDeltaRawEnv ctx)
      (pointAddUnequalDeltaRawState ctx) .normal := by
  rw [pointAddUnequalDeltaRawBlockStmt_eq]
  rw [← restore_pointAddUnequalDeltaHighEnv]
  apply Step.block
  rw [hoist_pointAddUnequalDeltaRawBody]
  exact step_pointAddUnequalDeltaRawBodyGeneric ctx

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
