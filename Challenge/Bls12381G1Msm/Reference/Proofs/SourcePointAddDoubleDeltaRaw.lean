import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddDoubleDeltaWords

set_option warningAsError true

/-! Relational composition of the raw-word prefix of the generic delta subtraction. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def pointAddDoubleDeltaLocalsEnv (ctx : PointAddDoubleDeltaContext) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  [("fc0_47", pointAddDoubleDeltaLeftHi ctx),
   ("fc0_46", pointAddDoubleDeltaLeftLo ctx),
   ("fc0_45", ctx.x3Hi), ("fc0_44", ctx.x3Lo)]

private theorem pointAddDoubleDeltaLeftHiEnv_eq
    (ctx : PointAddDoubleDeltaContext) :
    pointAddDoubleDeltaLeftHiEnv ctx =
      pointAddDoubleDeltaLocalsEnv ctx ++
        pointAddDoubleDeltaInitialEnv ctx := by rfl

private theorem pointAddDoubleDeltaHighEnv_eq
    (ctx : PointAddDoubleDeltaContext) :
    pointAddDoubleDeltaHighEnv ctx =
      pointAddDoubleDeltaLocalsEnv ctx ++ pointAddDoubleDeltaRawEnv ctx := by
  rw [pointAddDoubleDeltaHighEnv, pointAddDoubleDeltaLowEnv,
    pointAddDoubleDeltaLeftHiEnv_eq]
  rw [venv_set_append_of_names_ne _ _ _ _
    (by simp [pointAddDoubleDeltaLocalsEnv])]
  rw [venv_set_append_of_names_ne _ _ _ _
    (by simp [pointAddDoubleDeltaLocalsEnv])]
  rfl

private theorem restore_pointAddDoubleDeltaHighEnv
    (ctx : PointAddDoubleDeltaContext) :
    restore (pointAddDoubleDeltaInitialEnv ctx)
      (pointAddDoubleDeltaHighEnv ctx) = pointAddDoubleDeltaRawEnv ctx := by
  rw [pointAddDoubleDeltaHighEnv_eq]
  apply restore_append_of_length_eq
  simp [pointAddDoubleDeltaInitialEnv, pointAddDoubleDeltaRawEnv, bindZeros]

theorem step_pointAddDoubleDeltaRawBodyGeneric
    (ctx : PointAddDoubleDeltaContext) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) (pointAddDoubleDeltaInitialEnv ctx)
      ctx.state pointAddDoubleDeltaRawBody
      (pointAddDoubleDeltaHighEnv ctx)
      (pointAddDoubleDeltaRawState ctx) .normal := by
  rw [pointAddDoubleDeltaRawBody_eq]
  exact Step.seqCons (step_pointAddDoubleDeltaLoVarGeneric ctx)
    (Step.seqCons (step_pointAddDoubleDeltaHiVarGeneric ctx)
      (Step.seqCons (step_pointAddDoubleDeltaLeftLoGeneric ctx)
        (Step.seqCons (step_pointAddDoubleDeltaLeftHiGeneric ctx)
          (Step.seqCons (step_pointAddDoubleDeltaLowGeneric ctx)
            (Step.seqCons (step_pointAddDoubleDeltaHighGeneric ctx)
              Step.seqNil)))))

theorem step_pointAddDoubleDeltaRawBlockGeneric
    (ctx : PointAddDoubleDeltaContext) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect
      ([] :: pointAddBodyFuns) (pointAddDoubleDeltaInitialEnv ctx)
      ctx.state pointAddDoubleDeltaRawBlockStmt
      (pointAddDoubleDeltaRawEnv ctx)
      (pointAddDoubleDeltaRawState ctx) .normal := by
  rw [pointAddDoubleDeltaRawBlockStmt_eq]
  rw [← restore_pointAddDoubleDeltaHighEnv]
  apply Step.block
  rw [hoist_pointAddDoubleDeltaRawBody]
  exact step_pointAddDoubleDeltaRawBodyGeneric ctx

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
