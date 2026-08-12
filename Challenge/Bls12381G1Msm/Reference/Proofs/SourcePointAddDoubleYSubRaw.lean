import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddDoubleYSubWords

set_option warningAsError true

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def pointAddDoubleYSubLocalsEnv (ctx : PointAddDoubleYSubContext) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  [("fc0_54", ctx.inputHi), ("fc0_53", ctx.inputLo),
   ("fc0_52", pointAddDoubleYSubLeftHi ctx),
   ("fc0_51", pointAddDoubleYSubLeftLo ctx)]

private theorem hiVarEnv_eq (ctx : PointAddDoubleYSubContext) :
    pointAddDoubleYSubHiVarEnv ctx = pointAddDoubleYSubLocalsEnv ctx ++
      pointAddDoubleYSubInitialEnv ctx := by rfl

private theorem highEnv_eq (ctx : PointAddDoubleYSubContext) :
    pointAddDoubleYSubHighEnv ctx = pointAddDoubleYSubLocalsEnv ctx ++
      pointAddDoubleYSubRawEnv ctx := by
  rw [pointAddDoubleYSubHighEnv, pointAddDoubleYSubLowEnv, hiVarEnv_eq]
  rw [venv_set_append_of_names_ne _ _ _ _
    (by simp [pointAddDoubleYSubLocalsEnv])]
  rw [venv_set_append_of_names_ne _ _ _ _
    (by simp [pointAddDoubleYSubLocalsEnv])]
  rfl

private theorem restore_highEnv (ctx : PointAddDoubleYSubContext) :
    restore (pointAddDoubleYSubInitialEnv ctx) (pointAddDoubleYSubHighEnv ctx) =
      pointAddDoubleYSubRawEnv ctx := by
  rw [highEnv_eq]
  apply restore_append_of_length_eq
  simp [pointAddDoubleYSubInitialEnv, pointAddDoubleYSubRawEnv, bindZeros]

theorem step_pointAddDoubleYSubRawBodyGeneric (ctx : PointAddDoubleYSubContext) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) (pointAddDoubleYSubInitialEnv ctx)
      ctx.state pointAddDoubleYSubRawBody (pointAddDoubleYSubHighEnv ctx)
      (pointAddDoubleYSubRawState ctx) .normal := by
  rw [pointAddDoubleYSubRawBody_eq]
  exact Step.seqCons (step_pointAddDoubleYSubLeftLoGeneric ctx)
    (Step.seqCons (step_pointAddDoubleYSubLeftHiGeneric ctx)
      (Step.seqCons (step_pointAddDoubleYSubLoVarGeneric ctx)
        (Step.seqCons (step_pointAddDoubleYSubHiVarGeneric ctx)
          (Step.seqCons (step_pointAddDoubleYSubLowGeneric ctx)
            (Step.seqCons (step_pointAddDoubleYSubHighGeneric ctx) Step.seqNil)))))

theorem step_pointAddDoubleYSubRawBlockGeneric (ctx : PointAddDoubleYSubContext) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect
      ([] :: pointAddBodyFuns) (pointAddDoubleYSubInitialEnv ctx) ctx.state
      pointAddDoubleYSubRawBlockStmt (pointAddDoubleYSubRawEnv ctx)
      (pointAddDoubleYSubRawState ctx) .normal := by
  rw [pointAddDoubleYSubRawBlockStmt_eq, ← restore_highEnv]
  apply Step.block
  rw [hoist_pointAddDoubleYSubRawBody]
  exact step_pointAddDoubleYSubRawBodyGeneric ctx

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
