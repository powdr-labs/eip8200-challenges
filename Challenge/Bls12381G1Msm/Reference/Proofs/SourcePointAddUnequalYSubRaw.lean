import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalYSubWords

set_option warningAsError true

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def pointAddUnequalYSubLocalsEnv (ctx : PointAddUnequalYSubContext) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  [("fc0_107", ctx.inputHi), ("fc0_106", ctx.inputLo),
   ("fc0_105", pointAddUnequalYSubLeftHi ctx),
   ("fc0_104", pointAddUnequalYSubLeftLo ctx)]

private theorem hiVarEnv_eq (ctx : PointAddUnequalYSubContext) :
    pointAddUnequalYSubHiVarEnv ctx = pointAddUnequalYSubLocalsEnv ctx ++
      pointAddUnequalYSubInitialEnv ctx := by rfl

private theorem highEnv_eq (ctx : PointAddUnequalYSubContext) :
    pointAddUnequalYSubHighEnv ctx = pointAddUnequalYSubLocalsEnv ctx ++
      pointAddUnequalYSubRawEnv ctx := by
  rw [pointAddUnequalYSubHighEnv, pointAddUnequalYSubLowEnv, hiVarEnv_eq]
  rw [venv_set_append_of_names_ne _ _ _ _
    (by simp [pointAddUnequalYSubLocalsEnv])]
  rw [venv_set_append_of_names_ne _ _ _ _
    (by simp [pointAddUnequalYSubLocalsEnv])]
  rfl

private theorem restore_highEnv (ctx : PointAddUnequalYSubContext) :
    restore (pointAddUnequalYSubInitialEnv ctx) (pointAddUnequalYSubHighEnv ctx) =
      pointAddUnequalYSubRawEnv ctx := by
  rw [highEnv_eq]
  apply restore_append_of_length_eq
  simp [pointAddUnequalYSubInitialEnv, pointAddUnequalYSubRawEnv, bindZeros]

theorem step_pointAddUnequalYSubRawBodyGeneric (ctx : PointAddUnequalYSubContext) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) (pointAddUnequalYSubInitialEnv ctx)
      ctx.state pointAddUnequalYSubRawBody (pointAddUnequalYSubHighEnv ctx)
      (pointAddUnequalYSubRawState ctx) .normal := by
  rw [pointAddUnequalYSubRawBody_eq]
  exact Step.seqCons (step_pointAddUnequalYSubLeftLoGeneric ctx)
    (Step.seqCons (step_pointAddUnequalYSubLeftHiGeneric ctx)
      (Step.seqCons (step_pointAddUnequalYSubLoVarGeneric ctx)
        (Step.seqCons (step_pointAddUnequalYSubHiVarGeneric ctx)
          (Step.seqCons (step_pointAddUnequalYSubLowGeneric ctx)
            (Step.seqCons (step_pointAddUnequalYSubHighGeneric ctx) Step.seqNil)))))

theorem step_pointAddUnequalYSubRawBlockGeneric (ctx : PointAddUnequalYSubContext) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect
      ([] :: pointAddBodyFuns) (pointAddUnequalYSubInitialEnv ctx) ctx.state
      pointAddUnequalYSubRawBlockStmt (pointAddUnequalYSubRawEnv ctx)
      (pointAddUnequalYSubRawState ctx) .normal := by
  rw [pointAddUnequalYSubRawBlockStmt_eq, ← restore_highEnv]
  apply Step.block
  rw [hoist_pointAddUnequalYSubRawBody]
  exact step_pointAddUnequalYSubRawBodyGeneric ctx

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
