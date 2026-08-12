import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalXSubRightHigh

set_option warningAsError true

/-! Generic relational composition of the second-subtraction raw-word prefix. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def pointAddUnequalXSubRightLocalsEnv (ctx : PointAddUnequalXSubRightContext) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  [("fc0_93", ctx.x3Hi), ("fc0_92", ctx.x3Lo),
   ("fc0_91", pointAddUnequalXSubRightHi ctx),
   ("fc0_90", pointAddUnequalXSubRightLo ctx)]

private theorem pointAddUnequalXSubRightHiVarEnv_eq
    (ctx : PointAddUnequalXSubRightContext) :
    pointAddUnequalXSubRightHiVarEnv ctx =
      pointAddUnequalXSubRightLocalsEnv ctx ++
        pointAddUnequalXSubRightInitialEnv ctx := by
  rfl

private theorem pointAddUnequalXSubRightHighEnv_eq
    (ctx : PointAddUnequalXSubRightContext) :
    pointAddUnequalXSubRightHighEnv ctx =
      pointAddUnequalXSubRightLocalsEnv ctx ++
        pointAddUnequalXSubRightRawEnv ctx := by
  rw [pointAddUnequalXSubRightHighEnv, pointAddUnequalXSubRightLowEnv,
    pointAddUnequalXSubRightHiVarEnv_eq]
  rw [venv_set_append_of_names_ne _ _ _ _
    (by simp [pointAddUnequalXSubRightLocalsEnv])]
  rw [venv_set_append_of_names_ne _ _ _ _
    (by simp [pointAddUnequalXSubRightLocalsEnv])]
  rfl

private theorem restore_pointAddUnequalXSubRightHighEnv
    (ctx : PointAddUnequalXSubRightContext) :
    restore (pointAddUnequalXSubRightInitialEnv ctx)
      (pointAddUnequalXSubRightHighEnv ctx) =
        pointAddUnequalXSubRightRawEnv ctx := by
  rw [pointAddUnequalXSubRightHighEnv_eq]
  apply restore_append_of_length_eq
  simp [pointAddUnequalXSubRightInitialEnv,
    pointAddUnequalXSubRightRawEnv, bindZeros]

theorem step_pointAddUnequalXSubRightRawBodyGeneric
    (ctx : PointAddUnequalXSubRightContext) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) (pointAddUnequalXSubRightInitialEnv ctx)
      ctx.state pointAddUnequalXSubRightRawBody
      (pointAddUnequalXSubRightHighEnv ctx)
      (pointAddUnequalXSubRightRawState ctx) .normal := by
  rw [pointAddUnequalXSubRightRawBody_eq]
  exact Step.seqCons (step_pointAddUnequalXSubRightLoGeneric ctx)
    (Step.seqCons (step_pointAddUnequalXSubRightHiGeneric ctx)
      (Step.seqCons (step_pointAddUnequalXSubRightLoVarGeneric ctx)
        (Step.seqCons (step_pointAddUnequalXSubRightHiVarGeneric ctx)
          (Step.seqCons (step_pointAddUnequalXSubRightLowGeneric ctx)
            (Step.seqCons (step_pointAddUnequalXSubRightHighGeneric ctx)
              Step.seqNil)))))

theorem step_pointAddUnequalXSubRightRawBlockGeneric
    (ctx : PointAddUnequalXSubRightContext) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect
      ([] :: pointAddBodyFuns) (pointAddUnequalXSubRightInitialEnv ctx)
      ctx.state pointAddUnequalXSubRightRawBlockStmt
      (pointAddUnequalXSubRightRawEnv ctx)
      (pointAddUnequalXSubRightRawState ctx) .normal := by
  rw [pointAddUnequalXSubRightRawBlockStmt_eq]
  rw [← restore_pointAddUnequalXSubRightHighEnv]
  apply Step.block
  rw [hoist_pointAddUnequalXSubRightRawBody]
  exact step_pointAddUnequalXSubRightRawBodyGeneric ctx

theorem step_pointAddUnequalXSubRightRawGeneric
    (ctx : PointAddUnequalXSubRightContext) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect
      ([] :: pointAddBodyFuns) ctx.env ctx.state
      (pointAddUnequalXSubRightTail.take 2)
      (pointAddUnequalXSubRightRawEnv ctx)
      (pointAddUnequalXSubRightRawState ctx) .normal := by
  rw [pointAddUnequalXSubRightRawPrefix_shape]
  exact Step.seqCons (step_pointAddUnequalXSubRightRawDeclGeneric ctx)
    (Step.seqCons (step_pointAddUnequalXSubRightRawBlockGeneric ctx) Step.seqNil)

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
