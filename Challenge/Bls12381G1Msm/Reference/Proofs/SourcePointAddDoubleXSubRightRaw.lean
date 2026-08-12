import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddDoubleXSubRightHigh

set_option warningAsError true

/-! Generic relational composition of the second-subtraction raw-word prefix. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def pointAddDoubleXSubRightLocalsEnv (ctx : PointAddDoubleXSubRightContext) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  [("fc0_40", ctx.x3Hi), ("fc0_39", ctx.x3Lo),
   ("fc0_38", pointAddDoubleXSubRightHi ctx),
   ("fc0_37", pointAddDoubleXSubRightLo ctx)]

private theorem pointAddDoubleXSubRightHiVarEnv_eq
    (ctx : PointAddDoubleXSubRightContext) :
    pointAddDoubleXSubRightHiVarEnv ctx =
      pointAddDoubleXSubRightLocalsEnv ctx ++
        pointAddDoubleXSubRightInitialEnv ctx := by
  rfl

private theorem pointAddDoubleXSubRightHighEnv_eq
    (ctx : PointAddDoubleXSubRightContext) :
    pointAddDoubleXSubRightHighEnv ctx =
      pointAddDoubleXSubRightLocalsEnv ctx ++
        pointAddDoubleXSubRightRawEnv ctx := by
  rw [pointAddDoubleXSubRightHighEnv, pointAddDoubleXSubRightLowEnv,
    pointAddDoubleXSubRightHiVarEnv_eq]
  rw [venv_set_append_of_names_ne _ _ _ _
    (by simp [pointAddDoubleXSubRightLocalsEnv])]
  rw [venv_set_append_of_names_ne _ _ _ _
    (by simp [pointAddDoubleXSubRightLocalsEnv])]
  rfl

private theorem restore_pointAddDoubleXSubRightHighEnv
    (ctx : PointAddDoubleXSubRightContext) :
    restore (pointAddDoubleXSubRightInitialEnv ctx)
      (pointAddDoubleXSubRightHighEnv ctx) =
        pointAddDoubleXSubRightRawEnv ctx := by
  rw [pointAddDoubleXSubRightHighEnv_eq]
  apply restore_append_of_length_eq
  simp [pointAddDoubleXSubRightInitialEnv,
    pointAddDoubleXSubRightRawEnv, bindZeros]

theorem step_pointAddDoubleXSubRightRawBodyGeneric
    (ctx : PointAddDoubleXSubRightContext) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) (pointAddDoubleXSubRightInitialEnv ctx)
      ctx.state pointAddDoubleXSubRightRawBody
      (pointAddDoubleXSubRightHighEnv ctx)
      (pointAddDoubleXSubRightRawState ctx) .normal := by
  rw [pointAddDoubleXSubRightRawBody_eq]
  exact Step.seqCons (step_pointAddDoubleXSubRightLoGeneric ctx)
    (Step.seqCons (step_pointAddDoubleXSubRightHiGeneric ctx)
      (Step.seqCons (step_pointAddDoubleXSubRightLoVarGeneric ctx)
        (Step.seqCons (step_pointAddDoubleXSubRightHiVarGeneric ctx)
          (Step.seqCons (step_pointAddDoubleXSubRightLowGeneric ctx)
            (Step.seqCons (step_pointAddDoubleXSubRightHighGeneric ctx)
              Step.seqNil)))))

theorem step_pointAddDoubleXSubRightRawBlockGeneric
    (ctx : PointAddDoubleXSubRightContext) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect
      ([] :: pointAddBodyFuns) (pointAddDoubleXSubRightInitialEnv ctx)
      ctx.state pointAddDoubleXSubRightRawBlockStmt
      (pointAddDoubleXSubRightRawEnv ctx)
      (pointAddDoubleXSubRightRawState ctx) .normal := by
  rw [pointAddDoubleXSubRightRawBlockStmt_eq]
  rw [← restore_pointAddDoubleXSubRightHighEnv]
  apply Step.block
  rw [hoist_pointAddDoubleXSubRightRawBody]
  exact step_pointAddDoubleXSubRightRawBodyGeneric ctx

theorem step_pointAddDoubleXSubRightRawGeneric
    (ctx : PointAddDoubleXSubRightContext) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect
      ([] :: pointAddBodyFuns) ctx.env ctx.state
      (pointAddDoubleXSubRightTail.take 2)
      (pointAddDoubleXSubRightRawEnv ctx)
      (pointAddDoubleXSubRightRawState ctx) .normal := by
  rw [pointAddDoubleXSubRightRawPrefix_shape]
  exact Step.seqCons (step_pointAddDoubleXSubRightRawDeclGeneric ctx)
    (Step.seqCons (step_pointAddDoubleXSubRightRawBlockGeneric ctx) Step.seqNil)

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
