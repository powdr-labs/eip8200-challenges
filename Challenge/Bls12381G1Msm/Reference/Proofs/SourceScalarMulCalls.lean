import Challenge.Bls12381G1Msm.Reference.Proofs.SourceScalarMulPost

set_option warningAsError true

/-! Relational call adapters for the two point additions in one scalar bit. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

private theorem scalarMulDoubleStmt_eq : scalarMulDoubleStmt =
    .exprStmt (.call "\x0016"
      [.var "\x00144", .var "\x00144", .var "\x00144"]) := by rfl

private theorem scalarMulAddStmt_eq : scalarMulAddStmt =
    .cond (.builtin .and [.var "\x00142", .var "\x00145"])
      [.exprStmt (.call "\x0016"
        [.var "\x00144", .var "\x00144", .var "\x00143"])] := by rfl

private theorem step_doubleArgs (yst : EvmState) (bit scalar point out : U256) :
    EvalArgs Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: scalarMulBodyFuns)
      (scalarMulLoopEnv bit scalar point out) yst
      [.var "\x00144", .var "\x00144", .var "\x00144"]
      (.vals [out, out, out] yst) :=
  Step.argsCons
    (Step.argsCons (Step.argsCons Step.argsNil (Step.var rfl)) (Step.var rfl))
    (Step.var rfl)

private theorem step_addArgs (yst : EvmState) (bit scalar point out : U256) :
    EvalArgs Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: [] :: scalarMulBodyFuns)
      (scalarMulLoopEnv bit scalar point out) yst
      [.var "\x00144", .var "\x00144", .var "\x00143"]
      (.vals [out, out, point] yst) :=
  Step.argsCons
    (Step.argsCons (Step.argsCons Step.argsNil (Step.var rfl)) (Step.var rfl))
    (Step.var rfl)

private theorem step_pointAddBlock {yst stend : EvmState} {out left right : U256}
    {Vend : VEnv Challenge.EvmProof.modexpExec.toDialect} {o : Outcome}
    (hbody : ExecStmts Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddInitialEnv out left right) yst pointAddBody Vend stend o) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect sourceFuns
      (pointAddInitialEnv out left right) yst (.block pointAddBody)
      (restore (pointAddInitialEnv out left right) Vend) stend o := by
  apply Step.block
  rw [hoist_pointAddBody]
  exact hbody

theorem step_scalarMulDouble {yst stend : EvmState}
    (bit scalar point out : U256)
    {Vend : VEnv Challenge.EvmProof.modexpExec.toDialect} {o : Outcome}
    (hbody : ExecStmts Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddInitialEnv out out out) yst pointAddBody Vend stend o)
    (ho : o = .normal ∨ o = .leave) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: scalarMulBodyFuns)
      (scalarMulLoopEnv bit scalar point out) yst scalarMulDoubleStmt
      (scalarMulLoopEnv bit scalar point out) stend .normal := by
  rw [scalarMulDoubleStmt_eq]
  apply Step.exprStmt
  have hcall := Step.callOk
    (step_doubleArgs yst bit scalar point out)
    (show lookupFun ([] :: [] :: scalarMulBodyFuns) "\x0016" =
      some (pointAddDecl, sourceFuns) by rfl)
    rfl (step_pointAddBlock hbody) ho
  simpa [pointAddDecl] using hcall

private theorem step_scalarMulAddCondition (funs) (yst : EvmState)
    (bit scalar point out : U256) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect funs
      (scalarMulLoopEnv bit scalar point out) yst
      (.builtin .and [.var "\x00142", .var "\x00145"])
      (.vals [scalar &&& bit] yst) :=
  Step.builtinOk
    (Step.argsCons (Step.argsCons Step.argsNil (Step.var rfl)) (Step.var rfl)) rfl

theorem step_scalarMulAddSkip (yst : EvmState) (bit scalar point out : U256)
    (hzero : scalar &&& bit = 0) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: scalarMulBodyFuns)
      (scalarMulLoopEnv bit scalar point out) yst scalarMulAddStmt
      (scalarMulLoopEnv bit scalar point out) yst .normal := by
  rw [scalarMulAddStmt_eq]
  exact Step.ifFalse
    (step_scalarMulAddCondition _ yst bit scalar point out) hzero

theorem step_scalarMulAddTaken {yst stend : EvmState}
    (bit scalar point out : U256)
    {Vend : VEnv Challenge.EvmProof.modexpExec.toDialect} {o : Outcome}
    (hbit : scalar &&& bit ≠ 0)
    (hbody : ExecStmts Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddInitialEnv out out point) yst pointAddBody Vend stend o)
    (ho : o = .normal ∨ o = .leave) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: scalarMulBodyFuns)
      (scalarMulLoopEnv bit scalar point out) yst scalarMulAddStmt
      (scalarMulLoopEnv bit scalar point out) stend .normal := by
  rw [scalarMulAddStmt_eq]
  apply Step.ifTrue
    (step_scalarMulAddCondition _ yst bit scalar point out) hbit
  have hinner : ExecStmts Challenge.EvmProof.modexpExec.toDialect
    ([] :: [] :: [] :: scalarMulBodyFuns)
    (scalarMulLoopEnv bit scalar point out) yst
    [.exprStmt (.call "\x0016"
      [.var "\x00144", .var "\x00144", .var "\x00143"])]
    (scalarMulLoopEnv bit scalar point out) stend .normal := by
    apply Step.seqCons
    · apply Step.exprStmt
      have hcall := Step.callOk
        (step_addArgs yst bit scalar point out)
        (show lookupFun ([] :: [] :: [] :: scalarMulBodyFuns) "\x0016" =
          some (pointAddDecl, sourceFuns) by rfl)
        rfl (step_pointAddBlock hbody) ho
      simpa [pointAddDecl] using hcall
    · exact Step.seqNil
  have hblock : ExecStmt Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: scalarMulBodyFuns)
      (scalarMulLoopEnv bit scalar point out) yst
      (.block [.exprStmt (.call "\x0016"
        [.var "\x00144", .var "\x00144", .var "\x00143"])])
      (restore (scalarMulLoopEnv bit scalar point out)
        (scalarMulLoopEnv bit scalar point out)) stend .normal :=
    Step.block hinner
  simpa [restore, scalarMulLoopEnv, scalarMulInitialEnv] using hblock

theorem step_scalarMulLoopBodySkip {yst stend : EvmState}
    (bit scalar point out : U256)
    {Vend : VEnv Challenge.EvmProof.modexpExec.toDialect} {o : Outcome}
    (hzero : scalar &&& bit = 0)
    (hdouble : ExecStmts Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddInitialEnv out out out) yst pointAddBody Vend stend o)
    (ho : o = .normal ∨ o = .leave) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect
      ([] :: scalarMulBodyFuns) (scalarMulLoopEnv bit scalar point out) yst
      (.block scalarMulLoopBody) (scalarMulLoopEnv bit scalar point out)
      stend .normal := by
  have hinner : ExecStmts Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: scalarMulBodyFuns)
      (scalarMulLoopEnv bit scalar point out) yst scalarMulLoopBody
      (scalarMulLoopEnv bit scalar point out) stend .normal := by
    rw [scalarMulLoopBody_eq]
    exact Step.seqCons (step_scalarMulDouble bit scalar point out hdouble ho)
      (Step.seqCons (step_scalarMulAddSkip stend bit scalar point out hzero)
        Step.seqNil)
  have hblock : ExecStmt Challenge.EvmProof.modexpExec.toDialect
      ([] :: scalarMulBodyFuns)
      (scalarMulLoopEnv bit scalar point out) yst
      (.block scalarMulLoopBody)
      (restore (scalarMulLoopEnv bit scalar point out)
        (scalarMulLoopEnv bit scalar point out)) stend .normal :=
    Step.block hinner
  simpa [restore, scalarMulLoopEnv, scalarMulInitialEnv] using hblock

theorem step_scalarMulLoopBodyTaken {yst stdouble stend : EvmState}
    (bit scalar point out : U256)
    {Vdouble Vend : VEnv Challenge.EvmProof.modexpExec.toDialect}
    {odouble oadd : Outcome}
    (hbit : scalar &&& bit ≠ 0)
    (hdouble : ExecStmts Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddInitialEnv out out out) yst pointAddBody Vdouble stdouble odouble)
    (hodouble : odouble = .normal ∨ odouble = .leave)
    (hadd : ExecStmts Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddInitialEnv out out point) stdouble pointAddBody Vend stend oadd)
    (hoadd : oadd = .normal ∨ oadd = .leave) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect
      ([] :: scalarMulBodyFuns) (scalarMulLoopEnv bit scalar point out) yst
      (.block scalarMulLoopBody) (scalarMulLoopEnv bit scalar point out)
      stend .normal := by
  have hinner : ExecStmts Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: scalarMulBodyFuns)
      (scalarMulLoopEnv bit scalar point out) yst scalarMulLoopBody
      (scalarMulLoopEnv bit scalar point out) stend .normal := by
    rw [scalarMulLoopBody_eq]
    exact Step.seqCons
      (step_scalarMulDouble bit scalar point out hdouble hodouble)
      (Step.seqCons
        (step_scalarMulAddTaken bit scalar point out hbit hadd hoadd) Step.seqNil)
  have hblock : ExecStmt Challenge.EvmProof.modexpExec.toDialect
      ([] :: scalarMulBodyFuns)
      (scalarMulLoopEnv bit scalar point out) yst
      (.block scalarMulLoopBody)
      (restore (scalarMulLoopEnv bit scalar point out)
        (scalarMulLoopEnv bit scalar point out)) stend .normal :=
    Step.block hinner
  simpa [restore, scalarMulLoopEnv, scalarMulInitialEnv] using hblock

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
