import Challenge.Bls12381G2Msm.Reference.Proofs.SourceScalarMulPost
import Challenge.Bls12381G2Msm.Reference.Proofs.SourcePointAddCalls

set_option warningAsError true

/-! One doubled-and-optional-add body of the naive G2 scalar loop. -/

namespace Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def scalarMulAddValue (scalar bit : U256) : U256 := scalar &&& bit

private theorem scalarMulDoubleStmt_eq : scalarMulDoubleStmt =
    .exprStmt (.call "\x0029"
      [.var "\x00150", .var "\x00150", .var "\x00150"]) := by rfl

private theorem scalarMulAddStmt_eq : scalarMulAddStmt =
    .cond (.builtin .and [.var "\x00148", .var "\x00151"])
      [.exprStmt (.call "\x0029"
        [.var "\x00150", .var "\x00150", .var "\x00149"])] := by rfl

private theorem step_scalarMulOutArgs {funs} (yst : EvmState)
    (bit scalar point out : U256) :
    EvalArgs Challenge.EvmProof.modexpExec.toDialect funs
      (scalarMulLoopEnv bit scalar point out) yst
      [.var "\x00150", .var "\x00150", .var "\x00150"]
      (.vals [out, out, out] yst) :=
  Step.argsCons
    (Step.argsCons (Step.argsCons Step.argsNil (Step.var rfl)) (Step.var rfl))
    (Step.var rfl)

theorem step_scalarMulDouble {yst stend : EvmState}
    (bit scalar point out : U256) {outcome : Outcome}
    (hbody : ExecStmt Challenge.EvmProof.modexpExec.toDialect pointAddFuns
      (pointAddInitialEnv out out out) yst (.block pointAddBody)
      (pointAddInitialEnv out out out) stend outcome)
    (houtcome : outcome = .normal ∨ outcome = .leave) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: scalarMulBodyFuns)
      (scalarMulLoopEnv bit scalar point out) yst
      scalarMulDoubleStmt (scalarMulLoopEnv bit scalar point out)
      stend .normal := by
  rw [scalarMulDoubleStmt_eq]
  exact Step.exprStmt (step_pointAdd_of_args out out out
    (step_scalarMulOutArgs yst bit scalar point out) (by rfl)
    hbody houtcome)

private theorem step_scalarMulAddCondition {funs} (yst : EvmState)
    (bit scalar point out : U256) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect funs
      (scalarMulLoopEnv bit scalar point out) yst
      (.builtin .and [.var "\x00148", .var "\x00151"])
      (.vals [scalarMulAddValue scalar bit] yst) := by
  have hbit : EvalExpr Challenge.EvmProof.modexpExec.toDialect funs
      (scalarMulLoopEnv bit scalar point out) yst (.var "\x00151")
      (.vals [bit] yst) := Step.var rfl
  have hscalar : EvalExpr Challenge.EvmProof.modexpExec.toDialect funs
      (scalarMulLoopEnv bit scalar point out) yst (.var "\x00148")
      (.vals [scalar] yst) := Step.var rfl
  exact Step.builtinOk
    (Step.argsCons (Step.argsCons Step.argsNil hbit) hscalar) rfl

theorem step_scalarMulAddSkip (yst : EvmState)
    (bit scalar point out : U256)
    (hzero : scalarMulAddValue scalar bit = 0) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: scalarMulBodyFuns)
      (scalarMulLoopEnv bit scalar point out) yst
      scalarMulAddStmt (scalarMulLoopEnv bit scalar point out) yst .normal := by
  rw [scalarMulAddStmt_eq]
  exact Step.ifFalse
    (step_scalarMulAddCondition yst bit scalar point out) hzero

private theorem step_scalarMulPointArgs {funs} (yst : EvmState)
    (bit scalar point out : U256) :
    EvalArgs Challenge.EvmProof.modexpExec.toDialect funs
      (scalarMulLoopEnv bit scalar point out) yst
      [.var "\x00150", .var "\x00150", .var "\x00149"]
      (.vals [out, out, point] yst) :=
  Step.argsCons
    (Step.argsCons (Step.argsCons Step.argsNil (Step.var rfl)) (Step.var rfl))
    (Step.var rfl)

theorem step_scalarMulAddTaken {yst stend : EvmState}
    (bit scalar point out : U256) {outcome : Outcome}
    (hnonzero : scalarMulAddValue scalar bit ≠ 0)
    (hbody : ExecStmt Challenge.EvmProof.modexpExec.toDialect pointAddFuns
      (pointAddInitialEnv out out point) yst (.block pointAddBody)
      (pointAddInitialEnv out out point) stend outcome)
    (houtcome : outcome = .normal ∨ outcome = .leave) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: scalarMulBodyFuns)
      (scalarMulLoopEnv bit scalar point out) yst
      scalarMulAddStmt (scalarMulLoopEnv bit scalar point out)
      stend .normal := by
  rw [scalarMulAddStmt_eq]
  have hcall := step_pointAdd_of_args out out point
    (step_scalarMulPointArgs
      (funs := [] :: [] :: [] :: scalarMulBodyFuns)
      yst bit scalar point out)
    (by rfl) hbody houtcome
  have hseq : ExecStmts Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: [] :: scalarMulBodyFuns)
      (scalarMulLoopEnv bit scalar point out) yst
      [.exprStmt (.call "\x0029"
        [.var "\x00150", .var "\x00150", .var "\x00149"])]
      (scalarMulLoopEnv bit scalar point out) stend .normal :=
    Step.seqCons (Step.exprStmt hcall) Step.seqNil
  have hblock := Step.block (D := Challenge.EvmProof.modexpExec.toDialect)
    (body := [.exprStmt (.call "\x0029"
      [.var "\x00150", .var "\x00150", .var "\x00149"])]) hseq
  exact Step.ifTrue (step_scalarMulAddCondition yst bit scalar point out)
    hnonzero (by simpa [restore, scalarMulLoopEnv, scalarMulInitialEnv] using hblock)

theorem step_scalarMulLoopBodySkip {yst stmid : EvmState}
    (bit scalar point out : U256) {doubleOutcome : Outcome}
    (hdouble : ExecStmt Challenge.EvmProof.modexpExec.toDialect pointAddFuns
      (pointAddInitialEnv out out out) yst (.block pointAddBody)
      (pointAddInitialEnv out out out) stmid doubleOutcome)
    (hdoubleOutcome : doubleOutcome = .normal ∨ doubleOutcome = .leave)
    (hzero : scalarMulAddValue scalar bit = 0) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect
      ([] :: scalarMulBodyFuns)
      (scalarMulLoopEnv bit scalar point out) yst (.block scalarMulLoopBody)
      (scalarMulLoopEnv bit scalar point out) stmid .normal := by
  have hseq : ExecStmts Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: scalarMulBodyFuns)
      (scalarMulLoopEnv bit scalar point out) yst
      scalarMulLoopBody (scalarMulLoopEnv bit scalar point out) stmid .normal := by
    rw [scalarMulLoopBody_eq]
    exact Step.seqCons
      (step_scalarMulDouble bit scalar point out hdouble hdoubleOutcome)
      (Step.seqCons (step_scalarMulAddSkip stmid bit scalar point out hzero)
        Step.seqNil)
  have hblock := Step.block (D := Challenge.EvmProof.modexpExec.toDialect)
    (body := scalarMulLoopBody) hseq
  simpa [restore, scalarMulLoopEnv, scalarMulInitialEnv] using hblock

theorem step_scalarMulLoopBodyTaken {yst stmid stend : EvmState}
    (bit scalar point out : U256)
    {doubleOutcome addOutcome : Outcome}
    (hdouble : ExecStmt Challenge.EvmProof.modexpExec.toDialect pointAddFuns
      (pointAddInitialEnv out out out) yst (.block pointAddBody)
      (pointAddInitialEnv out out out) stmid doubleOutcome)
    (hdoubleOutcome : doubleOutcome = .normal ∨ doubleOutcome = .leave)
    (hnonzero : scalarMulAddValue scalar bit ≠ 0)
    (hadd : ExecStmt Challenge.EvmProof.modexpExec.toDialect pointAddFuns
      (pointAddInitialEnv out out point) stmid (.block pointAddBody)
      (pointAddInitialEnv out out point) stend addOutcome)
    (haddOutcome : addOutcome = .normal ∨ addOutcome = .leave) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect
      ([] :: scalarMulBodyFuns)
      (scalarMulLoopEnv bit scalar point out) yst (.block scalarMulLoopBody)
      (scalarMulLoopEnv bit scalar point out) stend .normal := by
  have hseq : ExecStmts Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: scalarMulBodyFuns)
      (scalarMulLoopEnv bit scalar point out) yst
      scalarMulLoopBody (scalarMulLoopEnv bit scalar point out) stend .normal := by
    rw [scalarMulLoopBody_eq]
    exact Step.seqCons
      (step_scalarMulDouble bit scalar point out hdouble hdoubleOutcome)
      (Step.seqCons (step_scalarMulAddTaken (yst := stmid) (stend := stend)
        bit scalar point out hnonzero hadd haddOutcome) Step.seqNil)
  have hblock := Step.block (D := Challenge.EvmProof.modexpExec.toDialect)
    (body := scalarMulLoopBody) hseq
  simpa [restore, scalarMulLoopEnv, scalarMulInitialEnv] using hblock

end Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics
