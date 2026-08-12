import Challenge.Bls12381G2Msm.Reference.Proofs.SourcePointAddExceptionalRun

set_option warningAsError true

/-! Relational call transport for the fully staged G2MSM `pointAdd`. -/

namespace Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

theorem step_pointAdd_of_args {funs V st argState args stend outcome}
    (out left right : U256)
    (hargs : EvalArgs Challenge.EvmProof.modexpExec.toDialect funs V st args
      (.vals [out, left, right] argState))
    (hlookup : lookupFun funs "\x0029" =
      some (pointAddDecl, pointAddFuns))
    (hbody : ExecStmt Challenge.EvmProof.modexpExec.toDialect pointAddFuns
      (pointAddInitialEnv out left right) argState (.block pointAddBody)
      (pointAddInitialEnv out left right) stend outcome)
    (houtcome : outcome = .normal ∨ outcome = .leave) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect funs V st
      (.call "\x0029" args) (.vals [] stend) := by
  have hcall := Step.callOk hargs hlookup rfl hbody houtcome
  simpa [pointAddDecl, pointAddInitialEnv] using hcall

end Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics
