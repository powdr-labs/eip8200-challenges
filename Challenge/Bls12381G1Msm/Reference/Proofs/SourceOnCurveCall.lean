import Challenge.Bls12381G1Msm.Reference.Proofs.SourceOnCurveBody

set_option warningAsError true

/-! Relational call semantics of the frozen G1MSM `onCurve` helper. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def onCurveFinalEnv (xhi xlo yhi ylo : U256) (yst : EvmState) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  restore (onCurveInitialEnv xhi xlo yhi ylo)
    (onCurveReturnEnv xhi xlo yhi ylo yst)

theorem onCurveFinalEnv_result (xhi xlo yhi ylo : U256) (yst : EvmState) :
    (VEnv.get (onCurveFinalEnv xhi xlo yhi ylo yst) "\x0090").getD 0 =
      onCurveResult xhi xlo yhi ylo yst := by
  rfl

theorem step_onCurveBlock (xhi xlo yhi ylo : U256) (yst : EvmState) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect sourceFuns
      (onCurveInitialEnv xhi xlo yhi ylo) yst (.block onCurveBody)
      (onCurveFinalEnv xhi xlo yhi ylo yst)
      (onCurveX3State xhi xlo yhi ylo yst) .normal := by
  exact Step.block (step_onCurveBody xhi xlo yhi ylo yst)

theorem step_onCurve_of_args {funs V yst args} (xhi xlo yhi ylo : U256)
    (hargs : EvalArgs Challenge.EvmProof.modexpExec.toDialect funs V yst args
      (.vals [xhi, xlo, yhi, ylo] yst))
    (hlookup : lookupFun funs "\x0011" = some (onCurveDecl, sourceFuns)) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect funs V yst
      (.call "\x0011" args)
      (.vals [onCurveResult xhi xlo yhi ylo yst]
        (onCurveX3State xhi xlo yhi ylo yst)) := by
  have hcall := Step.callOk hargs hlookup rfl
    (step_onCurveBlock xhi xlo yhi ylo yst) (Or.inl rfl)
  change EvalExpr Challenge.EvmProof.modexpExec.toDialect funs V yst
    (.call "\x0011" args)
    (.vals [(VEnv.get (onCurveFinalEnv xhi xlo yhi ylo yst)
      "\x0090").getD 0] (onCurveX3State xhi xlo yhi ylo yst)) at hcall
  rw [onCurveFinalEnv_result] at hcall
  exact hcall

theorem step_onCurve (xhi xlo yhi ylo : U256) (yst : EvmState) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect sourceFuns
      [("xhi", xhi), ("xlo", xlo), ("yhi", yhi), ("ylo", ylo)] yst
      (.call "\x0011" [.var "xhi", .var "xlo", .var "yhi", .var "ylo"])
      (.vals [onCurveResult xhi xlo yhi ylo yst]
        (onCurveX3State xhi xlo yhi ylo yst)) := by
  have hargs : EvalArgs Challenge.EvmProof.modexpExec.toDialect sourceFuns
      [("xhi", xhi), ("xlo", xlo), ("yhi", yhi), ("ylo", ylo)] yst
      [.var "xhi", .var "xlo", .var "yhi", .var "ylo"]
      (.vals [xhi, xlo, yhi, ylo] yst) :=
    Step.argsCons (Step.argsCons (Step.argsCons (Step.argsCons Step.argsNil
      (Step.var rfl)) (Step.var rfl)) (Step.var rfl)) (Step.var rfl)
  exact step_onCurve_of_args xhi xlo yhi ylo hargs lookup_onCurve

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
