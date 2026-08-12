import Challenge.Bls12381G1Msm.Reference.Proofs.SourceOnCurveEq

set_option warningAsError true

/-! Relational composition of the frozen G1MSM `onCurve` body. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

theorem step_onCurveBody (xhi xlo yhi ylo : U256) (yst : EvmState) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect onCurveBodyFuns
      (onCurveInitialEnv xhi xlo yhi ylo) yst onCurveBody
      (onCurveReturnEnv xhi xlo yhi ylo yst)
      (onCurveX3State xhi xlo yhi ylo yst) .normal := by
  rw [onCurveBody_eq]
  exact Step.seqCons (step_onCurveY2 xhi xlo yhi ylo yst)
    (Step.seqCons (step_onCurveX2 xhi xlo yhi ylo yst)
      (Step.seqCons (step_onCurveX3 xhi xlo yhi ylo yst)
        (Step.seqCons (step_onCurveAdd4 xhi xlo yhi ylo yst)
          (Step.seqCons (step_onCurveEq xhi xlo yhi ylo yst) Step.seqNil))))

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
