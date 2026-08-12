import Challenge.Bls12381G1Msm.Reference.Proofs.SourceOnCurveX3
import Challenge.Bls12381G1Msm.Reference.Proofs.SourceFpAddCall

set_option warningAsError true

/-! Relational execution of the `x³ + 4` statement in G1MSM `onCurve`. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

private theorem onCurveStmt3_shape : onCurveStmt3 =
    .assign ["\x0095", "\x0096"]
      (.call "\x004"
        [.var "\x0095", .var "\x0096", .lit (.number 0),
          .lit (.number 4)]) := by
  rfl

def onCurveCube (xhi xlo yhi ylo : U256) (yst : EvmState) : U256 × U256 :=
  let x2 := fpMulResult (onCurveY2State yhi ylo yst) xhi xlo xhi xlo
  fpMulResult (onCurveX2State xhi xlo yhi ylo yst) x2.1 x2.2 xhi xlo

def onCurveRhs (xhi xlo yhi ylo : U256) (yst : EvmState) : U256 × U256 :=
  let cube := onCurveCube xhi xlo yhi ylo yst
  fpAddResult cube.1 cube.2 0 4

def onCurveAdd4Env (xhi xlo yhi ylo : U256) (yst : EvmState) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  VEnv.setMany (onCurveX3Env xhi xlo yhi ylo yst)
    ["\x0095", "\x0096"]
    [(onCurveRhs xhi xlo yhi ylo yst).1,
     (onCurveRhs xhi xlo yhi ylo yst).2]

theorem step_onCurveAdd4 (xhi xlo yhi ylo : U256) (yst : EvmState) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect onCurveBodyFuns
      (onCurveX3Env xhi xlo yhi ylo yst)
      (onCurveX3State xhi xlo yhi ylo yst) onCurveStmt3
      (onCurveAdd4Env xhi xlo yhi ylo yst)
      (onCurveX3State xhi xlo yhi ylo yst) .normal := by
  let cube := onCurveCube xhi xlo yhi ylo yst
  have hhi : EvalExpr Challenge.EvmProof.modexpExec.toDialect onCurveBodyFuns
      (onCurveX3Env xhi xlo yhi ylo yst)
      (onCurveX3State xhi xlo yhi ylo yst) (.var "\x0095")
      (.vals [cube.1] (onCurveX3State xhi xlo yhi ylo yst)) := Step.var rfl
  have hlo : EvalExpr Challenge.EvmProof.modexpExec.toDialect onCurveBodyFuns
      (onCurveX3Env xhi xlo yhi ylo yst)
      (onCurveX3State xhi xlo yhi ylo yst) (.var "\x0096")
      (.vals [cube.2] (onCurveX3State xhi xlo yhi ylo yst)) := Step.var rfl
  have hz : EvalExpr Challenge.EvmProof.modexpExec.toDialect onCurveBodyFuns
      (onCurveX3Env xhi xlo yhi ylo yst)
      (onCurveX3State xhi xlo yhi ylo yst) (.lit (.number 0))
      (.vals [0] (onCurveX3State xhi xlo yhi ylo yst)) := Step.lit
  have hfour : EvalExpr Challenge.EvmProof.modexpExec.toDialect onCurveBodyFuns
      (onCurveX3Env xhi xlo yhi ylo yst)
      (onCurveX3State xhi xlo yhi ylo yst) (.lit (.number 4))
      (.vals [4] (onCurveX3State xhi xlo yhi ylo yst)) := Step.lit
  have hargs : EvalArgs Challenge.EvmProof.modexpExec.toDialect onCurveBodyFuns
      (onCurveX3Env xhi xlo yhi ylo yst)
      (onCurveX3State xhi xlo yhi ylo yst)
      [.var "\x0095", .var "\x0096", .lit (.number 0), .lit (.number 4)]
      (.vals [cube.1, cube.2, 0, 4]
        (onCurveX3State xhi xlo yhi ylo yst)) :=
    Step.argsCons (Step.argsCons (Step.argsCons (Step.argsCons Step.argsNil
      hfour) hz) hlo) hhi
  have hlookup : lookupFun onCurveBodyFuns "\x004" =
      some (fpAddDecl, sourceFuns) := by
    rfl
  have hcall := step_fpAdd_of_args cube.1 cube.2 0 4 hargs hlookup
  rw [onCurveStmt3_shape]
  change ExecStmt Challenge.EvmProof.modexpExec.toDialect onCurveBodyFuns
    (onCurveX3Env xhi xlo yhi ylo yst)
    (onCurveX3State xhi xlo yhi ylo yst)
    (.assign ["\x0095", "\x0096"]
      (.call "\x004"
        [.var "\x0095", .var "\x0096", .lit (.number 0),
          .lit (.number 4)]))
    (VEnv.setMany (onCurveX3Env xhi xlo yhi ylo yst)
      ["\x0095", "\x0096"]
      [(fpAddResult cube.1 cube.2 0 4).1,
       (fpAddResult cube.1 cube.2 0 4).2])
    (onCurveX3State xhi xlo yhi ylo yst) .normal
  exact Step.assignVal hcall rfl

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
