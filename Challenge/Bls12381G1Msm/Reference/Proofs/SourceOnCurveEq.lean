import Challenge.Bls12381G1Msm.Reference.Proofs.SourceOnCurveAdd4
import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePredicates

set_option warningAsError true

/-! Relational execution of the final equality in G1MSM `onCurve`. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

private theorem onCurveStmt4_shape : onCurveStmt4 =
    .assign ["\x0090"]
      (.builtin .and
        [.builtin .eq [.var "\x0091", .var "\x0095"],
         .builtin .eq [.var "\x0092", .var "\x0096"]]) := by
  rfl

def onCurveLhs (yhi ylo : U256) (yst : EvmState) : U256 × U256 :=
  fpMulResult yst yhi ylo yhi ylo

def onCurveResult (xhi xlo yhi ylo : U256) (yst : EvmState) : U256 :=
  let lhs := onCurveLhs yhi ylo yst
  let rhs := onCurveRhs xhi xlo yhi ylo yst
  fpEqValue lhs.1 lhs.2 rhs.1 rhs.2

def onCurveReturnEnv (xhi xlo yhi ylo : U256) (yst : EvmState) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  VEnv.setMany (onCurveAdd4Env xhi xlo yhi ylo yst) ["\x0090"]
    [onCurveResult xhi xlo yhi ylo yst]

theorem step_onCurveEq (xhi xlo yhi ylo : U256) (yst : EvmState) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect onCurveBodyFuns
      (onCurveAdd4Env xhi xlo yhi ylo yst)
      (onCurveX3State xhi xlo yhi ylo yst) onCurveStmt4
      (onCurveReturnEnv xhi xlo yhi ylo yst)
      (onCurveX3State xhi xlo yhi ylo yst) .normal := by
  let lhs := onCurveLhs yhi ylo yst
  let rhs := onCurveRhs xhi xlo yhi ylo yst
  have heqHi : EvalExpr Challenge.EvmProof.modexpExec.toDialect onCurveBodyFuns
      (onCurveAdd4Env xhi xlo yhi ylo yst)
      (onCurveX3State xhi xlo yhi ylo yst)
      (.builtin .eq [.var "\x0091", .var "\x0095"])
      (.vals [b2w (lhs.1 = rhs.1)]
        (onCurveX3State xhi xlo yhi ylo yst)) :=
    Step.builtinOk
      (Step.argsCons (Step.argsCons Step.argsNil (Step.var rfl))
        (Step.var rfl)) rfl
  have heqLo : EvalExpr Challenge.EvmProof.modexpExec.toDialect onCurveBodyFuns
      (onCurveAdd4Env xhi xlo yhi ylo yst)
      (onCurveX3State xhi xlo yhi ylo yst)
      (.builtin .eq [.var "\x0092", .var "\x0096"])
      (.vals [b2w (lhs.2 = rhs.2)]
        (onCurveX3State xhi xlo yhi ylo yst)) :=
    Step.builtinOk
      (Step.argsCons (Step.argsCons Step.argsNil (Step.var rfl))
        (Step.var rfl)) rfl
  have hand : EvalExpr Challenge.EvmProof.modexpExec.toDialect onCurveBodyFuns
      (onCurveAdd4Env xhi xlo yhi ylo yst)
      (onCurveX3State xhi xlo yhi ylo yst)
      (.builtin .and
        [.builtin .eq [.var "\x0091", .var "\x0095"],
         .builtin .eq [.var "\x0092", .var "\x0096"]])
      (.vals [fpEqValue lhs.1 lhs.2 rhs.1 rhs.2]
        (onCurveX3State xhi xlo yhi ylo yst)) :=
    Step.builtinOk
      (Step.argsCons (Step.argsCons Step.argsNil heqLo) heqHi) rfl
  rw [onCurveStmt4_shape, onCurveReturnEnv]
  exact Step.assignVal hand rfl

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
