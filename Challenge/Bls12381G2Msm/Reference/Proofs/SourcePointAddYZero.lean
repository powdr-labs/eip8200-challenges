import Challenge.Bls12381G2Msm.Reference.Proofs.SourcePointAddDoubleYSum
import Challenge.Bls12381G2Msm.Reference.Proofs.SourceMsmPointCalls

set_option warningAsError true

/-! Exceptional equal-point branch that stores infinity and leaves `pointAdd`. -/

namespace Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def pointAddYZeroArgsState (yst : EvmState) : EvmState :=
  touchMemory (pointAddAfterDoubleYZero yst) 1920 32

def pointAddYZeroOut (yst : EvmState) : U256 :=
  loadWord (pointAddAfterDoubleYZero yst).memory 1920

def pointAddYZeroFinalState (yst : EvmState) : EvmState :=
  msmStoreInfinityState (pointAddYZeroArgsState yst) (pointAddYZeroOut yst)

private theorem step_pointAddYZeroStore (yst : EvmState)
    (out left right : U256) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) (pointAddInitialEnv out left right)
      (pointAddAfterDoubleYZero yst)
      (.call "\x0026" [.builtin .mload [.lit (.number 1920)]])
      (.vals [] (pointAddYZeroFinalState yst)) := by
  have hoffset : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) (pointAddInitialEnv out left right)
      (pointAddAfterDoubleYZero yst) (.lit (.number 1920))
      (.vals [1920] (pointAddAfterDoubleYZero yst)) := Step.lit
  have hload : EvalExpr Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) (pointAddInitialEnv out left right)
      (pointAddAfterDoubleYZero yst)
      (.builtin .mload [.lit (.number 1920)])
      (.vals [pointAddYZeroOut yst] (pointAddYZeroArgsState yst)) :=
    Step.builtinOk (Step.argsCons Step.argsNil hoffset) rfl
  have hargs : EvalArgs Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) (pointAddInitialEnv out left right)
      (pointAddAfterDoubleYZero yst)
      [.builtin .mload [.lit (.number 1920)]]
      (.vals [pointAddYZeroOut yst] (pointAddYZeroArgsState yst)) :=
    Step.argsCons Step.argsNil hload
  exact step_msmStoreInfinity_of_args _ hargs (by rfl)

private theorem step_pointAddYZeroBody (yst : EvmState)
    (out left right : U256) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect
      ([] :: pointAddBodyFuns) (pointAddInitialEnv out left right)
      (pointAddAfterDoubleYZero yst) (.block pointAddEqualYZeroBody)
      (pointAddInitialEnv out left right)
      (pointAddYZeroFinalState yst) .leave := by
  rw [pointAddEqualYZeroBody_eq]
  have hseq : ExecStmts Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) (pointAddInitialEnv out left right)
      (pointAddAfterDoubleYZero yst)
      [.exprStmt (.call "\x0026"
        [.builtin .mload [.lit (.number 1920)]]), .leave]
      (pointAddInitialEnv out left right)
      (pointAddYZeroFinalState yst) .leave :=
    Step.seqCons (Step.exprStmt (step_pointAddYZeroStore yst out left right))
      (Step.seqStop Step.leave (by decide))
  have hblock := Step.block (D := Challenge.EvmProof.modexpExec.toDialect)
    (body := [.exprStmt (.call "\x0026"
      [.builtin .mload [.lit (.number 1920)]]), .leave]) hseq
  simpa [restore, pointAddInitialEnv] using hblock

theorem step_pointAddDoubleYZero (yst : EvmState)
    (out left right : U256) (hy : pointAddDoubleYZero yst ≠ 0) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect
      ([] :: pointAddBodyFuns) (pointAddInitialEnv out left right) yst
      pointAddEqualStmt1 (pointAddInitialEnv out left right)
      (pointAddYZeroFinalState yst) .leave := by
  rw [pointAddEqualYZeroStmt_eq]
  exact Step.ifTrue (step_pointAddDoubleYZeroCondition yst out left right) hy
    (step_pointAddYZeroBody yst out left right)

end Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics
