import Challenge.Bls12381G2Msm.Reference.Proofs.SourcePointAddPostArithmetic
import Challenge.Bls12381G2Msm.Reference.Proofs.SourceMsmPointCalls

set_option warningAsError true

/-! Complete common finite postlude of G2MSM `pointAdd`. -/

namespace Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def pointAddPostStoreArgsState (yst : EvmState) : EvmState :=
  touchMemory yst 1920 32

def pointAddPostOut (yst : EvmState) : U256 := loadWord yst.memory 1920

def pointAddPostStoreState (yst : EvmState) : EvmState :=
  msmStorePointState (pointAddPostStoreArgsState yst)
    (pointAddPostOut yst) 2688 2944

private theorem pointAddStmt13_eq : pointAddStmt13 =
    .exprStmt (.call "\x0025"
      [.builtin .mload [.lit (.number 1920)],
        .lit (.number 2688), .lit (.number 2944)]) := by rfl

theorem step_pointAddPostStore (yst : EvmState) (out left right : U256) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddInitialEnv out left right) yst pointAddStmt13
      (pointAddInitialEnv out left right) (pointAddPostStoreState yst)
      .normal := by
  rw [pointAddStmt13_eq]
  have hy : EvalExpr Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddInitialEnv out left right) yst (.lit (.number 2944))
      (.vals [2944] yst) := Step.lit
  have hx : EvalExpr Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddInitialEnv out left right) yst (.lit (.number 2688))
      (.vals [2688] yst) := Step.lit
  have hload : EvalExpr Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddInitialEnv out left right) yst
      (.builtin .mload [.lit (.number 1920)])
      (.vals [pointAddPostOut yst] (pointAddPostStoreArgsState yst)) :=
    Step.builtinOk (Step.argsCons Step.argsNil Step.lit) rfl
  have hargs : EvalArgs Challenge.EvmProof.modexpExec.toDialect
      pointAddBodyFuns (pointAddInitialEnv out left right) yst
      [.builtin .mload [.lit (.number 1920)],
        .lit (.number 2688), .lit (.number 2944)]
      (.vals [pointAddPostOut yst, 2688, 2944]
        (pointAddPostStoreArgsState yst)) :=
    Step.argsCons (Step.argsCons (Step.argsCons Step.argsNil hy) hx) hload
  exact Step.exprStmt (step_msmStorePoint_of_args _ _ _ hargs (by rfl))

def pointAddPostState1 (yst : EvmState) : EvmState :=
  pointAddPostSquareState yst

def pointAddPostState2 (yst : EvmState) : EvmState :=
  pointAddPostSubLeftState (pointAddPostState1 yst)

def pointAddPostState3 (yst : EvmState) : EvmState :=
  pointAddPostSubRightState (pointAddPostState2 yst)

def pointAddPostState4 (yst : EvmState) : EvmState :=
  pointAddPostDeltaXState (pointAddPostState3 yst)

def pointAddPostState5 (yst : EvmState) : EvmState :=
  pointAddPostMulYState (pointAddPostState4 yst)

def pointAddPostState6 (yst : EvmState) : EvmState :=
  pointAddPostSubYState (pointAddPostState5 yst)

def pointAddPostFinalState (yst : EvmState) : EvmState :=
  pointAddPostStoreState (pointAddPostState6 yst)

theorem step_pointAddPost (yst : EvmState) (out left right : U256) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddInitialEnv out left right) yst pointAddPostBody
      (pointAddInitialEnv out left right) (pointAddPostFinalState yst)
      .normal := by
  exact Step.seqCons (step_pointAddPostSquare yst out left right)
    (Step.seqCons
      (step_pointAddPostSubLeft (pointAddPostState1 yst) out left right)
      (Step.seqCons
        (step_pointAddPostSubRight (pointAddPostState2 yst) out left right)
        (Step.seqCons
          (step_pointAddPostDeltaX (pointAddPostState3 yst) out left right)
          (Step.seqCons
            (step_pointAddPostMulY (pointAddPostState4 yst) out left right)
            (Step.seqCons
              (step_pointAddPostSubY (pointAddPostState5 yst) out left right)
              (Step.seqCons
                (step_pointAddPostStore (pointAddPostState6 yst)
                  out left right)
                Step.seqNil))))))

end Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics
