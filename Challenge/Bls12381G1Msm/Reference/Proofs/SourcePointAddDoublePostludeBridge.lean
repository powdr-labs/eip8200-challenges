import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddDoubleYSubEnvLookup
import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddDoublePostludeFull

set_option warningAsError true

/-! Single bridge from the final field subtraction to the output-store postlude. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def pointAddDoublePostContext (yst : EvmState)
    (out left right : U256) : PointAddDoublePostContext where
  env := pointAddDoubleYSubConcreteEnv yst out left right
  state := pointAddDoubleYSubConcreteState yst out left right
  xHi := (pointAddDoubleXSubResult yst out left right).1
  xLo := (pointAddDoubleXSubResult yst out left right).2
  yHi := (pointAddDoubleYSubResult
    (pointAddDoubleYSubContext yst out left right)).1
  yLo := (pointAddDoubleYSubResult
    (pointAddDoubleYSubContext yst out left right)).2
  tempHi := (pointAddDoubleDeltaResult
    (pointAddDoubleDeltaContext yst out left right)).1
  tempLo := (pointAddDoubleDeltaResult
    (pointAddDoubleDeltaContext yst out left right)).2
  env_xHi := pointAddDoubleYSubConcreteEnv_xHi yst out left right
  env_xLo := pointAddDoubleYSubConcreteEnv_xLo yst out left right
  env_yHi := pointAddDoubleYSubConcreteEnv_yHi yst out left right
  env_yLo := pointAddDoubleYSubConcreteEnv_yLo yst out left right
  env_tempHi := pointAddDoubleYSubConcreteEnv_tempHi yst out left right
  env_tempLo := pointAddDoubleYSubConcreteEnv_tempLo yst out left right

def pointAddDoubleFinalEnv (yst : EvmState)
    (out left right : U256) : VEnv Challenge.EvmProof.modexpExec.toDialect :=
  pointAddDoublePostEnv (pointAddDoublePostContext yst out left right)

def pointAddDoubleFinalState (yst : EvmState)
    (out left right : U256) : EvmState :=
  pointAddDoublePostState (pointAddDoublePostContext yst out left right)

theorem step_pointAddDoublePostlude (yst : EvmState)
    (out left right : U256) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddDoublePostContext yst out left right).env
      (pointAddDoublePostContext yst out left right).state
      pointAddDoublePostlude
      (pointAddDoublePostEnv (pointAddDoublePostContext yst out left right))
      (pointAddDoublePostState (pointAddDoublePostContext yst out left right))
      .normal :=
  step_pointAddDoublePostludeGeneric
    (pointAddDoublePostContext yst out left right)

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
