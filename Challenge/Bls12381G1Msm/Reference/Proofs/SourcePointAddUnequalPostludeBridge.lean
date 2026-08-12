import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalYSubEnvLookup
import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalPostludeFull

set_option warningAsError true

/-! Single bridge from the final field subtraction to the output-store postlude. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def pointAddUnequalPostX (yst : EvmState)
    (out left right : U256) : U256 × U256 :=
  pointAddUnequalXSubResult yst out left right

theorem pointAddUnequalPostX_eq (yst : EvmState)
    (out left right : U256) :
    pointAddUnequalPostX yst out left right =
      pointAddUnequalXSubResult yst out left right := by
  rfl

def pointAddUnequalPostY (yst : EvmState)
    (out left right : U256) : U256 × U256 :=
  pointAddUnequalYSubResult
    (pointAddUnequalYSubContext yst out left right)

theorem pointAddUnequalPostY_eq (yst : EvmState)
    (out left right : U256) :
    pointAddUnequalPostY yst out left right =
      pointAddUnequalYSubResult
        (pointAddUnequalYSubContext yst out left right) := by
  rfl

attribute [irreducible] pointAddUnequalPostX pointAddUnequalPostY

def pointAddUnequalPostContext (yst : EvmState)
    (out left right : U256) : PointAddUnequalPostContext :=
  makePointAddUnequalPostContext
    (pointAddUnequalPostX yst out left right).1
    (pointAddUnequalPostX yst out left right).2
    (pointAddUnequalPostY yst out left right).1
    (pointAddUnequalPostY yst out left right).2
    (pointAddUnequalDeltaResult
      (pointAddUnequalDeltaContext yst out left right)).1
    (pointAddUnequalDeltaResult
      (pointAddUnequalDeltaContext yst out left right)).2
    (pointAddUnequalYSubConcreteEnv yst out left right)
    (pointAddUnequalYSubConcreteState yst out left right)
    (by
      rw [pointAddUnequalPostX_eq]
      exact pointAddUnequalYSubConcreteEnv_xHi yst out left right)
    (by
      rw [pointAddUnequalPostX_eq]
      exact pointAddUnequalYSubConcreteEnv_xLo yst out left right)
    (by
      rw [pointAddUnequalPostY_eq]
      exact pointAddUnequalYSubConcreteEnv_yHi yst out left right)
    (by
      rw [pointAddUnequalPostY_eq]
      exact pointAddUnequalYSubConcreteEnv_yLo yst out left right)
    (pointAddUnequalYSubConcreteEnv_tempHi yst out left right)
    (pointAddUnequalYSubConcreteEnv_tempLo yst out left right)

theorem pointAddUnequalPostContext_xHi (yst : EvmState)
    (out left right : U256) :
    (pointAddUnequalPostContext yst out left right).xHi =
      (pointAddUnequalPostX yst out left right).1 := by
  rw [pointAddUnequalPostContext,
    makePointAddUnequalPostContext_xHi]

theorem pointAddUnequalPostContext_xLo (yst : EvmState)
    (out left right : U256) :
    (pointAddUnequalPostContext yst out left right).xLo =
      (pointAddUnequalPostX yst out left right).2 := by
  rw [pointAddUnequalPostContext,
    makePointAddUnequalPostContext_xLo]

theorem pointAddUnequalPostContext_yHi (yst : EvmState)
    (out left right : U256) :
    (pointAddUnequalPostContext yst out left right).yHi =
      (pointAddUnequalPostY yst out left right).1 := by
  rw [pointAddUnequalPostContext,
    makePointAddUnequalPostContext_yHi]

theorem pointAddUnequalPostContext_yLo (yst : EvmState)
    (out left right : U256) :
    (pointAddUnequalPostContext yst out left right).yLo =
      (pointAddUnequalPostY yst out left right).2 := by
  rw [pointAddUnequalPostContext,
    makePointAddUnequalPostContext_yLo]

theorem pointAddUnequalPostContext_env (yst : EvmState)
    (out left right : U256) :
    (pointAddUnequalPostContext yst out left right).env =
      pointAddUnequalYSubConcreteEnv yst out left right := by
  rw [pointAddUnequalPostContext,
    makePointAddUnequalPostContext_env]

theorem pointAddUnequalPostContext_state (yst : EvmState)
    (out left right : U256) :
    (pointAddUnequalPostContext yst out left right).state =
      pointAddUnequalYSubConcreteState yst out left right := by
  rw [pointAddUnequalPostContext,
    makePointAddUnequalPostContext_state]

def pointAddUnequalFinalEnv (yst : EvmState)
    (out left right : U256) : VEnv Challenge.EvmProof.modexpExec.toDialect :=
  pointAddUnequalPostEnv (pointAddUnequalPostContext yst out left right)

def pointAddUnequalFinalState (yst : EvmState)
    (out left right : U256) : EvmState :=
  pointAddUnequalPostState (pointAddUnequalPostContext yst out left right)

theorem step_pointAddUnequalPostlude (yst : EvmState)
    (out left right : U256) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddUnequalPostContext yst out left right).env
      (pointAddUnequalPostContext yst out left right).state
      pointAddUnequalPostlude
      (pointAddUnequalPostEnv (pointAddUnequalPostContext yst out left right))
      (pointAddUnequalPostState (pointAddUnequalPostContext yst out left right))
      .normal :=
  step_pointAddUnequalPostludeGeneric
    (pointAddUnequalPostContext yst out left right)

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
