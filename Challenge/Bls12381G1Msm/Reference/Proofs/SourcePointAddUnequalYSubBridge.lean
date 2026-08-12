import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalYMul
import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalYSubFull

set_option warningAsError true

/-! Single bridge from the computed y product to the generic final subtraction. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def pointAddUnequalYSubContext (yst : EvmState)
    (out left right : U256) : PointAddUnequalYSubContext where
  env := pointAddUnequalYMulEnv yst out left right
  state := pointAddUnequalYMulState yst out left right
  inputHi := (pointAddUnequalYMulResult yst out left right).1
  inputLo := (pointAddUnequalYMulResult yst out left right).2
  env_hi := by rfl
  env_lo := by rfl

def pointAddUnequalYSubConcreteEnv (yst : EvmState)
    (out left right : U256) : VEnv Challenge.EvmProof.modexpExec.toDialect :=
  pointAddUnequalYSubEnv (pointAddUnequalYSubContext yst out left right)

def pointAddUnequalYSubConcreteState (yst : EvmState)
    (out left right : U256) : EvmState :=
  pointAddUnequalYSubRawState (pointAddUnequalYSubContext yst out left right)

theorem step_pointAddUnequalYSubStmt (yst : EvmState)
    (out left right : U256) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddUnequalYMulEnv yst out left right)
      (pointAddUnequalYMulState yst out left right) pointAddUnequalYSubStmt
      (pointAddUnequalYSubConcreteEnv yst out left right)
      (pointAddUnequalYSubConcreteState yst out left right) .normal :=
  step_pointAddUnequalYSubGeneric
    (pointAddUnequalYSubContext yst out left right)

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
