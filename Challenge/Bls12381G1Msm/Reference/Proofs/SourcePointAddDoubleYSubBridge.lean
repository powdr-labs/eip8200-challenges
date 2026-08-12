import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddDoubleYMul
import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddDoubleYSubFull

set_option warningAsError true

/-! Single bridge from the computed y product to the generic final subtraction. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def pointAddDoubleYSubContext (yst : EvmState)
    (out left right : U256) : PointAddDoubleYSubContext where
  env := pointAddDoubleYMulEnv yst out left right
  state := pointAddDoubleYMulState yst out left right
  inputHi := (pointAddDoubleYMulResult yst out left right).1
  inputLo := (pointAddDoubleYMulResult yst out left right).2
  env_hi := by rfl
  env_lo := by rfl

def pointAddDoubleYSubConcreteEnv (yst : EvmState)
    (out left right : U256) : VEnv Challenge.EvmProof.modexpExec.toDialect :=
  pointAddDoubleYSubEnv (pointAddDoubleYSubContext yst out left right)

def pointAddDoubleYSubConcreteState (yst : EvmState)
    (out left right : U256) : EvmState :=
  pointAddDoubleYSubRawState (pointAddDoubleYSubContext yst out left right)

theorem step_pointAddDoubleYSubStmt (yst : EvmState)
    (out left right : U256) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddDoubleYMulEnv yst out left right)
      (pointAddDoubleYMulState yst out left right) pointAddDoubleYSubStmt
      (pointAddDoubleYSubConcreteEnv yst out left right)
      (pointAddDoubleYSubConcreteState yst out left right) .normal :=
  step_pointAddDoubleYSubGeneric
    (pointAddDoubleYSubContext yst out left right)

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
