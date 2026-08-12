import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalDefs
import Challenge.Bls12381G1Msm.Reference.Proofs.SourceVEnvRestore

set_option warningAsError true

/-! Entry into the unequal-x G1MSM `pointAdd` path. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

theorem step_pointAddXUnequal (yst : EvmState) (out left right : U256)
    (hxeq : pointAddXEqValue yst out left right = 0) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddInitialEnv out left right) (pointAddFiniteState yst out left right)
      pointAddStmt5 (pointAddInitialEnv out left right)
      (pointAddXEqState yst out left right) .normal := by
  rw [pointAddStmt5_eq]
  exact Step.ifFalse (step_pointAddXEq yst out left right) hxeq

def pointAddUnequalNumeratorInitialEnv (out left right : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  bindZeros Challenge.EvmProof.modexpExec.toDialect ["\x00128", "\x00129"] ++
    pointAddInitialEnv out left right

theorem step_pointAddUnequalNumeratorInit (yst : EvmState)
    (out left right : U256) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddInitialEnv out left right) (pointAddXEqState yst out left right)
      pointAddUnequalNumeratorInitStmt
      (pointAddUnequalNumeratorInitialEnv out left right)
      (pointAddXEqState yst out left right) .normal := by
  rw [pointAddUnequalNumeratorInitStmt_eq]
  simpa [pointAddUnequalNumeratorInitialEnv] using
    (Step.letZero (D := Challenge.EvmProof.modexpExec.toDialect)
      (funs := pointAddBodyFuns) (V := pointAddInitialEnv out left right)
      (st := pointAddXEqState yst out left right)
      (vars := ["\x00128", "\x00129"]))

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
