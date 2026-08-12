import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalDenominatorWords
import Challenge.Bls12381G1Msm.Reference.Proofs.SourceVEnvRestore

set_option warningAsError true

/-! Concrete bridge for the complete raw unequal-denominator subtraction. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def pointAddUnequalDenominatorContext (yst : EvmState)
    (out left right : U256) : PointAddUnequalDenominatorContext where
  env := pointAddUnequalDenominatorInputsEnv yst out left right
  state := pointAddUnequalDenominatorInputsState yst out left right
  leftHi := pointAddUnequalLeftXHi yst out left right
  leftLo := pointAddUnequalLeftXLo yst out left right
  rightHi := pointAddUnequalRightXHi yst out left right
  rightLo := pointAddUnequalRightXLo yst out left right
  env_leftHi := by rfl
  env_leftLo := by rfl
  env_rightHi := by rfl
  env_rightLo := by rfl

def pointAddUnequalDenominatorRawEnv (yst : EvmState)
    (out left right : U256) : VEnv Challenge.EvmProof.modexpExec.toDialect :=
  restore (pointAddUnequalDenominatorRawInitialEnv yst out left right)
    (pointAddUnequalDenominatorHighEnvGeneric
      (pointAddUnequalDenominatorContext yst out left right))

theorem step_pointAddUnequalDenominatorRawDecl (yst : EvmState)
    (out left right : U256) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect
      ([] :: pointAddBodyFuns)
      (pointAddUnequalDenominatorInitialEnv yst out left right)
      (pointAddUnequalNumeratorInputsState yst out left right)
      pointAddUnequalDenominatorDeclStmt
      (pointAddUnequalDenominatorRawInitialEnv yst out left right)
      (pointAddUnequalNumeratorInputsState yst out left right) .normal := by
  rw [pointAddUnequalDenominatorDeclStmt_eq]
  simpa [pointAddUnequalDenominatorRawInitialEnv] using
    (Step.letZero (D := Challenge.EvmProof.modexpExec.toDialect)
      (funs := [] :: pointAddBodyFuns)
      (V := pointAddUnequalDenominatorInitialEnv yst out left right)
      (st := pointAddUnequalNumeratorInputsState yst out left right)
      (vars := ["fc0_74", "fc0_75"]))

theorem step_pointAddUnequalDenominatorRawBlock (yst : EvmState)
    (out left right : U256) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect
      ([] :: pointAddBodyFuns)
      (pointAddUnequalDenominatorRawInitialEnv yst out left right)
      (pointAddUnequalNumeratorInputsState yst out left right)
      pointAddUnequalDenominatorRawStmt
      (pointAddUnequalDenominatorRawEnv yst out left right)
      (pointAddUnequalDenominatorInputsState yst out left right) .normal := by
  let ctx := pointAddUnequalDenominatorContext yst out left right
  have hseq : ExecStmts Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns)
      (pointAddUnequalDenominatorRawInitialEnv yst out left right)
      (pointAddUnequalNumeratorInputsState yst out left right)
      pointAddUnequalDenominatorRawBody
      (pointAddUnequalDenominatorHighEnvGeneric ctx)
      (pointAddUnequalDenominatorInputsState yst out left right) .normal := by
    rw [pointAddUnequalDenominatorRawBody_eq]
    exact Step.seqCons (step_pointAddUnequalDenominatorLeftLo yst out left right)
      (Step.seqCons (step_pointAddUnequalDenominatorLeftHi yst out left right)
        (Step.seqCons (step_pointAddUnequalDenominatorRightLo yst out left right)
          (Step.seqCons (step_pointAddUnequalDenominatorRightHi yst out left right)
            (Step.seqCons (step_pointAddUnequalDenominatorLowGeneric ctx)
              (Step.seqCons (step_pointAddUnequalDenominatorHighGeneric ctx)
                Step.seqNil)))))
  rw [pointAddUnequalDenominatorRawStmt_eq,
    pointAddUnequalDenominatorRawEnv]
  exact Step.block hseq

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
