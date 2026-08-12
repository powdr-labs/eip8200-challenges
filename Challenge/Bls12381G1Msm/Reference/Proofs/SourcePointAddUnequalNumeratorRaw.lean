import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalNumeratorWords
import Challenge.Bls12381G1Msm.Reference.Proofs.SourceVEnvRestore

set_option warningAsError true

/-! Concrete bridge for the complete raw unequal-numerator subtraction. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def pointAddUnequalNumeratorContext (yst : EvmState)
    (out left right : U256) : PointAddUnequalNumeratorContext where
  env := pointAddUnequalNumeratorInputsEnv yst out left right
  state := pointAddUnequalNumeratorInputsState yst out left right
  leftHi := pointAddUnequalLeftYHi yst out left right
  leftLo := pointAddUnequalLeftYLo yst out left right
  rightHi := pointAddUnequalRightYHi yst out left right
  rightLo := pointAddUnequalRightYLo yst out left right
  env_leftHi := by rfl
  env_leftLo := by rfl
  env_rightHi := by rfl
  env_rightLo := by rfl

def pointAddUnequalNumeratorRawEnv (yst : EvmState)
    (out left right : U256) : VEnv Challenge.EvmProof.modexpExec.toDialect :=
  restore (pointAddUnequalNumeratorRawInitialEnv out left right)
    (pointAddUnequalNumeratorHighEnvGeneric
      (pointAddUnequalNumeratorContext yst out left right))

theorem step_pointAddUnequalNumeratorRawDecl (yst : EvmState)
    (out left right : U256) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect
      ([] :: pointAddBodyFuns)
      (pointAddUnequalNumeratorInitialEnv out left right)
      (pointAddXEqState yst out left right)
      pointAddUnequalNumeratorDeclStmt
      (pointAddUnequalNumeratorRawInitialEnv out left right)
      (pointAddXEqState yst out left right) .normal := by
  rw [pointAddUnequalNumeratorDeclStmt_eq]
  simpa [pointAddUnequalNumeratorRawInitialEnv] using
    (Step.letZero (D := Challenge.EvmProof.modexpExec.toDialect)
      (funs := [] :: pointAddBodyFuns)
      (V := pointAddUnequalNumeratorInitialEnv out left right)
      (st := pointAddXEqState yst out left right)
      (vars := ["fc0_67", "fc0_68"]))

theorem step_pointAddUnequalNumeratorRawBlock (yst : EvmState)
    (out left right : U256) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect
      ([] :: pointAddBodyFuns)
      (pointAddUnequalNumeratorRawInitialEnv out left right)
      (pointAddXEqState yst out left right)
      pointAddUnequalNumeratorRawStmt
      (pointAddUnequalNumeratorRawEnv yst out left right)
      (pointAddUnequalNumeratorInputsState yst out left right) .normal := by
  let ctx := pointAddUnequalNumeratorContext yst out left right
  have hseq : ExecStmts Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns)
      (pointAddUnequalNumeratorRawInitialEnv out left right)
      (pointAddXEqState yst out left right)
      pointAddUnequalNumeratorRawBody
      (pointAddUnequalNumeratorHighEnvGeneric ctx)
      (pointAddUnequalNumeratorInputsState yst out left right) .normal := by
    rw [pointAddUnequalNumeratorRawBody_eq]
    exact Step.seqCons (step_pointAddUnequalNumeratorLeftLo yst out left right)
      (Step.seqCons (step_pointAddUnequalNumeratorLeftHi yst out left right)
        (Step.seqCons (step_pointAddUnequalNumeratorRightLo yst out left right)
          (Step.seqCons (step_pointAddUnequalNumeratorRightHi yst out left right)
            (Step.seqCons (step_pointAddUnequalNumeratorLowGeneric ctx)
              (Step.seqCons (step_pointAddUnequalNumeratorHighGeneric ctx)
                Step.seqNil)))))
  rw [pointAddUnequalNumeratorRawStmt_eq,
    pointAddUnequalNumeratorRawEnv]
  exact Step.block hseq

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
