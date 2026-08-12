import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddRightInfinity

set_option warningAsError true

/-! Fall-through of both G1MSM `pointAdd` infinity identity branches. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def pointAddLeftInfinityValue (yst : EvmState) (out left right : U256) : U256 :=
  pointInfinityResult (pointAddLeftPointerState yst out left right)
    (pointAddLeftPointer yst out left right)

def pointAddRightInfinityValue (yst : EvmState) (out left right : U256) : U256 :=
  pointInfinityResult (pointAddRightPointerState yst out left right)
    (pointAddRightPointer yst out left right)

theorem step_pointAddLeftInfinityFalse (yst : EvmState) (out left right : U256)
    (hfinite : pointAddLeftInfinityValue yst out left right = 0) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddInitialEnv out left right)
      (pointAddPrefixState yst out left right) pointAddStmt3
      (pointAddInitialEnv out left right)
      (pointAddLeftInfinityState yst out left right) .normal := by
  rw [pointAddStmt3_eq]
  exact Step.ifFalse (step_pointAddLeftInfinityCondition yst out left right)
    hfinite

theorem step_pointAddRightInfinityFalse (yst : EvmState) (out left right : U256)
    (hfinite : pointAddRightInfinityValue yst out left right = 0) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddInitialEnv out left right)
      (pointAddLeftInfinityState yst out left right) pointAddStmt4
      (pointAddInitialEnv out left right)
      (pointAddRightInfinityState yst out left right) .normal := by
  rw [pointAddStmt4_eq]
  exact Step.ifFalse (step_pointAddRightInfinityCondition yst out left right)
    hfinite

theorem step_pointAddFinitePrefix (yst : EvmState) (out left right : U256)
    (hleft : pointAddLeftInfinityValue yst out left right = 0)
    (hright : pointAddRightInfinityValue yst out left right = 0) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddInitialEnv out left right)
      (pointAddPrefixState yst out left right) [pointAddStmt3, pointAddStmt4]
      (pointAddInitialEnv out left right)
      (pointAddRightInfinityState yst out left right) .normal :=
  Step.seqCons (step_pointAddLeftInfinityFalse yst out left right hleft)
    (Step.seqCons (step_pointAddRightInfinityFalse yst out left right hright)
      Step.seqNil)

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
