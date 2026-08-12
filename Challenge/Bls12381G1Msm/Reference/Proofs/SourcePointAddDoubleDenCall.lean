import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddDoubleDen

set_option warningAsError true

/-! Opaque `fpAdd` composition for the point-doubling denominator. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def pointAddDoubleDenResult (yst : EvmState) (out left right : U256) :
    U256 × U256 :=
  fpAddResult (pointAddDoubleLeftYHi yst out left right)
    (pointAddDoubleLeftYLo yst out left right)
    (pointAddDoubleLeftYHi yst out left right)
    (pointAddDoubleLeftYLo yst out left right)

def pointAddDoubleDenEnv (yst : EvmState) (out left right : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  ["\x00116", "\x00117"].zip
    [(pointAddDoubleDenResult yst out left right).1,
      (pointAddDoubleDenResult yst out left right).2] ++
    pointAddDoubleNum3Env yst out left right

theorem step_pointAddDoubleDen (yst : EvmState) (out left right : U256) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddDoubleNum3Env yst out left right)
      (pointAddDoubleXSqState yst out left right) pointAddDoubleDenExpr
      (.vals [(pointAddDoubleDenResult yst out left right).1,
        (pointAddDoubleDenResult yst out left right).2]
        (pointAddDoubleDenArgsState yst out left right)) := by
  rw [pointAddDoubleDenExpr_eq]
  exact step_fpAdd_of_args _ _ _ _
    (step_pointAddDoubleDenArgs yst out left right) (by rfl)

theorem step_pointAddDoubleDenStmt (yst : EvmState) (out left right : U256) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddDoubleNum3Env yst out left right)
      (pointAddDoubleXSqState yst out left right) pointAddDoubleDenStmt
      (pointAddDoubleDenEnv yst out left right)
      (pointAddDoubleDenArgsState yst out left right) .normal := by
  rw [pointAddDoubleDenStmt_eq]
  exact Step.letVal (step_pointAddDoubleDen yst out left right) rfl

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
