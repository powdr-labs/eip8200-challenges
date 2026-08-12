import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalXSubLeftRepair

set_option warningAsError true

/-! Opaque selected result/environment for the first unequal-point subtraction. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def pointAddUnequalXSubLeftResult (yst : EvmState) (out left right : U256) :
    U256 × U256 :=
  if pointAddUnequalXSubLeftRepairValue yst out left right = 0 then
    pointAddUnequalXSubLeftRaw yst out left right
  else pointAddUnequalXSubLeftRepaired yst out left right

def pointAddUnequalXSubLeftSelectedEnv (yst : EvmState)
    (out left right : U256) : VEnv Challenge.EvmProof.modexpExec.toDialect :=
  if pointAddUnequalXSubLeftRepairValue yst out left right = 0 then
    pointAddUnequalXSubLeftRawEnv yst out left right
  else pointAddUnequalXSubLeftRepairedEnv yst out left right

theorem step_pointAddUnequalXSubLeftRepairSelected (yst : EvmState)
    (out left right : U256) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect ([] :: pointAddBodyFuns)
      (pointAddUnequalXSubLeftRawEnv yst out left right)
      (pointAddUnequalXSubLeftRawState yst out left right)
      pointAddUnequalXSubLeftRepairStmt
      (pointAddUnequalXSubLeftSelectedEnv yst out left right)
      (pointAddUnequalXSubLeftRawState yst out left right) .normal := by
  by_cases h : pointAddUnequalXSubLeftRepairValue yst out left right = 0
  · rw [pointAddUnequalXSubLeftRepairStmt_parts]
    rw [pointAddUnequalXSubLeftSelectedEnv, if_pos h]
    exact Step.ifFalse
      (step_pointAddUnequalXSubLeftRepairCondition yst out left right) h
  · rw [pointAddUnequalXSubLeftSelectedEnv, if_neg h]
    exact step_pointAddUnequalXSubLeftRepair yst out left right h

theorem pointAddUnequalXSubLeftSelectedEnv_hi (yst : EvmState)
    (out left right : U256) :
    VEnv.get (pointAddUnequalXSubLeftSelectedEnv yst out left right) "fc0_81" =
      some (pointAddUnequalXSubLeftResult yst out left right).1 := by
  by_cases h : pointAddUnequalXSubLeftRepairValue yst out left right = 0
  · rw [pointAddUnequalXSubLeftSelectedEnv, if_pos h,
      pointAddUnequalXSubLeftResult, if_pos h]
    exact pointAddUnequalXSubLeftRawEnv_hi yst out left right
  · rw [pointAddUnequalXSubLeftSelectedEnv, if_neg h,
      pointAddUnequalXSubLeftResult, if_neg h]
    exact pointAddUnequalXSubLeftRepairedEnv_hi yst out left right

theorem pointAddUnequalXSubLeftSelectedEnv_lo (yst : EvmState)
    (out left right : U256) :
    VEnv.get (pointAddUnequalXSubLeftSelectedEnv yst out left right) "fc0_82" =
      some (pointAddUnequalXSubLeftResult yst out left right).2 := by
  by_cases h : pointAddUnequalXSubLeftRepairValue yst out left right = 0
  · rw [pointAddUnequalXSubLeftSelectedEnv, if_pos h,
      pointAddUnequalXSubLeftResult, if_pos h]
    exact pointAddUnequalXSubLeftRawEnv_lo yst out left right
  · rw [pointAddUnequalXSubLeftSelectedEnv, if_neg h,
      pointAddUnequalXSubLeftResult, if_neg h]
    exact pointAddUnequalXSubLeftRepairedEnv_lo yst out left right

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
