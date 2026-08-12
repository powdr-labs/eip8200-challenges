import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddDoubleXSubLeftRepair

set_option warningAsError true

/-! Opaque selected result/environment for the first point-double subtraction. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def pointAddDoubleXSubLeftResult (yst : EvmState) (out left right : U256) :
    U256 × U256 :=
  if pointAddDoubleXSubLeftRepairValue yst out left right = 0 then
    pointAddDoubleXSubLeftRaw yst out left right
  else pointAddDoubleXSubLeftRepaired yst out left right

def pointAddDoubleXSubLeftSelectedEnv (yst : EvmState)
    (out left right : U256) : VEnv Challenge.EvmProof.modexpExec.toDialect :=
  if pointAddDoubleXSubLeftRepairValue yst out left right = 0 then
    pointAddDoubleXSubLeftRawEnv yst out left right
  else pointAddDoubleXSubLeftRepairedEnv yst out left right

theorem step_pointAddDoubleXSubLeftRepairSelected (yst : EvmState)
    (out left right : U256) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect ([] :: pointAddBodyFuns)
      (pointAddDoubleXSubLeftRawEnv yst out left right)
      (pointAddDoubleXSubLeftRawState yst out left right)
      pointAddDoubleXSubLeftRepairStmt
      (pointAddDoubleXSubLeftSelectedEnv yst out left right)
      (pointAddDoubleXSubLeftRawState yst out left right) .normal := by
  by_cases h : pointAddDoubleXSubLeftRepairValue yst out left right = 0
  · rw [pointAddDoubleXSubLeftRepairStmt_parts]
    rw [pointAddDoubleXSubLeftSelectedEnv, if_pos h]
    exact Step.ifFalse
      (step_pointAddDoubleXSubLeftRepairCondition yst out left right) h
  · rw [pointAddDoubleXSubLeftSelectedEnv, if_neg h]
    exact step_pointAddDoubleXSubLeftRepair yst out left right h

theorem pointAddDoubleXSubLeftSelectedEnv_hi (yst : EvmState)
    (out left right : U256) :
    VEnv.get (pointAddDoubleXSubLeftSelectedEnv yst out left right) "fc0_28" =
      some (pointAddDoubleXSubLeftResult yst out left right).1 := by
  by_cases h : pointAddDoubleXSubLeftRepairValue yst out left right = 0
  · rw [pointAddDoubleXSubLeftSelectedEnv, if_pos h,
      pointAddDoubleXSubLeftResult, if_pos h]
    exact pointAddDoubleXSubLeftRawEnv_hi yst out left right
  · rw [pointAddDoubleXSubLeftSelectedEnv, if_neg h,
      pointAddDoubleXSubLeftResult, if_neg h]
    exact pointAddDoubleXSubLeftRepairedEnv_hi yst out left right

theorem pointAddDoubleXSubLeftSelectedEnv_lo (yst : EvmState)
    (out left right : U256) :
    VEnv.get (pointAddDoubleXSubLeftSelectedEnv yst out left right) "fc0_29" =
      some (pointAddDoubleXSubLeftResult yst out left right).2 := by
  by_cases h : pointAddDoubleXSubLeftRepairValue yst out left right = 0
  · rw [pointAddDoubleXSubLeftSelectedEnv, if_pos h,
      pointAddDoubleXSubLeftResult, if_pos h]
    exact pointAddDoubleXSubLeftRawEnv_lo yst out left right
  · rw [pointAddDoubleXSubLeftSelectedEnv, if_neg h,
      pointAddDoubleXSubLeftResult, if_neg h]
    exact pointAddDoubleXSubLeftRepairedEnv_lo yst out left right

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
