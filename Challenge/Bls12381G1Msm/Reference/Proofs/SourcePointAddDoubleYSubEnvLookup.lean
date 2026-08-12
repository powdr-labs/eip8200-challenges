import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddDoubleYSubBridge
import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddDoubleDeltaEnvLookup

set_option warningAsError true

/-! Opaque result and preserved-coordinate lookups after the final y subtraction. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

theorem pointAddDoubleYSubEnv_eq (ctx : PointAddDoubleYSubContext) :
    pointAddDoubleYSubEnv ctx =
      VEnv.set
        (VEnv.set ctx.env "\x00126" (pointAddDoubleYSubResult ctx).1)
        "\x00127" (pointAddDoubleYSubResult ctx).2 := by
  rw [pointAddDoubleYSubEnv, pointAddDoubleYSubWorkEnv,
    pointAddDoubleYSubHighOutEnv, pointAddDoubleYSubSelectedEnv]
  rw [venv_set_append_of_names_ne _ _ _ _ (by simp)]
  rw [venv_set_append_of_names_ne _ _ _ _ (by simp)]
  apply restore_append_of_length_eq
  rw [venv_set_length, venv_set_length]

theorem pointAddDoubleYMulEnv_xHi (yst : EvmState) (out left right : U256) :
    VEnv.get (pointAddDoubleYMulEnv yst out left right) "\x00122" =
      some (pointAddDoubleXSubResult yst out left right).1 := by
  rw [pointAddDoubleYMulEnv]
  simp only [List.zip, List.zipWith, List.cons_append, List.nil_append]
  rw [venv_get_cons_ne _ _ _ _ (by decide)]
  rw [venv_get_cons_ne _ _ _ _ (by decide)]
  rw [pointAddDoubleDeltaConcreteEnv, pointAddDoubleDeltaEnv_eq]
  rw [venv_get_set_ne _ _ _ _ (by decide)]
  rw [venv_get_set_ne _ _ _ _ (by decide)]
  change VEnv.get (pointAddDoubleDeltaInitialConcreteEnv yst out left right)
    "\x00122" = _
  rw [pointAddDoubleDeltaInitialConcreteEnv]
  rw [venv_get_append_of_names_ne _ _ _ (by simp [bindZeros])]
  exact pointAddDoubleXSubEnv_hi yst out left right

theorem pointAddDoubleYMulEnv_xLo (yst : EvmState) (out left right : U256) :
    VEnv.get (pointAddDoubleYMulEnv yst out left right) "\x00123" =
      some (pointAddDoubleXSubResult yst out left right).2 := by
  rw [pointAddDoubleYMulEnv]
  simp only [List.zip, List.zipWith, List.cons_append, List.nil_append]
  rw [venv_get_cons_ne _ _ _ _ (by decide)]
  rw [venv_get_cons_ne _ _ _ _ (by decide)]
  rw [pointAddDoubleDeltaConcreteEnv, pointAddDoubleDeltaEnv_eq]
  rw [venv_get_set_ne _ _ _ _ (by decide)]
  rw [venv_get_set_ne _ _ _ _ (by decide)]
  change VEnv.get (pointAddDoubleDeltaInitialConcreteEnv yst out left right)
    "\x00123" = _
  rw [pointAddDoubleDeltaInitialConcreteEnv]
  rw [venv_get_append_of_names_ne _ _ _ (by simp [bindZeros])]
  exact pointAddDoubleXSubEnv_lo yst out left right

theorem pointAddDoubleYMulEnv_tempHi (yst : EvmState) (out left right : U256) :
    VEnv.get (pointAddDoubleYMulEnv yst out left right) "\x00124" =
      some (pointAddDoubleDeltaResult
        (pointAddDoubleDeltaContext yst out left right)).1 := by
  rw [pointAddDoubleYMulEnv]
  simp only [List.zip, List.zipWith, List.cons_append, List.nil_append]
  rw [venv_get_cons_ne _ _ _ _ (by decide)]
  rw [venv_get_cons_ne _ _ _ _ (by decide)]
  exact pointAddDoubleDeltaConcreteEnv_hi yst out left right

theorem pointAddDoubleYMulEnv_tempLo (yst : EvmState) (out left right : U256) :
    VEnv.get (pointAddDoubleYMulEnv yst out left right) "\x00125" =
      some (pointAddDoubleDeltaResult
        (pointAddDoubleDeltaContext yst out left right)).2 := by
  rw [pointAddDoubleYMulEnv]
  simp only [List.zip, List.zipWith, List.cons_append, List.nil_append]
  rw [venv_get_cons_ne _ _ _ _ (by decide)]
  rw [venv_get_cons_ne _ _ _ _ (by decide)]
  exact pointAddDoubleDeltaConcreteEnv_lo yst out left right

theorem pointAddDoubleYSubConcreteEnv_xHi (yst : EvmState)
    (out left right : U256) :
    VEnv.get (pointAddDoubleYSubConcreteEnv yst out left right) "\x00122" =
      some (pointAddDoubleXSubResult yst out left right).1 := by
  rw [pointAddDoubleYSubConcreteEnv, pointAddDoubleYSubEnv_eq]
  rw [venv_get_set_ne _ _ _ _ (by decide)]
  rw [venv_get_set_ne _ _ _ _ (by decide)]
  change VEnv.get (pointAddDoubleYMulEnv yst out left right) "\x00122" = _
  exact pointAddDoubleYMulEnv_xHi yst out left right

theorem pointAddDoubleYSubConcreteEnv_xLo (yst : EvmState)
    (out left right : U256) :
    VEnv.get (pointAddDoubleYSubConcreteEnv yst out left right) "\x00123" =
      some (pointAddDoubleXSubResult yst out left right).2 := by
  rw [pointAddDoubleYSubConcreteEnv, pointAddDoubleYSubEnv_eq]
  rw [venv_get_set_ne _ _ _ _ (by decide)]
  rw [venv_get_set_ne _ _ _ _ (by decide)]
  change VEnv.get (pointAddDoubleYMulEnv yst out left right) "\x00123" = _
  exact pointAddDoubleYMulEnv_xLo yst out left right

theorem pointAddDoubleYSubConcreteEnv_yHi (yst : EvmState)
    (out left right : U256) :
    VEnv.get (pointAddDoubleYSubConcreteEnv yst out left right) "\x00126" =
      some (pointAddDoubleYSubResult
        (pointAddDoubleYSubContext yst out left right)).1 := by
  rw [pointAddDoubleYSubConcreteEnv, pointAddDoubleYSubEnv_eq]
  rw [venv_get_set_ne _ _ _ _ (by decide)]
  apply venv_get_set_self_of_some
  rfl

theorem pointAddDoubleYSubConcreteEnv_yLo (yst : EvmState)
    (out left right : U256) :
    VEnv.get (pointAddDoubleYSubConcreteEnv yst out left right) "\x00127" =
      some (pointAddDoubleYSubResult
        (pointAddDoubleYSubContext yst out left right)).2 := by
  rw [pointAddDoubleYSubConcreteEnv, pointAddDoubleYSubEnv_eq]
  apply venv_get_set_self_of_some
  rw [venv_get_set_ne _ _ _ _ (by decide)]
  rfl

theorem pointAddDoubleYSubConcreteEnv_tempHi (yst : EvmState)
    (out left right : U256) :
    VEnv.get (pointAddDoubleYSubConcreteEnv yst out left right) "\x00124" =
      some (pointAddDoubleDeltaResult
        (pointAddDoubleDeltaContext yst out left right)).1 := by
  rw [pointAddDoubleYSubConcreteEnv, pointAddDoubleYSubEnv_eq]
  rw [venv_get_set_ne _ _ _ _ (by decide)]
  rw [venv_get_set_ne _ _ _ _ (by decide)]
  change VEnv.get (pointAddDoubleYMulEnv yst out left right) "\x00124" = _
  exact pointAddDoubleYMulEnv_tempHi yst out left right

theorem pointAddDoubleYSubConcreteEnv_tempLo (yst : EvmState)
    (out left right : U256) :
    VEnv.get (pointAddDoubleYSubConcreteEnv yst out left right) "\x00125" =
      some (pointAddDoubleDeltaResult
        (pointAddDoubleDeltaContext yst out left right)).2 := by
  rw [pointAddDoubleYSubConcreteEnv, pointAddDoubleYSubEnv_eq]
  rw [venv_get_set_ne _ _ _ _ (by decide)]
  rw [venv_get_set_ne _ _ _ _ (by decide)]
  change VEnv.get (pointAddDoubleYMulEnv yst out left right) "\x00125" = _
  exact pointAddDoubleYMulEnv_tempLo yst out left right

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
