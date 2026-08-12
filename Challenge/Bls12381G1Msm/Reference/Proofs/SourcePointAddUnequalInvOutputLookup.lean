import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalInvRestore
import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalNumeratorEnvLookup

set_option warningAsError true

/-! Opaque limb projections from the unequal inversion output environment. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

theorem pointAddUnequalInvOutputEnv_numHi (yst : EvmState)
    (out left right : U256) :
    VEnv.get (pointAddUnequalInvOutputEnv yst out left right) "\x00128" =
      some (pointAddUnequalNumeratorResult yst out left right).1 := by
  rw [pointAddUnequalInvOutputEnv_eq_generic]
  simpa [pointAddUnequalInvGenericOutputEnv,
    pointAddUnequalInvGenericEnv, VEnv.setMany, VEnv.set, VEnv.get] using
      pointAddUnequalNumeratorEnv_hi yst out left right

theorem pointAddUnequalInvOutputEnv_numLo (yst : EvmState)
    (out left right : U256) :
    VEnv.get (pointAddUnequalInvOutputEnv yst out left right) "\x00129" =
      some (pointAddUnequalNumeratorResult yst out left right).2 := by
  rw [pointAddUnequalInvOutputEnv_eq_generic]
  simpa [pointAddUnequalInvGenericOutputEnv,
    pointAddUnequalInvGenericEnv, VEnv.setMany, VEnv.set, VEnv.get] using
      pointAddUnequalNumeratorEnv_lo yst out left right

theorem pointAddUnequalInvOutputEnv_invHi (yst : EvmState)
    (out left right : U256) :
    VEnv.get (pointAddUnequalInvOutputEnv yst out left right) "\x00132" =
      some (pointAddUnequalInvResult yst out left right).1 := by
  rw [pointAddUnequalInvOutputEnv_eq_generic]
  rfl

theorem pointAddUnequalInvOutputEnv_invLo (yst : EvmState)
    (out left right : U256) :
    VEnv.get (pointAddUnequalInvOutputEnv yst out left right) "\x00133" =
      some (pointAddUnequalInvResult yst out left right).2 := by
  rw [pointAddUnequalInvOutputEnv_eq_generic]
  rfl

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
