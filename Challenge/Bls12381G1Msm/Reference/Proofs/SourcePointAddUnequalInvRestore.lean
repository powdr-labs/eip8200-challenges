import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalInvOutput

set_option warningAsError true

/-! Value-only environment restoration for the inlined unequal inversion. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def pointAddUnequalInvGenericOutputEnv
    (tail : VEnv Challenge.EvmProof.modexpExec.toDialect)
    (hi lo resultHi resultLo : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  VEnv.setMany (pointAddUnequalInvGenericEnv tail hi lo)
    ["\x00132", "\x00133"] [resultHi, resultLo]

def pointAddUnequalInvGenericFinalEnv
    (tail : VEnv Challenge.EvmProof.modexpExec.toDialect)
    (hi lo resultHi resultLo : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  VEnv.setMany
    (VEnv.setMany
      (VEnv.setMany
        (VEnv.setMany (pointAddUnequalInvGenericWorkEnv tail hi lo)
          ["fc2_7"] [resultHi])
        ["fc2_8"] [resultLo])
      ["\x00132"] [resultHi])
    ["\x00133"] [resultLo]

theorem pointAddUnequalInvGenericFinalEnv_eq
    (tail : VEnv Challenge.EvmProof.modexpExec.toDialect)
    (hi lo resultHi resultLo : U256) :
    pointAddUnequalInvGenericFinalEnv tail hi lo resultHi resultLo =
      [("fc2_7", resultHi), ("fc2_8", resultLo)] ++
        pointAddUnequalInvGenericOutputEnv tail hi lo resultHi resultLo := by
  rfl

theorem restore_pointAddUnequalInvGenericFinalEnv
    (tail : VEnv Challenge.EvmProof.modexpExec.toDialect)
    (hi lo resultHi resultLo : U256) :
    @restore Challenge.EvmProof.modexpExec.toDialect
      (pointAddUnequalInvGenericEnv tail hi lo)
      (pointAddUnequalInvGenericFinalEnv tail hi lo resultHi resultLo) =
      pointAddUnequalInvGenericOutputEnv tail hi lo resultHi resultLo := by
  rw [pointAddUnequalInvGenericFinalEnv_eq]
  apply @restore_append_of_length_eq
    Challenge.EvmProof.modexpExec.toDialect
  rfl

theorem pointAddUnequalInvOutputEnv_eq_generic (yst : EvmState)
    (out left right : U256) :
    pointAddUnequalInvOutputEnv yst out left right =
      pointAddUnequalInvGenericOutputEnv
        (pointAddUnequalNumeratorEnv yst out left right)
        (pointAddUnequalDenominatorResult yst out left right).1
        (pointAddUnequalDenominatorResult yst out left right).2
        (pointAddUnequalInvResult yst out left right).1
        (pointAddUnequalInvResult yst out left right).2 := by
  rw [pointAddUnequalInvOutputEnv, pointAddUnequalInvInitialEnv_eq]
  rfl

theorem pointAddUnequalInvFinalWorkEnv_eq_generic (yst : EvmState)
    (out left right : U256) :
    pointAddUnequalInvFinalWorkEnv yst out left right =
      pointAddUnequalInvGenericFinalEnv
        (pointAddUnequalNumeratorEnv yst out left right)
        (pointAddUnequalDenominatorResult yst out left right).1
        (pointAddUnequalDenominatorResult yst out left right).2
        (pointAddUnequalInvResult yst out left right).1
        (pointAddUnequalInvResult yst out left right).2 := by
  rw [pointAddUnequalInvFinalWorkEnv, pointAddUnequalInvWorkEnv]
  rfl

theorem restore_pointAddUnequalInvFinalWorkEnv (yst : EvmState)
    (out left right : U256) :
    @restore Challenge.EvmProof.modexpExec.toDialect
      (pointAddUnequalInvInitialEnv yst out left right)
      (pointAddUnequalInvFinalWorkEnv yst out left right) =
      pointAddUnequalInvOutputEnv yst out left right := by
  rw [pointAddUnequalInvInitialEnv_eq,
    pointAddUnequalInvFinalWorkEnv_eq_generic,
    pointAddUnequalInvOutputEnv_eq_generic]
  exact restore_pointAddUnequalInvGenericFinalEnv _ _ _ _ _

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
