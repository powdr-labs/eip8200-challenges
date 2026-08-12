import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalInvPrefix
import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalMid

set_option warningAsError true

/-! Opaque composition boundary after the unequal denominator subtraction. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def pointAddUnequalAfterDenominatorCode : Block Op :=
  pointAddUnequalInvInitStmt :: pointAddUnequalMidCode

theorem step_pointAddUnequalAfterDenominator (yst : EvmState)
    (out left right : U256)
    (hhi : (pointAddUnequalDenominatorResult yst out left right).1.toNat <
      2 ^ 128) :
    ∃ Vend stend,
      ExecStmts Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
        (pointAddUnequalDenominatorEnv yst out left right)
        (pointAddUnequalNumeratorInputsState yst out left right)
        pointAddUnequalAfterDenominatorCode Vend stend .normal := by
  obtain ⟨Vend, stend, hmid⟩ :=
    step_pointAddUnequalMid yst out left right hhi
  refine ⟨Vend, stend, ?_⟩
  rw [pointAddUnequalAfterDenominatorCode]
  exact Step.seqCons (step_pointAddUnequalInvInit yst out left right) hmid

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
