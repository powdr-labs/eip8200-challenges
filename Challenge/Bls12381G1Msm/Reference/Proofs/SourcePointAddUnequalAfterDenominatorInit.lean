import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalDenominatorFull
import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalAfterDenominator

set_option warningAsError true

/-! Opaque composition boundary after declaring the unequal denominator limbs. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def pointAddUnequalAfterDenominatorInitCode : Block Op :=
  pointAddUnequalDenominatorStmt :: pointAddUnequalAfterDenominatorCode

theorem step_pointAddUnequalAfterDenominatorInit (yst : EvmState)
    (out left right : U256)
    (hhi : (pointAddUnequalDenominatorResult yst out left right).1.toNat <
      2 ^ 128)
    (hstate : pointAddUnequalDenominatorInputsState yst out left right =
      pointAddUnequalNumeratorInputsState yst out left right) :
    ∃ Vend stend,
      ExecStmts Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
        (pointAddUnequalDenominatorInitialEnv yst out left right)
        (pointAddUnequalNumeratorInputsState yst out left right)
        pointAddUnequalAfterDenominatorInitCode Vend stend .normal := by
  obtain ⟨Vend, stend, hafter⟩ :=
    step_pointAddUnequalAfterDenominator yst out left right hhi
  refine ⟨Vend, stend, ?_⟩
  rw [pointAddUnequalAfterDenominatorInitCode]
  have hblock := step_pointAddUnequalDenominatorBlock yst out left right
  rw [hstate] at hblock
  exact Step.seqCons
    hblock hafter

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
