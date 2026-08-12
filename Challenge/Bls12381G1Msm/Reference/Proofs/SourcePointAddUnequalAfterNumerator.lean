import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalDenominatorFull
import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalAfterDenominatorInit
import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalXSubLeftPrefixRepair

set_option warningAsError true

/-! Opaque composition boundary after the unequal numerator subtraction. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def pointAddUnequalAfterNumeratorCode : Block Op :=
  pointAddUnequalDenominatorInitStmt ::
    pointAddUnequalAfterDenominatorInitCode

theorem step_pointAddUnequalAfterNumerator (yst : EvmState)
    (out left right : U256)
    (hhi : (pointAddUnequalDenominatorResult yst out left right).1.toNat <
      2 ^ 128)
    (hstate : pointAddUnequalDenominatorInputsState yst out left right =
      pointAddUnequalNumeratorInputsState yst out left right) :
    ∃ Vend stend,
      ExecStmts Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
        (pointAddUnequalNumeratorEnv yst out left right)
        (pointAddUnequalNumeratorInputsState yst out left right)
        pointAddUnequalAfterNumeratorCode Vend stend .normal := by
  obtain ⟨Vend, stend, hafter⟩ :=
    step_pointAddUnequalAfterDenominatorInit yst out left right hhi hstate
  refine ⟨Vend, stend, ?_⟩
  rw [pointAddUnequalAfterNumeratorCode]
  exact Step.seqCons (step_pointAddUnequalDenominatorInit yst out left right)
    hafter

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
