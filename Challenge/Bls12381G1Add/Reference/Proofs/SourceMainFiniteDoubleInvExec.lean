import Challenge.Bls12381G1Add.Reference.Proofs.SourceMainFiniteDoubleState
import Challenge.Bls12381G1Add.Reference.Proofs.SourceFpInvResultBridge

set_option warningAsError true

/-! # Relational execution of the doubling-slope inversion call -/

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM
open Challenge.Bls12381.ProofSupport

private theorem mainFiniteDoubleStmt4_shape : mainFiniteDoubleStmt4 =
    .letDecl ["\x00109", "\x00110"]
      (some (.call "\x0010" [.var "\x00107", .var "\x00108"])) := by
  rfl

/-- The native `fpInv` call preserves the EVM state and binds the two stable
inversion-result words.  Keeping this proof in a leaf module prevents the
interpreter proofs for the surrounding slope schedule from unfolding it. -/
theorem step_mainFiniteDoubleStmt4 (yst : EvmState)
    (hden : Fp.Canonical (fpInvInputLimbs
      (mainFiniteDoubleDenominatorWords yst).1
      (mainFiniteDoubleDenominatorWords yst).2)) :
    ExecStmt Challenge.YulProof.ClosedEvm.exec.toDialect ([] :: mainFuns)
      (mainFiniteDoubleEnv4 yst) (mainFiniteDoubleDenArgsState yst)
      mainFiniteDoubleStmt4 (mainFiniteDoubleEnv5 yst)
      (mainFiniteDoubleState2 yst) .normal := by
  let den := mainFiniteDoubleDenominatorWords yst
  have hargs : EvalArgs Challenge.YulProof.ClosedEvm.exec.toDialect
      ([] :: mainFuns) (mainFiniteDoubleEnv4 yst)
      (mainFiniteDoubleDenArgsState yst)
      [.var "\x00107", .var "\x00108"]
      (.vals [den.1, den.2] (mainFiniteDoubleDenArgsState yst)) :=
    Step.argsCons (Step.argsCons Step.argsNil (Step.var (by rfl)))
      (Step.var (by rfl))
  have hcall := eval_fpInv_call_result den.1 den.2 (by rfl) hargs hden
  rw [mainFiniteDoubleStmt4_shape, mainFiniteDoubleEnv5_eq,
    mainFiniteDoubleState2_eq]
  exact Step.letVal hcall (by rfl)

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
