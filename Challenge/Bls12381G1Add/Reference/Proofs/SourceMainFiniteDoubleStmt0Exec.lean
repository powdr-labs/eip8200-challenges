import Challenge.Bls12381G1Add.Reference.Proofs.SourceMainFiniteDoubleStmt0Args
import Challenge.Bls12381G1Add.Reference.Proofs.SourceFpMulRelationalCall

set_option warningAsError true

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

private theorem mainFiniteDoubleStmt0_shape : mainFiniteDoubleStmt0 =
    .letDecl ["\x00103", "\x00104"]
      (some (.call "\x009"
        [.builtin .mload [.lit (.number 0)],
          .builtin .mload [.lit (.number 32)],
          .builtin .mload [.lit (.number 0)],
          .builtin .mload [.lit (.number 32)]])) := by
  rfl

/-- Relational execution of the source multiplication computing `x²`. -/
theorem step_mainFiniteDoubleStmt0 (yst : EvmState) :
    ExecStmt Challenge.YulProof.ClosedEvm.dialect ([] :: mainFuns)
      (mainFiniteEnv yst) (mainFiniteYZeroArgsState yst)
      mainFiniteDoubleStmt0 (mainFiniteDoubleEnv1 yst)
      (mainFiniteDoubleState1 yst) .normal := by
  let x := mainFiniteDoubleXWords yst
  have hargs := eval_mainFiniteDoubleStmt0Args yst
  have hcall := step_fpMul_call x.1 x.2 x.1 x.2 (by rfl) hargs
  rw [mainFiniteDoubleStmt0_shape, mainFiniteDoubleEnv1_eq,
    mainFiniteDoubleState1_eq]
  exact Step.letVal hcall (by rfl)

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
