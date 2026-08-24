import Challenge.Bls12381G1Add.Reference.Proofs.SourceMainFiniteDoubleStmt3Args
import Challenge.Bls12381G1Add.Reference.Proofs.SourceFpAddRelationalCall

set_option warningAsError true

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

private theorem mainFiniteDoubleStmt3_shape : mainFiniteDoubleStmt3 =
    .letDecl ["\x00107", "\x00108"]
      (some (.call "\x004"
        [.builtin .mload [.lit (.number 64)],
          .builtin .mload [.lit (.number 96)],
          .builtin .mload [.lit (.number 64)],
          .builtin .mload [.lit (.number 96)]])) := by
  rfl

theorem step_mainFiniteDoubleStmt3 (yst : EvmState) :
    ExecStmt Challenge.YulProof.ClosedEvm.dialect ([] :: mainFuns)
      (mainFiniteDoubleEnv3 yst) (mainFiniteDoubleState1 yst)
      mainFiniteDoubleStmt3 (mainFiniteDoubleEnv4 yst)
      (mainFiniteDoubleDenArgsState yst) .normal := by
  let y := mainFiniteDoubleYWords yst
  have hargs := eval_mainFiniteDoubleStmt3Args yst
  have hcall := step_fpAdd_call y.1 y.2 y.1 y.2 (by rfl) hargs
  rw [mainFiniteDoubleStmt3_shape, mainFiniteDoubleEnv4_eq]
  exact Step.letVal hcall (by rfl)

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
