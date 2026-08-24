import Challenge.Bls12381G1Add.Reference.Proofs.SourceSpec
import Challenge.Bls12381G1Add.Reference.Proofs.SourceProgram
import Challenge.Bls12381G1Add.YulSpec

set_option warningAsError true

/-!
# Correctness of the checked-in G1ADD Yul source

The universal theorem below targets `Challenge.Bls12381G1Add.Yul.Correct`.
The only concrete checks are parsing and equality with the readable frozen
normalized AST. There is deliberately no compiler, assembly, instruction, or
bytecode correctness theorem in this proof surface.
-/

namespace Challenge.Bls12381G1Add.Reference.Proofs.Yul

open YulSemantics
open Challenge.Bls12381G1Add.Reference.Proofs
open Challenge.Bls12381G1Add.Reference.Proofs.Compilation

/-- The normalized source AST satisfies the complete public Yul contract. -/
theorem referenceNormalized_correct :
    Challenge.Bls12381G1Add.Yul.Correct referenceCompiledBlock := by
  intro initial hpre
  obtain ⟨_hmemory, hhalted, input, hcalldata, hfit⟩ := hpre
  obtain ⟨final, hrun, hresult⟩ :=
    SourceSemantics.run_matches_spec initial input hcalldata hfit hhalted
  refine ⟨[], final, .halt, hrun, rfl, ?_⟩
  rw [hcalldata, Challenge.Bls12381G1Add.Yul.expected_toList]
  cases hspec : Challenge.Bls12381G1Add.spec input <;>
    simp only [hspec] at hresult ⊢
  · exact hresult
  · exact hresult

/-- Correctness transported back across semantics-preserving normalization. -/
theorem referenceParsedBlock_correct :
    Challenge.Bls12381G1Add.Yul.Correct referenceParsedBlock := by
  exact referenceNormalized_correct.map_program
    (fun initial finalEnv final outcome hrun =>
      (reference_runEquiv initial finalEnv final outcome).mpr hrun)

/-- Source-text-facing obligation: every successful parse of the checked-in
`reference.yul` block satisfies the public Yul specification. -/
def ReferenceCorrect : Prop :=
  ∀ block, Challenge.Bls12381G1Add.referenceBlock? = some block →
    Challenge.Bls12381G1Add.Yul.Correct block

theorem referenceBlock?_eq :
    Challenge.Bls12381G1Add.referenceBlock? = some referenceParsedBlock := by
  exact Option.eq_some_of_isSome referenceParseSucceeded

theorem reference_correct : ReferenceCorrect := by
  intro block hblock
  rw [referenceBlock?_eq] at hblock
  cases hblock
  exact referenceParsedBlock_correct

end Challenge.Bls12381G1Add.Reference.Proofs.Yul
