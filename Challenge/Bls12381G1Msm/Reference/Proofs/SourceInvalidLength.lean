import Challenge.Bls12381G1Msm.Reference.Proofs.SourceInvalidLengthExec
import Challenge.Bls12381G1Add.ProofSupport.YulDialect
import Challenge.Bls12381G1Msm.SpecRefinement
import Challenge.EvmProof.ModexpExec

set_option warningAsError true

/-!
# G1MSM source rejection for invalid input lengths

This is the first source-semantics slice for the exact frozen backend block.
It proves that empty calldata and nonmultiples of the 160-byte term width take
the runtime's first `invalid()` branch.  Keeping this prefix separate avoids
elaborating any field or scalar-multiplication body for a length rejection.
-/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open EvmSemantics
open YulSemantics YulSemantics.EVM
open Challenge.EvmProof
open Challenge.Bls12381G1Msm.Reference.Proofs.Compilation

/-- Empty calldata and nonmultiples of 160 bytes take the exact backend's
first source-level `invalid()` branch. -/
theorem run_invalid_length {yst : EvmState}
    (hfit : yst.env.calldata.length < 2 ^ 256)
    (hbad : yst.env.calldata.length = 0 ∨
      yst.env.calldata.length % Challenge.Bls12381G1Msm.pairBytes ≠ 0)
    (_hhalted : yst.halted = none) :
    ∃ yst',
      Run Challenge.Bls12381G1Add.ProofSupport.Yul.localDialect
        referenceBackendBlock yst [] yst' .halt ∧
      yst'.halted = some (.invalid, []) := by
  let yst' : EvmState := { yst with halted := some (.invalid, []) }
  let funs : FunEnv modexpExec.toDialect :=
    [hoist modexpExec.toDialect referenceBackendBlock]
  have hsize := step_sizeStmt yst funs []
  have hinvalid := step_invalidLengthStmt funs [] hfit hbad
  have htail : ExecStmts modexpExec.toDialect funs [] yst
      (sizeStmt :: invalidLengthStmt :: referenceBackendBlock.drop 13)
      (sizeEnv yst []) yst' .halt :=
    Step.seqCons hsize (Step.seqStop hinvalid (by decide))
  have hbody := step_reference_function_prefix htail
  have hrun := Step.block
    (D := modexpExec.toDialect) hbody
  refine ⟨yst', ?_, rfl⟩
  simpa [Run, funs, restore, sizeEnv] using hrun

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
