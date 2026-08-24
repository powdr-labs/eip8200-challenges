import Challenge.Modexp.Reference.Bytecode
import Challenge.Modexp.Reference.Proofs.Yul.BigArithmetic
import Challenge.Modexp.Reference.Proofs.Yul.BigDriver
import Challenge.Modexp.Reference.Proofs.Yul.BigExponent
import Challenge.Modexp.Reference.Proofs.Yul.BigFinal
import Challenge.Modexp.Reference.Proofs.Yul.BigFold
import Challenge.Modexp.Reference.Proofs.Yul.BigMath
import Challenge.Modexp.Reference.Proofs.Yul.BigMul
import Challenge.Modexp.Reference.Proofs.Yul.BigPath
import Challenge.Modexp.Reference.Proofs.Yul.BigResult
import Challenge.Modexp.Reference.Proofs.Yul.BigSetup
import Challenge.Modexp.Reference.Proofs.Yul.Execution
import Challenge.Modexp.Reference.Proofs.Yul.Program
import Challenge.Modexp.Reference.Proofs.Yul.SoftwareModexpMath
import Challenge.Modexp.Reference.Proofs.Yul.Word
import Challenge.Modexp.Reference.Proofs.Yul.WordMath
import YulEvmCompiler.Optimizer.Implementation.Pipeline

set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/-!
# Verified source/compiler bridge for the reference MODEXP program

This file pins the concrete path from `reference.yul` through parsing,
normalization, optimization, verified compilation, and assembly to the frozen
artifact. The semantic proof can be supplied independently as a proof of the
public `Challenge.Modexp.Yul.Correct verifiedProgram` predicate.

The `native_decide` uses below prove only finite facts about this fixed source
and artifact. The optimizer equivalence is the verified pipeline theorem.
-/

namespace Challenge.Modexp.Reference.Proofs.Yul

open YulSemantics (Block)
open YulSemantics.EVM (Op ExternalCalls ExternalCreates ExternalGas)
open YulEvmCompiler
open Challenge.YulProof.ClosedEvm

/-- Concrete evidence that parsing the fixed source succeeds. -/
theorem referenceParseSucceeded : referenceBlock?.isSome := by
  native_decide

/-- The concrete block returned by parsing `reference.yul`. -/
def referenceParsedBlock : Block Op :=
  referenceBlock?.get referenceParseSucceeded

/-- The normalized reference block used by the proof-side compiler route. -/
def referenceNormalizedBlock : Block Op :=
  @Optimizer.Normalize.normalize dialect referenceParsedBlock

/-- The verified optimizer candidate used by the proof-side compiler route.
The production `compileSource` result is pinned independently below. -/
def referenceOptimizedBlock : Block Op :=
  (Optimizer.optimizerPipeline
    (calls := ExternalCalls.none) (creates := ExternalCreates.none)
    (gasOracle := ExternalGas.none)).run
      referenceNormalizedBlock

/-- Concrete evidence that the verified backend accepts the optimized block. -/
theorem referenceCompileSucceeded :
    (compile referenceOptimizedBlock).isSome := by
  native_decide

def referenceInstructions : List Instr :=
  (compile referenceOptimizedBlock).get referenceCompileSucceeded

/-- Parsing succeeds and returns `referenceParsedBlock`. -/
theorem referenceBlock?_eq : referenceBlock? = some referenceParsedBlock := by
  exact Option.eq_some_of_isSome referenceParseSucceeded

/-- Source-text-facing functional obligation for the MODEXP reference. This
pins the parsed source while keeping its target the public Yul challenge. -/
def ReferenceCorrect : Prop :=
  ∀ block, referenceBlock? = some block → Challenge.Modexp.Yul.Correct block

/-- Compatibility name retained for downstream users of the original direct
proof API. -/
abbrev ReferenceComputesResult := ReferenceCorrect

theorem referenceComputesResult_iff :
    ReferenceCorrect ↔ Challenge.Modexp.Yul.Correct referenceParsedBlock := by
  constructor
  · intro h
    exact h referenceParsedBlock referenceBlock?_eq
  · intro h block hblock
    rw [referenceBlock?_eq] at hblock
    cases hblock
    exact h

theorem referenceParsedBlock_eq_verifiedProgram :
    referenceParsedBlock = verifiedProgram := by
  apply YulSemantics.SyntaxEq.stmtsBeq_eq
  native_decide

/-- The parser returns exactly the readable proof-side AST. -/
theorem referenceBlock?_eq_verifiedProgram :
    referenceBlock? = some verifiedProgram := by
  rw [referenceBlock?_eq, referenceParsedBlock_eq_verifiedProgram]

/-- A direct proof of the readable AST discharges the source-text obligation. -/
theorem referenceComputesResult_of_verifiedProgram
    (h : Challenge.Modexp.Yul.Correct verifiedProgram) : ReferenceCorrect := by
  rw [referenceComputesResult_iff, referenceParsedBlock_eq_verifiedProgram]
  exact h

/-- Functional correctness of the actual parsed MODEXP reference source
against the public, auditor-facing Yul specification. -/
theorem referenceCorrect : ReferenceCorrect := by
  exact referenceComputesResult_of_verifiedProgram
    Execution.verifiedProgram_computesResult

/-- The parsed reference block directly satisfies the public Yul challenge. -/
theorem referenceParsedBlock_correct :
    Challenge.Modexp.Yul.Correct referenceParsedBlock :=
  referenceComputesResult_iff.mp referenceCorrect

/-- Compatibility theorem for the original proof-facing name. -/
theorem referenceComputesResult : ReferenceComputesResult := referenceCorrect

/-- The production source entry point reproduces the frozen bytes. -/
theorem referenceBytecode?_eq : referenceBytecode? = some referenceBytecode := by
  native_decide

/-- The verified backend accepts the successful optimizer candidate. -/
theorem referenceOptimized_compile :
    compile referenceOptimizedBlock = some referenceInstructions := by
  exact Option.eq_some_of_isSome referenceCompileSucceeded

/-- Its accepted instruction list assembles to the frozen artifact. -/
theorem referenceInstructions_assemble :
    assemble referenceInstructions = referenceBytecode := by
  native_decide

/-- Normalization and the production optimizer preserve the complete big-step
behavior of the parsed program. -/
theorem reference_runEquiv :
    Optimizer.RunEquivBlock dialect referenceParsedBlock
      referenceOptimizedBlock := by
  simpa [referenceNormalizedBlock, referenceOptimizedBlock,
    Optimizer.optimizerPipeline] using
    (Optimizer.normalize_optimizerPipelineRounds_runEquiv
      (calls := ExternalCalls.none) (creates := ExternalCreates.none)
      (gasOracle := ExternalGas.none)
      Optimizer.pipelineRounds referenceParsedBlock)

/-- The MODEXP obligation may therefore be proved against either the readable
parsed source or the exact optimized block accepted by the backend. -/
theorem computesResult_optimized_iff :
    Challenge.Modexp.Yul.Correct referenceOptimizedBlock ↔
      Challenge.Modexp.Yul.Correct referenceParsedBlock := by
  constructor
  · intro h
    exact h.map_program (fun initial finalEnv final outcome hrun =>
      (reference_runEquiv initial finalEnv final outcome).mpr hrun)
  · intro h
    exact h.map_program (fun initial finalEnv final outcome hrun =>
      (reference_runEquiv initial finalEnv final outcome).mp hrun)

/-- End-to-end verified-compiler route for the frozen reference. Parsing,
optimization, backend compilation, and assembly are proved above; the direct
Yul semantics and initial-state abstraction remain explicit hypotheses. -/
theorem reference_correct_of_yul
    (hyul : ReferenceCorrect)
    (habs : AbstractsInitialState referenceBytecode) :
    Correct referenceBytecode := by
  rw [← referenceInstructions_assemble] at habs ⊢
  apply correct_of_computesResult referenceOptimized_compile
  · rw [referenceInstructions_assemble, referenceBytecode_size]
    norm_num
  · exact habs
  · exact computesResult_optimized_iff.mpr
      (referenceComputesResult_iff.mp hyul)

/-- The completed direct source proof discharges the functional premise of
the verified-compiler route; only the generic initial-state representation
premise remains explicit. -/
theorem reference_correct_via_yul
    (habs : AbstractsInitialState referenceBytecode) :
    Correct referenceBytecode :=
  reference_correct_of_yul referenceCorrect habs

end Challenge.Modexp.Reference.Proofs.Yul
