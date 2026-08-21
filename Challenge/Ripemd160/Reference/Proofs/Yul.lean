import Challenge.Ripemd160.ProofSupport.Yul
import Challenge.Ripemd160.Reference.Source
import Challenge.Ripemd160.Reference.Bytecode
import Challenge.Ripemd160.Reference.Proofs.Yul.Algorithm
import YulEvmCompiler.Optimizer.Implementation.Pipeline

set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/-!
# Verified source/compiler bridge for the reference RIPEMD-160 program

This file pins the complete concrete path from `reference.yul` to the frozen
artifact. The only remaining functional obligation on this route is
`ComputesDigest referenceParsedBlock`: a big-step proof that the parsed Yul
implements RIPEMD-160. Normalization and optimization preserve that property
by the verified optimizer's unconditional `RunEquivBlock` theorem.

The `native_decide` uses below establish finite, concrete artifact facts: the
result of parsing and compiling this fixed source. No universal semantic claim
is discharged by native evaluation.
-/

namespace Challenge.Ripemd160.Reference.Proofs.Yul

open YulSemantics (Block)
open YulSemantics.EVM (Op ExternalCalls ExternalCreates ExternalGas)
open YulEvmCompiler

/-- Concrete evidence that parsing the fixed source succeeds. -/
theorem referenceParseSucceeded : referenceBlock?.isSome := by
  native_decide

/-- The concrete block returned by parsing `reference.yul`. -/
def referenceParsedBlock : Block Op :=
  referenceBlock?.get referenceParseSucceeded

/-- The normalized reference block used by the production source compiler. -/
def referenceNormalizedBlock : Block Op :=
  @Optimizer.Normalize.normalize localDialect referenceParsedBlock

/-- The first (and successful) verified optimizer candidate used by
`YulParser.compileSource` for this source. -/
def referenceOptimizedBlock : Block Op :=
  (Optimizer.optimizerPipeline
    (calls := ExternalCalls.none) (creates := ExternalCreates.none)
    (gasOracle := ExternalGas.none)).run
      referenceNormalizedBlock

/-- The concrete instruction list accepted by the verified backend. -/
theorem referenceCompileSucceeded :
    (compile referenceOptimizedBlock).isSome := by
  native_decide

def referenceInstructions : List Instr :=
  (compile referenceOptimizedBlock).get referenceCompileSucceeded

/-- Parsing succeeds and returns `referenceParsedBlock`. -/
theorem referenceBlock?_eq : referenceBlock? = some referenceParsedBlock := by
  exact Option.eq_some_of_isSome referenceParseSucceeded

/-- Source-text-facing functional obligation: whatever block the parser
returns computes the digest. -/
def ReferenceComputesDigest : Prop :=
  ∀ block, referenceBlock? = some block → ComputesDigest block

theorem referenceComputesDigest_iff :
    ReferenceComputesDigest ↔ ComputesDigest referenceParsedBlock := by
  constructor
  · intro h
    exact h referenceParsedBlock referenceBlock?_eq
  · intro h block hblock
    rw [referenceBlock?_eq] at hblock
    cases hblock
    exact h

/-- The production source entry point reproduces the frozen bytes. -/
theorem referenceBytecode?_eq : referenceBytecode? = some referenceBytecode := by
  native_decide

/-- The verified backend accepts the successful optimizer candidate. -/
theorem referenceOptimized_compile :
    compile referenceOptimizedBlock = some referenceInstructions := by
  exact Option.eq_some_of_isSome referenceCompileSucceeded

/-- Assembling that accepted instruction list is byte-for-byte the frozen
reference artifact. -/
theorem referenceInstructions_assemble :
    assemble referenceInstructions = referenceBytecode := by
  native_decide

/-- Normalization followed by the production optimizer preserves the complete
big-step behavior of the parsed program. -/
theorem reference_runEquiv :
    Optimizer.RunEquivBlock localDialect referenceParsedBlock
      referenceOptimizedBlock := by
  simpa [referenceNormalizedBlock, referenceOptimizedBlock,
    Optimizer.optimizerPipeline] using
    (Optimizer.normalize_optimizerPipelineRounds_runEquiv
      (calls := ExternalCalls.none) (creates := ExternalCreates.none)
      (gasOracle := ExternalGas.none)
      Optimizer.pipelineRounds referenceParsedBlock)

/-- Hence the functional digest obligation can be proved against either the
auditable parsed source or the exact block accepted by the backend. -/
theorem computesDigest_optimized_iff :
    ComputesDigest referenceOptimizedBlock ↔
      ComputesDigest referenceParsedBlock := by
  constructor
  · intro h
    exact h.map_program (fun initial finalEnv final outcome hrun =>
      (reference_runEquiv initial finalEnv final outcome).mpr hrun)
  · intro h
    exact h.map_program (fun initial finalEnv final outcome hrun =>
      (reference_runEquiv initial finalEnv final outcome).mp hrun)

/-- End-to-end verified-compiler route for the frozen reference. The source
semantics and initial-frame abstraction are explicit hypotheses; parsing,
optimization, backend compilation, assembly, and target simulation are proved
here or in the reusable compiler library. -/
theorem reference_correct_of_yul
    (hyul : ReferenceComputesDigest)
    (habs : AbstractsInitialState referenceBytecode) :
    Correct referenceBytecode := by
  rw [← referenceInstructions_assemble] at habs ⊢
  apply correct_of_computesDigest referenceOptimized_compile
  · rw [referenceInstructions_assemble, referenceBytecode_size]
    norm_num
  · exact habs
  · exact computesDigest_optimized_iff.mpr (referenceComputesDigest_iff.mp hyul)

end Challenge.Ripemd160.Reference.Proofs.Yul
