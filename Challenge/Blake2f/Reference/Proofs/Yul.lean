import Challenge.Blake2f.ProofSupport.Yul
import Challenge.Blake2f.Reference.Source
import Challenge.Blake2f.Reference.Bytecode
import Challenge.Blake2f.Reference.Proofs.Bytecode.ReferenceCorrect
import YulEvmCompiler.Optimizer.Implementation.Pipeline

set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/-!
# Frozen BLAKE2f source/compiler certificate

The finite `native_decide` checks in this module certify parsing, compilation,
and byte-for-byte assembly of the fixed source. They are deliberately separate
from the direct bytecode correctness proof.
-/

namespace Challenge.Blake2f.Reference.Proofs.Yul

open YulSemantics (Block)
open YulSemantics.EVM (Op ExternalCalls ExternalCreates)
open YulEvmCompiler
open Challenge.Blake2f.ProofSupport.Yul

theorem referenceParseSucceeded : referenceBlock?.isSome := by native_decide

def referenceParsedBlock : Block Op :=
  referenceBlock?.get referenceParseSucceeded

def referenceNormalizedBlock : Block Op :=
  @Optimizer.Normalize.normalize localDialect referenceParsedBlock

def referenceOptimizedBlock : Block Op :=
  (Optimizer.optimizerPipeline
    (calls := ExternalCalls.none) (creates := ExternalCreates.none)).run
      referenceNormalizedBlock

theorem referenceCompileSucceeded :
    (compile referenceOptimizedBlock).isSome := by native_decide

def referenceInstructions : List Instr :=
  (compile referenceOptimizedBlock).get referenceCompileSucceeded

theorem referenceBlock?_eq : referenceBlock? = some referenceParsedBlock :=
  Option.eq_some_of_isSome referenceParseSucceeded

def ReferenceComputesBehavior : Prop :=
  ∀ block, referenceBlock? = some block → ComputesBehavior block

theorem referenceComputesBehavior_iff :
    ReferenceComputesBehavior ↔ ComputesBehavior referenceParsedBlock := by
  constructor
  · intro h
    exact h referenceParsedBlock referenceBlock?_eq
  · intro h block hblock
    rw [referenceBlock?_eq] at hblock
    cases hblock
    exact h

theorem referenceBytecode?_eq : referenceBytecode? = some referenceBytecode := by
  native_decide

theorem referenceOptimized_compile :
    compile referenceOptimizedBlock = some referenceInstructions :=
  Option.eq_some_of_isSome referenceCompileSucceeded

theorem referenceInstructions_assemble :
    assemble referenceInstructions = referenceBytecode := by native_decide

/-- The optimizer/compiler output, after assembly, obeys the challenge spec. -/
theorem referenceCompiled_correct :
    Correct (assemble referenceInstructions) := by
  rw [referenceInstructions_assemble]
  exact Bytecode.ReferenceCorrect.reference_correct

theorem reference_runEquiv :
    Optimizer.RunEquivBlock localDialect referenceParsedBlock
      referenceOptimizedBlock := by
  simpa [referenceNormalizedBlock, referenceOptimizedBlock,
    Optimizer.optimizerPipeline] using
    (Optimizer.normalize_optimizerPipelineRounds_runEquiv
      (calls := ExternalCalls.none) (creates := ExternalCreates.none)
      Optimizer.pipelineRounds referenceParsedBlock)

theorem computesBehavior_optimized_iff :
    ComputesBehavior referenceOptimizedBlock ↔
      ComputesBehavior referenceParsedBlock := by
  constructor
  · intro h yst hmemory hhalted
    obtain ⟨V, yst', hrun, hresult⟩ := h yst hmemory hhalted
    exact ⟨V, yst', (reference_runEquiv _ _ _ _).mpr hrun, hresult⟩
  · intro h yst hmemory hhalted
    obtain ⟨V, yst', hrun, hresult⟩ := h yst hmemory hhalted
    exact ⟨V, yst', (reference_runEquiv _ _ _ _).mp hrun, hresult⟩

/-- Compiler-route endpoint. The unconditional direct-bytecode proof supplies
the final theorem without these source-semantics premises. -/
theorem reference_correct_of_yul
    (hbehavior : ReferenceComputesBehavior)
    (habstract : AbstractsInitialState referenceBytecode) :
    Correct referenceBytecode := by
  rw [← referenceInstructions_assemble] at habstract ⊢
  apply correct_of_computesBehavior referenceOptimized_compile
  · rw [referenceInstructions_assemble, referenceBytecode_size]
    norm_num
  · exact habstract
  · exact computesBehavior_optimized_iff.mpr
      (referenceComputesBehavior_iff.mp hbehavior)

end Challenge.Blake2f.Reference.Proofs.Yul
