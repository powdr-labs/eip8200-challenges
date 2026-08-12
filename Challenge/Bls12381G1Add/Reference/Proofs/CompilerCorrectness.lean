import Challenge.Bls12381G1Add.Reference.Proofs.StackCertificateChunks
import Challenge.Bls12381G1Add.Reference.Proofs.ByteAssembly
import Challenge.Bls12381G1Add.Spec
import Challenge.EvmProof.ModexpCallRealization

set_option warningAsError true

/-!
# Profiled correctness of the concrete G1ADD compiler artifact

This module instantiates the generic profiled compiler theorem with the
ordinary checked source, optimized assembly, stack, lowering, and byte
certificates.  It deliberately bypasses only the pinned compiler's opaque
partial stack-certificate generator.
-/

namespace Challenge.Bls12381G1Add.Reference.Proofs.CompilerCorrectness

open EvmSemantics
open EvmSemantics.EVM
open YulSemantics (Outcome VEnv)
open YulSemantics.EVM (EvmState U256)
open YulEvmCompiler
open Challenge.EvmProof
open Challenge.Bls12381G1Add.Reference.Proofs.Compilation

theorem executionConfig_modexp_enabled :
    Precompile.isPrecompileWithConfig
      Challenge.Bls12381G1Add.executionConfig .Osaka
        Precompile.modexpAddress = true := by
  decide

private theorem reference_lowering :
    lowerProg (optimizeAsm referenceAssembly) = some referenceInstructions := by
  change lowerProg referenceComputedOptimizedAssembly =
    some referenceInstructions
  rw [referenceComputedOptimizedAssembly_eq]
  exact referenceAssembly_lower

private theorem reference_stack_bound [ExternalModel] (initial : EvmState) :
    ∀ mid, ASteps (optimizeAsm referenceAssembly)
      ⟨optimizeAsm referenceAssembly, [], initial⟩ mid →
      mid.stk.length ≤ 1023 := by
  intro mid hsteps
  change ASteps referenceComputedOptimizedAssembly
    ⟨referenceComputedOptimizedAssembly, [], initial⟩ mid at hsteps
  rw [referenceComputedOptimizedAssembly_eq] at hsteps
  exact referenceAssembly_stack_bound initial mid hsteps

/-- A source execution of the exact frozen normalized block is simulated by
the exact 1,723-byte lowered instruction artifact under the caller profile. -/
theorem referenceCompiledBlock_correct
    {yst0 : EvmState}
    {V' : VEnv Challenge.Bls12381G1Add.ProofSupport.Yul.localDialect}
    {yst' : EvmState} {o : Outcome}
    (hrun : YulSemantics.Run
      Challenge.Bls12381G1Add.ProofSupport.Yul.localDialect
      referenceCompiledBlock yst0 V' yst' o) :
    ∃ b : Nat, ∀ s0 : State,
      FrameOK (assemble referenceInstructions) s0 →
      StateMatch yst0 s0 →
      CallerProfile Challenge.Bls12381G1Add.executionConfig s0 →
      s0.pc = UInt256.ofNat 0 → s0.stack = [] →
      b ≤ s0.gasAvailable →
      ∃ s', Steps s0 s' ∧ s'.callStack = [] ∧ StateMatch yst' s' ∧
        ((o = .normal ∧ s'.halt = .Success ∧ s'.hReturn = .empty) ∨
         (o = .halt ∧ HaltedMatch yst' s')) := by
  letI : ExternalModel :=
    Challenge.Bls12381G1Add.ProofSupport.Yul.localModel
  exact profiled_compiledAssembly_correct
    (model := Challenge.Bls12381G1Add.ProofSupport.Yul.localModel)
    (successfulModexpCalls_realized _ executionConfig_modexp_enabled)
    rfl referenceCompiled_compileProgram reference_lowering
    (reference_stack_bound yst0) hrun

/-- Transport any relational contract for the frozen G1ADD source block to a
profiled target-EVM execution. -/
theorem referenceCompiledBlock_contract_correct
    {pre : EvmState → Prop}
    {post : EvmState →
      VEnv Challenge.Bls12381G1Add.ProofSupport.Yul.localDialect →
      EvmState → Outcome → Prop}
    (contract : YulRunContract
      Challenge.Bls12381G1Add.ProofSupport.Yul.localDialect
      referenceCompiledBlock pre post) :
    ∀ yst0, pre yst0 →
      ∃ finalEnv final outcome,
        post yst0 finalEnv final outcome ∧
        ∃ b : Nat, ∀ s0 : State,
          FrameOK (assemble referenceInstructions) s0 →
          StateMatch yst0 s0 →
          CallerProfile Challenge.Bls12381G1Add.executionConfig s0 →
          s0.pc = UInt256.ofNat 0 → s0.stack = [] →
          b ≤ s0.gasAvailable →
          ∃ s', Steps s0 s' ∧ s'.callStack = [] ∧
            StateMatch final s' ∧
            ((outcome = .normal ∧ s'.halt = .Success ∧
                s'.hReturn = .empty) ∨
              (outcome = .halt ∧ HaltedMatch final s')) := by
  letI : ExternalModel :=
    Challenge.Bls12381G1Add.ProofSupport.Yul.localModel
  exact profiled_compiledAssembly_contract_correct
    (model := Challenge.Bls12381G1Add.ProofSupport.Yul.localModel)
    (successfulModexpCalls_realized _ executionConfig_modexp_enabled)
    rfl referenceCompiled_compileProgram reference_lowering
    (fun initial => reference_stack_bound initial) contract

end Challenge.Bls12381G1Add.Reference.Proofs.CompilerCorrectness
