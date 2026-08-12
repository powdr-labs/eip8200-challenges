import Challenge.Bls12381G2Msm.Reference.Proofs.AssemblyOptimize
import Challenge.Bls12381G2Msm.Reference.Proofs.StackCertificateSound
import Challenge.Bls12381G2Msm.Reference.Proofs.ByteAssembly
import Challenge.Bls12381G2Msm.Spec
import Challenge.Bls12381G2Msm.ProofSupport.YulDialect
import Challenge.EvmProof.ModexpCallRealization
import Challenge.EvmProof.ProfiledCorrectness

set_option warningAsError true

/-!
# Profiled correctness of the concrete G2MSM compiler artifact

This module instantiates the generic profiled compiler theorem with the exact
frozen normalized source block and its checked assembly, stack, lowering, and
byte certificates. Source-level G2MSM correctness remains a separate staged
proof boundary.
-/

namespace Challenge.Bls12381G2Msm.Reference.Proofs.CompilerCorrectness

open EvmSemantics
open EvmSemantics.EVM
open YulSemantics (Outcome VEnv)
open YulSemantics.EVM (EvmState U256)
open YulEvmCompiler
open Challenge.EvmProof
open Challenge.Bls12381G2Msm.Reference.Proofs.Compilation

theorem executionConfig_modexp_enabled :
    Precompile.isPrecompileWithConfig
      Challenge.Bls12381G2Msm.executionConfig .Osaka
        Precompile.modexpAddress = true := by
  decide

/-- A source execution of the exact frozen normalized block is simulated by
the exact lowered instruction artifact under the caller profile. -/
theorem referenceCompiledBlock_correct
    {yst0 : EvmState}
    {V' : VEnv Challenge.Bls12381G2Msm.ProofSupport.Yul.localDialect}
    {yst' : EvmState} {o : Outcome}
    (hrun : YulSemantics.Run
      Challenge.Bls12381G2Msm.ProofSupport.Yul.localDialect
      referenceCompiledBlock yst0 V' yst' o) :
    ∃ b : Nat, ∀ s0 : State,
      FrameOK (assemble referenceInstructions) s0 →
      StateMatch yst0 s0 →
      CallerProfile Challenge.Bls12381G2Msm.executionConfig s0 →
      s0.pc = UInt256.ofNat 0 → s0.stack = [] →
      b ≤ s0.gasAvailable →
      ∃ s', Steps s0 s' ∧ s'.callStack = [] ∧ StateMatch yst' s' ∧
        ((o = .normal ∧ s'.halt = .Success ∧ s'.hReturn = .empty) ∨
         (o = .halt ∧ HaltedMatch yst' s')) := by
  letI : ExternalModel :=
    Challenge.Bls12381G2Msm.ProofSupport.Yul.localModel
  have hlow : lowerProg (optimizeAsm referenceAssembly) =
      some referenceInstructions := by
    rw [referenceAssembly_optimize]
    exact referenceAssembly_lower
  have hbound : ∀ mid, ASteps (optimizeAsm referenceAssembly)
      ⟨optimizeAsm referenceAssembly, [], yst0⟩ mid →
      mid.stk.length ≤ 1023 := by
    intro mid hsteps
    rw [referenceAssembly_optimize] at hsteps
    exact referenceAssembly_stack_bound yst0 mid hsteps
  exact profiled_compiledAssembly_correct
    (model := Challenge.Bls12381G2Msm.ProofSupport.Yul.localModel)
    (successfulModexpCalls_realized _ executionConfig_modexp_enabled)
    rfl referenceCompiled_compileProgram hlow hbound hrun

end Challenge.Bls12381G2Msm.Reference.Proofs.CompilerCorrectness
