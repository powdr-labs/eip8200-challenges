import Challenge.Bls12381G1Add.Reference.Proofs.CompilerCorrectness
import Challenge.Bls12381G1Add.Reference.Proofs.SourceRun

set_option warningAsError true

open Challenge.Bls12381G1Add.Reference.Proofs.CompilerCorrectness
open Challenge.Bls12381G1Add.Reference.Proofs.Compilation
open Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
open Challenge.EvmProof
open EvmSemantics EvmSemantics.EVM
open YulEvmCompiler

example (yst0 : YulSemantics.EVM.EvmState)
    (pre : MainBothInfinityPre yst0) :
    ∃ finalEnv final outcome,
      MainBothInfinityPost yst0 finalEnv final outcome ∧
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
            (outcome = .halt ∧ HaltedMatch final s')) :=
  referenceCompiledBlock_contract_correct
    main_bothInfinity_yulContract yst0 pre

example : EvmSemantics.EVM.Precompile.isPrecompileWithConfig
    Challenge.Bls12381G1Add.executionConfig .Osaka
      EvmSemantics.EVM.Precompile.modexpAddress = true :=
  executionConfig_modexp_enabled

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.CompilerCorrectness.executionConfig_modexp_enabled' does not depend on any axioms -/
#guard_msgs in
#print axioms executionConfig_modexp_enabled

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.CompilerCorrectness.referenceCompiledBlock_correct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms referenceCompiledBlock_correct

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.CompilerCorrectness.referenceCompiledBlock_contract_correct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms referenceCompiledBlock_contract_correct
