import Challenge.Bls12381G2Add.Reference.Proofs.StackCertificateChunks

set_option warningAsError true

open Challenge.Bls12381G2Add.Reference.Proofs.Compilation

local instance : YulEvmCompiler.ExternalModel :=
  Challenge.Bls12381G2Add.ProofSupport.Yul.localModel

example : referenceCheckedCert.Valid referenceOptimizedAssembly :=
  referenceCheckedCert_valid

example : referenceCheckedCert.Bounded := referenceCheckedCert_bounded

example (yst : YulSemantics.EVM.EvmState) :
    ∀ mid, YulEvmCompiler.ASteps referenceOptimizedAssembly
      ⟨referenceOptimizedAssembly, [], yst⟩ mid → mid.stk.length ≤ 1023 :=
  referenceAssembly_stack_bound yst

/-- info: 'Challenge.Bls12381G2Add.Reference.Proofs.Compilation.referenceCheckedCert_valid' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms referenceCheckedCert_valid

/-- info: 'Challenge.Bls12381G2Add.Reference.Proofs.Compilation.referenceCheckedCert_bounded' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms referenceCheckedCert_bounded

/-- info: 'Challenge.Bls12381G2Add.Reference.Proofs.Compilation.referenceLengthLookup_entry' depends on axioms: [propext] -/
#guard_msgs in
#print axioms referenceLengthLookup_entry

/-- info: 'Challenge.Bls12381G2Add.Reference.Proofs.Compilation.referenceAssembly_stack_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms referenceAssembly_stack_bound
