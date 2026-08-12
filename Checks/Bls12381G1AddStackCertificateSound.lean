import Challenge.Bls12381G1Add.Reference.Proofs.StackCertificateChunks

set_option warningAsError true

open Challenge.Bls12381G1Add.Reference.Proofs.Compilation

example {i c S F R} (h : i :: c <:+ referenceOptimizedAssembly) :
    YulEvmCompiler.frameStep referenceOptimizedAssembly referenceCheckedCert
      i c S F R ↔
      YulEvmCompiler.frameStep referenceOptimizedAssembly
        referenceLengthLookup.toCert i c S F R :=
  frameStep_checked_iff_length h

example : referenceCheckedCert.Valid referenceOptimizedAssembly :=
  referenceCheckedCert_valid

example : referenceCheckedCert.Bounded := referenceCheckedCert_bounded

example : referenceCheckedCert.fl referenceOptimizedAssembly = some [] :=
  referenceCheckedCert_entry.1

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.Compilation.frameStep_checked_iff_length' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms frameStep_checked_iff_length

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.Compilation.referenceCheckedCert_valid' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms referenceCheckedCert_valid

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.Compilation.referenceCheckedCert_bounded' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms referenceCheckedCert_bounded

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.Compilation.referenceLengthLookup_entry' depends on axioms: [propext] -/
#guard_msgs in
#print axioms referenceLengthLookup_entry

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.Compilation.referenceCheckedCert_entry' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms referenceCheckedCert_entry

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.Compilation.referenceAssembly_stack_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms referenceAssembly_stack_bound
