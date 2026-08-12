import Challenge.Bls12381G1Add.Reference.Proofs.StackCertificateChunks

set_option warningAsError true

open Challenge.Bls12381G1Add.Reference.Proofs.Compilation

example : stackFrozenEntryChecks frozenStackEntries = true :=
  referenceStackFrozenEntryChecks

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.Compilation.referenceStackFrozenEntryChecks' depends on axioms: [propext] -/
#guard_msgs in
#print axioms referenceStackFrozenEntryChecks
