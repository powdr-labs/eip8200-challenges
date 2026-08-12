import Challenge.Bls12381G1Add.Reference.Proofs.StackCertificateChunk0

set_option warningAsError true

open Challenge.Bls12381G1Add.Reference.Proofs.Compilation

example : stackFrozenEntryChecks (frozenStackEntries.take 100) = true :=
  stackFrozenEntryChecks_chunk0
