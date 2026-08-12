import Challenge.Bls12381G1Add.Reference.Proofs.StackCertificateCore

set_option warningAsError true

namespace Challenge.Bls12381G1Add.Reference.Proofs.Compilation

private def entries := frozenStackEntries
private def chunkEntries0 := (entries.drop 0).take 100
private def chunkEntries1 := (entries.drop 100).take 100
private def chunkEntries2 := (entries.drop 200).take 100
private def chunkEntries3 := (entries.drop 300).take 100
private def chunkEntries4 := (entries.drop 400).take 100

prove_frozen_entry_chunk stackFrozenEntryChecks_chunk0 :
    stackFrozenEntryChecks (entries.take 100) = true
  using chunkEntries0 with stackFrozenEntryChecks
  at referenceOptimizedAssembly via referenceLengthLookup

prove_frozen_entry_chunk stackFrozenEntryChecks_chunk1 :
    stackFrozenEntryChecks ((entries.drop 100).take 100) = true
  using chunkEntries1 with stackFrozenEntryChecks
  at referenceOptimizedAssembly via referenceLengthLookup

prove_frozen_entry_chunk stackFrozenEntryChecks_chunk2 :
    stackFrozenEntryChecks ((entries.drop 200).take 100) = true
  using chunkEntries2 with stackFrozenEntryChecks
  at referenceOptimizedAssembly via referenceLengthLookup

prove_frozen_entry_chunk stackFrozenEntryChecks_chunk3 :
    stackFrozenEntryChecks ((entries.drop 300).take 100) = true
  using chunkEntries3 with stackFrozenEntryChecks
  at referenceOptimizedAssembly via referenceLengthLookup

prove_frozen_entry_chunk stackFrozenEntryChecks_chunk4 :
    stackFrozenEntryChecks ((entries.drop 400).take 100) = true
  using chunkEntries4 with stackFrozenEntryChecks
  at referenceOptimizedAssembly via referenceLengthLookup

end Challenge.Bls12381G1Add.Reference.Proofs.Compilation
