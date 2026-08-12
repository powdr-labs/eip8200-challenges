import Challenge.Bls12381G2Add.Reference.Proofs.StackCertificateCore

set_option warningAsError true

namespace Challenge.Bls12381G2Add.Reference.Proofs.Compilation

private def entries := frozenStackEntries
private def chunkEntries10 := (entries.drop 1000).take 100
private def chunkEntries11 := (entries.drop 1100).take 100
private def chunkEntries12 := (entries.drop 1200).take 100
private def chunkEntries13 := (entries.drop 1300).take 100
private def chunkEntries14 := (entries.drop 1400).take 100

prove_frozen_entry_chunk stackFrozenEntryChecks_chunk10 :
    stackFrozenEntryChecks ((entries.drop 1000).take 100) = true
  using chunkEntries10 with stackFrozenEntryChecks
  at referenceOptimizedAssembly via referenceLengthLookup

prove_frozen_entry_chunk stackFrozenEntryChecks_chunk11 :
    stackFrozenEntryChecks ((entries.drop 1100).take 100) = true
  using chunkEntries11 with stackFrozenEntryChecks
  at referenceOptimizedAssembly via referenceLengthLookup

prove_frozen_entry_chunk stackFrozenEntryChecks_chunk12 :
    stackFrozenEntryChecks ((entries.drop 1200).take 100) = true
  using chunkEntries12 with stackFrozenEntryChecks
  at referenceOptimizedAssembly via referenceLengthLookup

prove_frozen_entry_chunk stackFrozenEntryChecks_chunk13 :
    stackFrozenEntryChecks ((entries.drop 1300).take 100) = true
  using chunkEntries13 with stackFrozenEntryChecks
  at referenceOptimizedAssembly via referenceLengthLookup

prove_frozen_entry_chunk stackFrozenEntryChecks_chunk14 :
    stackFrozenEntryChecks ((entries.drop 1400).take 100) = true
  using chunkEntries14 with stackFrozenEntryChecks
  at referenceOptimizedAssembly via referenceLengthLookup

end Challenge.Bls12381G2Add.Reference.Proofs.Compilation
