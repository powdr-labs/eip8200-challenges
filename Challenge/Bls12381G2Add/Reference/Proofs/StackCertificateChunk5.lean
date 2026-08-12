import Challenge.Bls12381G2Add.Reference.Proofs.StackCertificateCore

set_option warningAsError true

namespace Challenge.Bls12381G2Add.Reference.Proofs.Compilation

private def entries := frozenStackEntries
private def chunkEntries5 := (entries.drop 500).take 100
private def chunkEntries6 := (entries.drop 600).take 100
private def chunkEntries7 := (entries.drop 700).take 100
private def chunkEntries8 := (entries.drop 800).take 100
private def chunkEntries9 := (entries.drop 900).take 100

prove_frozen_entry_chunk stackFrozenEntryChecks_chunk5 :
    stackFrozenEntryChecks ((entries.drop 500).take 100) = true
  using chunkEntries5 with stackFrozenEntryChecks
  at referenceOptimizedAssembly via referenceLengthLookup

prove_frozen_entry_chunk stackFrozenEntryChecks_chunk6 :
    stackFrozenEntryChecks ((entries.drop 600).take 100) = true
  using chunkEntries6 with stackFrozenEntryChecks
  at referenceOptimizedAssembly via referenceLengthLookup

prove_frozen_entry_chunk stackFrozenEntryChecks_chunk7 :
    stackFrozenEntryChecks ((entries.drop 700).take 100) = true
  using chunkEntries7 with stackFrozenEntryChecks
  at referenceOptimizedAssembly via referenceLengthLookup

prove_frozen_entry_chunk stackFrozenEntryChecks_chunk8 :
    stackFrozenEntryChecks ((entries.drop 800).take 100) = true
  using chunkEntries8 with stackFrozenEntryChecks
  at referenceOptimizedAssembly via referenceLengthLookup

prove_frozen_entry_chunk stackFrozenEntryChecks_chunk9 :
    stackFrozenEntryChecks ((entries.drop 900).take 100) = true
  using chunkEntries9 with stackFrozenEntryChecks
  at referenceOptimizedAssembly via referenceLengthLookup

end Challenge.Bls12381G2Add.Reference.Proofs.Compilation
