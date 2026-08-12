import Challenge.Bls12381G2Add.Reference.Proofs.StackCertificateChunk0
import Challenge.Bls12381G2Add.Reference.Proofs.StackCertificateChunk5
import Challenge.Bls12381G2Add.Reference.Proofs.StackCertificateChunk10

set_option warningAsError true

namespace Challenge.Bls12381G2Add.Reference.Proofs.Compilation

set_option maxRecDepth 10000 in
theorem referenceStackFrozenEntryChecks :
    stackFrozenEntryChecks frozenStackEntries = true := by
  have h15 : stackFrozenEntryChecks
      (frozenStackEntries.drop 1500) = true := by
    rfl
  have h14 := stackFrozenEntryChecks_take_drop
    (frozenStackEntries.drop 1400) 100
    stackFrozenEntryChecks_chunk14 (by simpa [List.drop_drop] using h15)
  have h13 := stackFrozenEntryChecks_take_drop
    (frozenStackEntries.drop 1300) 100
    stackFrozenEntryChecks_chunk13 (by simpa [List.drop_drop] using h14)
  have h12 := stackFrozenEntryChecks_take_drop
    (frozenStackEntries.drop 1200) 100
    stackFrozenEntryChecks_chunk12 (by simpa [List.drop_drop] using h13)
  have h11 := stackFrozenEntryChecks_take_drop
    (frozenStackEntries.drop 1100) 100
    stackFrozenEntryChecks_chunk11 (by simpa [List.drop_drop] using h12)
  have h10 := stackFrozenEntryChecks_take_drop
    (frozenStackEntries.drop 1000) 100
    stackFrozenEntryChecks_chunk10 (by simpa [List.drop_drop] using h11)
  have h9 := stackFrozenEntryChecks_take_drop
    (frozenStackEntries.drop 900) 100
    stackFrozenEntryChecks_chunk9 (by simpa [List.drop_drop] using h10)
  have h8 := stackFrozenEntryChecks_take_drop
    (frozenStackEntries.drop 800) 100
    stackFrozenEntryChecks_chunk8 (by simpa [List.drop_drop] using h9)
  have h7 := stackFrozenEntryChecks_take_drop
    (frozenStackEntries.drop 700) 100
    stackFrozenEntryChecks_chunk7 (by simpa [List.drop_drop] using h8)
  have h6 := stackFrozenEntryChecks_take_drop
    (frozenStackEntries.drop 600) 100
    stackFrozenEntryChecks_chunk6 (by simpa [List.drop_drop] using h7)
  have h5 := stackFrozenEntryChecks_take_drop
    (frozenStackEntries.drop 500) 100
    stackFrozenEntryChecks_chunk5 (by simpa [List.drop_drop] using h6)
  have h4 := stackFrozenEntryChecks_take_drop
    (frozenStackEntries.drop 400) 100
    stackFrozenEntryChecks_chunk4 (by simpa [List.drop_drop] using h5)
  have h3 := stackFrozenEntryChecks_take_drop
    (frozenStackEntries.drop 300) 100
    stackFrozenEntryChecks_chunk3 (by simpa [List.drop_drop] using h4)
  have h2 := stackFrozenEntryChecks_take_drop
    (frozenStackEntries.drop 200) 100
    stackFrozenEntryChecks_chunk2 (by simpa [List.drop_drop] using h3)
  have h1 := stackFrozenEntryChecks_take_drop
    (frozenStackEntries.drop 100) 100
    stackFrozenEntryChecks_chunk1 (by simpa [List.drop_drop] using h2)
  exact stackFrozenEntryChecks_take_drop
    frozenStackEntries 100
    stackFrozenEntryChecks_chunk0 (by simpa [List.drop_drop] using h1)

/-! The public soundness bridge belongs at the aggregate certificate boundary:
the individual chunk modules remain data/decision memory firebreaks. -/

open YulEvmCompiler

abbrev referenceSuffixLookup : CertLookup :=
  Challenge.EvmProof.StackCertificate.suffixLookup
    referenceOptimizedAssembly frozenStackEntries

abbrev referenceCheckedCert : Cert :=
  Challenge.EvmProof.StackCertificate.checkedCert
    referenceOptimizedAssembly frozenStackEntries

theorem referenceSuffixLookup_eq {suffix : List Asm}
    (h : suffix <:+ referenceOptimizedAssembly) :
    referenceSuffixLookup suffix = referenceLengthLookup suffix :=
  Challenge.EvmProof.StackCertificate.suffixLookup_eq h

theorem frameStep_checked_iff_length {instruction : Asm}
    {suffix : List Asm} {stack : FLayout} {frameBase : Nat}
    {returns : FLayout}
    (hpos : instruction :: suffix <:+ referenceOptimizedAssembly) :
    frameStep referenceOptimizedAssembly referenceCheckedCert instruction
        suffix stack frameBase returns ↔
      frameStep referenceOptimizedAssembly referenceLengthLookup.toCert
        instruction suffix stack frameBase returns :=
  Challenge.EvmProof.StackCertificate.frameStep_checked_iff_length hpos

private theorem sharedChecks :
    Challenge.EvmProof.StackCertificate.lengthEntryChecks
      referenceOptimizedAssembly
      (Challenge.EvmProof.StackCertificate.lengthLookup frozenStackEntries)
      (Challenge.EvmProof.StackCertificate.certificateData
        referenceOptimizedAssembly frozenStackEntries).entries = true := by
  rw [← Challenge.EvmProof.StackCertificate.frozenEntryChecks_eq_lengthEntryChecks]
  exact referenceStackFrozenEntryChecks

theorem referenceCheckedCert_valid :
    referenceCheckedCert.Valid referenceOptimizedAssembly :=
  Challenge.EvmProof.StackCertificate.checkedCert_valid
    referenceOptimizedAssembly frozenStackEntries sharedChecks

theorem referenceCheckedCert_bounded : referenceCheckedCert.Bounded :=
  Challenge.EvmProof.StackCertificate.checkedCert_bounded
    referenceOptimizedAssembly frozenStackEntries sharedChecks

set_option maxRecDepth 10000 in
theorem referenceLengthLookup_entry :
    referenceLengthLookup referenceOptimizedAssembly = some ([], 0, []) := by
  with_unfolding_all decide

theorem referenceCheckedCert_entry :
    referenceCheckedCert.fl referenceOptimizedAssembly = some [] ∧
      referenceCheckedCert.fbMax referenceOptimizedAssembly = some 0 ∧
      referenceCheckedCert.rl referenceOptimizedAssembly = some [] :=
  Challenge.EvmProof.StackCertificate.checkedCert_entry
    referenceLengthLookup_entry

variable [model : ExternalModel]

theorem referenceAssembly_stack_bound (state : YulSemantics.EVM.EvmState) :
    ∀ mid, ASteps (model := model) referenceOptimizedAssembly
      ⟨referenceOptimizedAssembly, [], state⟩ mid → mid.stk.length ≤ 1023 :=
  Challenge.EvmProof.StackCertificate.assembly_stack_bound
    referenceOptimizedAssembly frozenStackEntries sharedChecks
      referenceLengthLookup_entry state

end Challenge.Bls12381G2Add.Reference.Proofs.Compilation
