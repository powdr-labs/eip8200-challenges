import Challenge.Bls12381G1Msm.Reference.Proofs.FrozenStackCertificate

set_option warningAsError true

/-!
# Chunked G1MSM stack-certificate checking

The verified checker is pure, but reducing all 1,721 finite entries in one
declaration builds an unnecessarily large proof term.  These definitions make
the two `List.all` passes explicit so separately compiled chunk proofs can be
combined without weakening the checker.
-/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.Compilation

open YulEvmCompiler

def stackKeyChecks (entries : List CertEntry) : Bool :=
  entries.all fun e => decide (e.1 ≤ referenceOptimizedAssembly.length)

def stackInitialCheck : Bool :=
  let C := referenceStackCertificate.toCert
  (C.fl referenceOptimizedAssembly == some []) &&
    (C.fbMax referenceOptimizedAssembly == some 0) &&
    (C.rl referenceOptimizedAssembly).isSome

def stackEntryChecks (entries : List CertEntry) : Bool :=
  let C := referenceStackCertificate.toCert
  entries.all fun e =>
    decide (e.2.2.1.length + e.2.2.2.1 ≤ 1023) &&
      match e.2.1 with
      | i :: c' => frameStepB referenceOptimizedAssembly C i c'
          e.2.2.1 e.2.2.2.1 e.2.2.2.2
      | [] => true

/-- Equivalent bundled-lookup form used for finite checking.  It avoids three
independent linear certificate scans per successor while retaining the exact
proof-facing `checkCert` semantics. -/
def stackIndexedEntryChecks (entries : List CertEntry) : Bool :=
  let lookup := referenceStackCertificate.toLookup
  entries.all fun e =>
    decide (e.2.2.1.length + e.2.2.2.1 ≤ 1023) &&
      match e.2.1 with
      | i :: c' => frameStepLookupB referenceOptimizedAssembly lookup i c'
          e.2.2.1 e.2.2.2.1 e.2.2.2.2
      | [] => true

abbrev FrozenCertValue := List Nat × Nat × List Nat

def thawCertValue (v : FrozenCertValue) : CertValue :=
  (v.1.map decodeStackSlot, v.2.1, v.2.2.map decodeStackSlot)

/-- Compact lookup used by the kernel checker.  It searches only numeric keys
and compact layouts, avoiding reconstruction of the certificate's array of
full assembly suffixes. -/
def frozenLayoutAt (k : Nat) : Option CertValue :=
  (frozenStackEntries.find? fun e => e.1 == k).map fun e =>
    thawCertValue (e.2.1, e.2.2.1, e.2.2.2)

def referenceLengthLookup : CertLookup := fun c => frozenLayoutAt c.length

def stackLengthEntryChecks (entries : List CertEntry) : Bool :=
  entries.all fun e =>
    decide (e.2.2.1.length + e.2.2.2.1 ≤ 1023) &&
      match e.2.1 with
      | i :: c' => frameStepLookupB referenceOptimizedAssembly
          referenceLengthLookup i c' e.2.2.1 e.2.2.2.1 e.2.2.2.2
      | [] => true

theorem stackIndexedEntryChecks_eq (entries : List CertEntry) :
    stackIndexedEntryChecks entries = stackEntryChecks entries := by
  unfold stackIndexedEntryChecks stackEntryChecks CertData.toCert
  apply List.all_congr rfl
  intro e
  apply congrArg (fun b => decide (e.2.2.1.length + e.2.2.2.1 ≤ 1023) && b)
  cases e.2.1 with
  | nil => rfl
  | cons i c =>
    exact frameStepLookupB_eq_frameStepB
      referenceOptimizedAssembly referenceStackCertificate.toLookup
      i c e.2.2.1 e.2.2.2.1 e.2.2.2.2

theorem checkCert_eq_chunkChecks :
    checkCert referenceOptimizedAssembly referenceStackCertificate =
      (stackKeyChecks referenceStackCertificate.entries &&
        (stackInitialCheck &&
          stackEntryChecks referenceStackCertificate.entries)) := rfl

theorem all_take_drop {α : Type} (f : α → Bool) (xs : List α) (n : Nat)
    (hhead : (xs.take n).all f = true)
    (htail : (xs.drop n).all f = true) : xs.all f = true := by
  rw [← List.take_append_drop n xs, List.all_append, hhead, htail]
  rfl

theorem stackLengthEntryChecks_take_drop (entries : List CertEntry) (n : Nat)
    (hhead : stackLengthEntryChecks (entries.take n) = true)
    (htail : stackLengthEntryChecks (entries.drop n) = true) :
    stackLengthEntryChecks entries = true := by
  unfold stackLengthEntryChecks at hhead htail ⊢
  exact all_take_drop _ _ _ hhead htail

end Challenge.Bls12381G1Msm.Reference.Proofs.Compilation
