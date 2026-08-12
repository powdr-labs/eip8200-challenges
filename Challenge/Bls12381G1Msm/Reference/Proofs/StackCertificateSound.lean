import Challenge.Bls12381G1Msm.Reference.Proofs.StackCertificateChunks

set_option warningAsError true

/-!
# Soundness bridge for the compact G1MSM stack certificate

The finite checker uses layouts keyed only by program-suffix length.  The
proof-facing certificate additionally rejects non-suffix lists, so its domain
is exactly the positions reachable by the assembly semantics.
-/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.Compilation

open YulEvmCompiler

def referenceSuffixLookup : CertLookup := fun c =>
  if c <:+ referenceOptimizedAssembly then referenceLengthLookup c else none

def referenceCheckedCert : Cert := referenceSuffixLookup.toCert

theorem referenceSuffixLookup_eq {c : List Asm}
    (h : c <:+ referenceOptimizedAssembly) :
    referenceSuffixLookup c = referenceLengthLookup c := by
  simp [referenceSuffixLookup, h]

private theorem referenceCheckedCert_eq {c : List Asm}
    (h : c <:+ referenceOptimizedAssembly) :
    referenceCheckedCert.fl c = referenceLengthLookup.toCert.fl c ∧
      referenceCheckedCert.fbMax c = referenceLengthLookup.toCert.fbMax c ∧
      referenceCheckedCert.rl c = referenceLengthLookup.toCert.rl c := by
  simp [referenceCheckedCert, CertLookup.toCert, referenceSuffixLookup_eq h]

private theorem tail_suffix {i : Asm} {c : List Asm}
    (h : i :: c <:+ referenceOptimizedAssembly) :
    c <:+ referenceOptimizedAssembly :=
  IsTrans.trans c (i :: c) referenceOptimizedAssembly
    (List.suffix_cons i c) h

theorem frameStep_checked_iff_length {i : Asm} {c : List Asm}
    {S : FLayout} {F : Nat} {R : FLayout}
    (hpos : i :: c <:+ referenceOptimizedAssembly) :
    frameStep referenceOptimizedAssembly referenceCheckedCert i c S F R ↔
      frameStep referenceOptimizedAssembly referenceLengthLookup.toCert
        i c S F R := by
  have hc := tail_suffix hpos
  rcases referenceCheckedCert_eq hc with ⟨hflc, hfbc, hrlc⟩
  cases i with
  | push | op | dup | swap | pop | label | pushLabel =>
      simp only [frameStep]
      rw [hflc, hfbc, hrlc]
  | dynJump => rfl
  | jump l =>
      simp only [frameStep]
      constructor
      · intro h
        rcases h with hlocal | hcall
        · rcases hlocal with ⟨t, hfind, hfl, hfb, hrl⟩
          have ht := findLabel_suffix hfind
          rcases referenceCheckedCert_eq ht with ⟨hflt, hfbt, hrlt⟩
          exact Or.inl ⟨t, hfind, hflt ▸ hfl, hfbt ▸ hfb, hrlt ▸ hrl⟩
        · rcases hcall with
            ⟨Sw, Smid, Lret, c', t, Sret, hfind, rfl, hS, hwords,
              hflt, hfbt, hrlt, hretwords, hfindRet, hflc', hfbc', hrlc'⟩
          have ht := findLabel_suffix hfind
          have hc' := findLabel_suffix hfindRet
          rcases referenceCheckedCert_eq ht with ⟨hflt', hfbt', hrlt'⟩
          rcases referenceCheckedCert_eq hc' with ⟨hflr, hfbr, hrlr⟩
          exact Or.inr ⟨Sw, Smid, Lret, c', t, Sret, hfind, rfl, hS,
            hwords, hflt' ▸ hflt, hfbt' ▸ hfbt, hrlt' ▸ hrlt, hretwords,
            hfindRet, hflr ▸ hflc', hfbr ▸ hfbc', hrlr ▸ hrlc'⟩
      · intro h
        rcases h with hlocal | hcall
        · rcases hlocal with ⟨t, hfind, hfl, hfb, hrl⟩
          have ht := findLabel_suffix hfind
          rcases referenceCheckedCert_eq ht with ⟨hflt, hfbt, hrlt⟩
          exact Or.inl ⟨t, hfind, hflt.symm ▸ hfl, hfbt.symm ▸ hfb,
            hrlt.symm ▸ hrl⟩
        · rcases hcall with
            ⟨Sw, Smid, Lret, c', t, Sret, hfind, rfl, hS, hwords,
              hflt, hfbt, hrlt, hretwords, hfindRet, hflc', hfbc', hrlc'⟩
          have ht := findLabel_suffix hfind
          have hc' := findLabel_suffix hfindRet
          rcases referenceCheckedCert_eq ht with ⟨hflt', hfbt', hrlt'⟩
          rcases referenceCheckedCert_eq hc' with ⟨hflr, hfbr, hrlr⟩
          exact Or.inr ⟨Sw, Smid, Lret, c', t, Sret, hfind, rfl, hS,
            hwords, hflt'.symm ▸ hflt, hfbt'.symm ▸ hfbt,
            hrlt'.symm ▸ hrlt, hretwords, hfindRet, hflr.symm ▸ hflc',
            hfbr.symm ▸ hfbc', hrlr.symm ▸ hrlc'⟩
  | jumpi l =>
      simp only [frameStep]
      constructor
      · rintro ⟨S', hS, ⟨t, hfind, hflt, hfbt, hrlt⟩, hfl, hfb, hrl⟩
        have ht := findLabel_suffix hfind
        rcases referenceCheckedCert_eq ht with ⟨hflt', hfbt', hrlt'⟩
        exact ⟨S', hS, ⟨t, hfind, hflt' ▸ hflt, hfbt' ▸ hfbt,
          hrlt' ▸ hrlt⟩, hflc ▸ hfl, hfbc ▸ hfb, hrlc ▸ hrl⟩
      · rintro ⟨S', hS, ⟨t, hfind, hflt, hfbt, hrlt⟩, hfl, hfb, hrl⟩
        have ht := findLabel_suffix hfind
        rcases referenceCheckedCert_eq ht with ⟨hflt', hfbt', hrlt'⟩
        exact ⟨S', hS, ⟨t, hfind, hflt'.symm ▸ hflt,
          hfbt'.symm ▸ hfbt, hrlt'.symm ▸ hrlt⟩, hflc.symm ▸ hfl,
          hfbc.symm ▸ hfb, hrlc.symm ▸ hrl⟩

private def certEntryOfFrozen (e : FrozenStackEntry) : CertEntry :=
  let t := thawStackEntry e
  (t.1,
    referenceOptimizedAssembly.drop
      (referenceOptimizedAssembly.length - t.1),
    t.2.1, t.2.2.1, t.2.2.2)

private theorem referenceEntries_eq :
    referenceStackCertificate.entries =
      frozenStackEntries.map certEntryOfFrozen := by
  simp [referenceStackCertificate, materializeStackCertificate,
    certEntryOfFrozen, List.map_map, Function.comp_def]

private theorem lengthLookup_some {c : List Asm} {v : CertValue}
    (h : referenceLengthLookup c = some v) :
    ∃ e ∈ frozenStackEntries,
      e.1 = c.length ∧ thawCertValue (e.2.1, e.2.2.1, e.2.2.2) = v := by
  unfold referenceLengthLookup frozenLayoutAt at h
  rcases hfind : frozenStackEntries.find? (fun e => e.1 == c.length) with _ | e
  · simp [hfind] at h
  · have hmem := List.mem_of_find?_eq_some hfind
    have hkey := List.find?_some hfind
    simp only [beq_iff_eq] at hkey
    simp only [hfind, Option.map_some] at h
    exact ⟨e, hmem, hkey, Option.some.inj h⟩

theorem referenceCheckedCert_valid :
    referenceCheckedCert.Valid referenceOptimizedAssembly := by
  intro i c S F R hfl hfb hrl
  have hpos : i :: c <:+ referenceOptimizedAssembly := by
    change Option.map (fun v => v.1) (referenceSuffixLookup (i :: c)) =
      some S at hfl
    unfold referenceSuffixLookup at hfl
    split at hfl
    · assumption
    · simp at hfl
  have heq := referenceCheckedCert_eq hpos
  have hlength : referenceLengthLookup (i :: c) = some (S, F, R) := by
    apply (CertLookup.eq_some_iff_fields referenceLengthLookup _ _ _ _).mpr
    exact ⟨heq.1 ▸ hfl, heq.2.1 ▸ hfb, heq.2.2 ▸ hrl⟩
  obtain ⟨e, hmem, hkey, hvalue⟩ := lengthLookup_some hlength
  have hcanon : referenceOptimizedAssembly.drop
      (referenceOptimizedAssembly.length - e.1) = i :: c := by
    rw [hkey]
    exact (List.suffix_iff_eq_drop.mp hpos).symm
  have hentryMem : certEntryOfFrozen e ∈ referenceStackCertificate.entries := by
    rw [referenceEntries_eq]
    exact List.mem_map.mpr ⟨e, hmem, rfl⟩
  have hchecked := (List.all_eq_true.mp referenceStackLengthEntryChecks)
    (certEntryOfFrozen e) hentryMem
  simp only [Bool.and_eq_true] at hchecked
  have hstep := hchecked.2
  dsimp [certEntryOfFrozen, thawStackEntry] at hstep hvalue
  rw [hcanon] at hstep
  change frameStepLookupB referenceOptimizedAssembly referenceLengthLookup
    i c (e.2.1.map decodeStackSlot) e.2.2.1
      (e.2.2.2.map decodeStackSlot) = true at hstep
  rw [frameStepLookupB_eq_frameStepB] at hstep
  have hsemantic := frameStepB_sound hstep
  dsimp [thawCertValue] at hvalue
  rcases Prod.mk.inj hvalue with ⟨hS, hFR⟩
  rcases Prod.mk.inj hFR with ⟨hF, hR⟩
  subst S
  subst F
  subst R
  exact (frameStep_checked_iff_length hpos).mpr hsemantic

theorem referenceCheckedCert_bounded : referenceCheckedCert.Bounded := by
  intro c S F hfl hfb
  have hpos : c <:+ referenceOptimizedAssembly := by
    change Option.map (fun v => v.1) (referenceSuffixLookup c) = some S at hfl
    unfold referenceSuffixLookup at hfl
    split at hfl
    · assumption
    · simp at hfl
  have heq := referenceCheckedCert_eq hpos
  have hfl' := heq.1 ▸ hfl
  have hfb' := heq.2.1 ▸ hfb
  change Option.map (fun v => v.1) (referenceLengthLookup c) = some S at hfl'
  change Option.map (fun v => v.2.1) (referenceLengthLookup c) = some F at hfb'
  rcases hlookup : referenceLengthLookup c with _ | v
  · simp [hlookup] at hfl'
  · rcases v with ⟨S', F', R'⟩
    simp only [hlookup, Option.map_some, Option.some.injEq] at hfl' hfb'
    subst S'
    subst F'
    obtain ⟨e, hmem, -, hvalue⟩ := lengthLookup_some hlookup
    have hentryMem : certEntryOfFrozen e ∈
        referenceStackCertificate.entries := by
      rw [referenceEntries_eq]
      exact List.mem_map.mpr ⟨e, hmem, rfl⟩
    have hchecked := (List.all_eq_true.mp referenceStackLengthEntryChecks)
      (certEntryOfFrozen e) hentryMem
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hchecked
    dsimp [certEntryOfFrozen, thawStackEntry, thawCertValue] at hchecked hvalue
    rcases Prod.mk.inj hvalue with ⟨hS, hFR⟩
    rcases Prod.mk.inj hFR with ⟨hF, -⟩
    rw [hS, hF] at hchecked
    exact hchecked.1

set_option maxRecDepth 10000 in
theorem referenceLengthLookup_entry :
    referenceLengthLookup referenceOptimizedAssembly = some ([], 0, []) := by
  with_unfolding_all decide

theorem referenceCheckedCert_entry :
    referenceCheckedCert.fl referenceOptimizedAssembly = some [] ∧
      referenceCheckedCert.fbMax referenceOptimizedAssembly = some 0 ∧
      referenceCheckedCert.rl referenceOptimizedAssembly = some [] := by
  simp [referenceCheckedCert, CertLookup.toCert,
    referenceSuffixLookup_eq (List.suffix_refl referenceOptimizedAssembly),
    referenceLengthLookup_entry]

variable [model : ExternalModel]

theorem referenceAssembly_stack_bound (yst : YulSemantics.EVM.EvmState) :
    ∀ mid, ASteps (model := model) referenceOptimizedAssembly
      ⟨referenceOptimizedAssembly, [], yst⟩ mid → mid.stk.length ≤ 1023 := by
  rcases referenceCheckedCert_entry with ⟨hfl, hfb, hrl⟩
  exact run_stack_bound2 referenceCheckedCert_valid
    referenceCheckedCert_bounded hfl hfb hrl yst

end Challenge.Bls12381G1Msm.Reference.Proofs.Compilation
