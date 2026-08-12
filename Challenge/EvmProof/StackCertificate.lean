import YulEvmCompiler.StackScalable

set_option warningAsError true

/-!
# Compact stack-certificate checking

Challenge-independent finite checker and chunk-composition support for frozen
Yul-to-EVM stack-layout certificates. Programs and untrusted certificate data
remain challenge-local; this module owns only their common representation and
verified checking logic.
-/

namespace Challenge.EvmProof.StackCertificate

open YulEvmCompiler

abbrev CompactStackEntry := Nat × FLayout × Nat × FLayout

def encodeStackSlot : FSlot → Nat
  | .word => 0
  | .ret => 1
  | .retTo label => label + 2

def decodeStackSlot : Nat → FSlot
  | 0 => .word
  | 1 => .ret
  | n + 2 => .retTo n

abbrev FrozenStackEntry := Nat × List Nat × Nat × List Nat

def thawStackEntry (entry : FrozenStackEntry) : CompactStackEntry :=
  (entry.1, entry.2.1.map decodeStackSlot, entry.2.2.1,
    entry.2.2.2.map decodeStackSlot)

def materializeStackCertificate (program : List Asm)
    (entries : List CompactStackEntry) : CertData where
  entries := entries.map fun entry =>
    (entry.1, program.drop (program.length - entry.1),
      entry.2.1, entry.2.2.1, entry.2.2.2)

def keyChecks (program : List Asm) (entries : List CertEntry) : Bool :=
  entries.all fun entry => decide (entry.1 ≤ program.length)

def initialCheck (program : List Asm) (certificate : CertData) : Bool :=
  let cert := certificate.toCert
  (cert.fl program == some []) &&
    (cert.fbMax program == some 0) &&
    (cert.rl program).isSome

def entryChecks (program : List Asm) (certificate : CertData)
    (entries : List CertEntry) : Bool :=
  let cert := certificate.toCert
  entries.all fun entry =>
    decide (entry.2.2.1.length + entry.2.2.2.1 ≤ 1023) &&
      match entry.2.1 with
      | instruction :: suffix => frameStepB program cert instruction suffix
          entry.2.2.1 entry.2.2.2.1 entry.2.2.2.2
      | [] => true

/-- Bundled-lookup form of `entryChecks`, avoiding repeated independent
certificate scans while retaining the proof-facing checker semantics. -/
def indexedEntryChecks (program : List Asm) (certificate : CertData)
    (entries : List CertEntry) : Bool :=
  let lookup := certificate.toLookup
  entries.all fun entry =>
    decide (entry.2.2.1.length + entry.2.2.2.1 ≤ 1023) &&
      match entry.2.1 with
      | instruction :: suffix => frameStepLookupB program lookup
          instruction suffix entry.2.2.1 entry.2.2.2.1 entry.2.2.2.2
      | [] => true

abbrev FrozenCertValue := List Nat × Nat × List Nat

def thawCertValue (value : FrozenCertValue) : CertValue :=
  (value.1.map decodeStackSlot, value.2.1,
    value.2.2.map decodeStackSlot)

/-- Numeric-key lookup over compact frozen layouts. No assembly suffix is
stored in the frozen representation. -/
def frozenLayoutAt (entries : List FrozenStackEntry) (key : Nat) :
    Option CertValue :=
  (entries.find? fun entry => entry.1 == key).map fun entry =>
    thawCertValue (entry.2.1, entry.2.2.1, entry.2.2.2)

def lengthLookup (entries : List FrozenStackEntry) : CertLookup :=
  fun suffix => frozenLayoutAt entries suffix.length

def lengthEntryChecks (program : List Asm) (lookup : CertLookup)
    (entries : List CertEntry) : Bool :=
  entries.all fun entry =>
    decide (entry.2.2.1.length + entry.2.2.2.1 ≤ 1023) &&
      match entry.2.1 with
      | instruction :: suffix => frameStepLookupB program lookup
          instruction suffix entry.2.2.1 entry.2.2.2.1 entry.2.2.2.2
      | [] => true

/-- Check frozen entries directly, materializing only the program suffix for the
entry currently being checked. In particular, callers can `drop` and `take` a
compact entry list before any suffixes are constructed. -/
def frozenEntryChecks (program : List Asm) (lookup : CertLookup)
    (entries : List FrozenStackEntry) : Bool :=
  entries.all fun entry =>
    let stack := entry.2.1.map decodeStackSlot
    let frameBase := entry.2.2.1
    let returns := entry.2.2.2.map decodeStackSlot
    decide (stack.length + frameBase ≤ 1023) &&
      match program.drop (program.length - entry.1) with
      | instruction :: suffix => frameStepLookupB program lookup
          instruction suffix stack frameBase returns
      | [] => true

theorem indexedEntryChecks_eq (program : List Asm) (certificate : CertData)
    (entries : List CertEntry) :
    indexedEntryChecks program certificate entries =
      entryChecks program certificate entries := by
  unfold indexedEntryChecks entryChecks CertData.toCert
  apply List.all_congr rfl
  intro entry
  apply congrArg (fun checked =>
    decide (entry.2.2.1.length + entry.2.2.2.1 ≤ 1023) && checked)
  cases entry.2.1 with
  | nil => rfl
  | cons instruction suffix =>
    exact frameStepLookupB_eq_frameStepB program certificate.toLookup
      instruction suffix entry.2.2.1 entry.2.2.2.1 entry.2.2.2.2

theorem checkCert_eq_chunkChecks (program : List Asm)
    (certificate : CertData) :
    checkCert program certificate =
      (keyChecks program certificate.entries &&
        (initialCheck program certificate &&
          entryChecks program certificate certificate.entries)) := rfl

theorem all_take_drop {α : Type} (f : α → Bool) (xs : List α) (n : Nat)
    (hhead : (xs.take n).all f = true)
    (htail : (xs.drop n).all f = true) : xs.all f = true := by
  rw [← List.take_append_drop n xs, List.all_append, hhead, htail]
  rfl

theorem lengthEntryChecks_take_drop (program : List Asm)
    (lookup : CertLookup) (entries : List CertEntry) (n : Nat)
    (hhead : lengthEntryChecks program lookup (entries.take n) = true)
    (htail : lengthEntryChecks program lookup (entries.drop n) = true) :
    lengthEntryChecks program lookup entries = true := by
  unfold lengthEntryChecks at hhead htail ⊢
  exact all_take_drop _ _ _ hhead htail

theorem frozenEntryChecks_take_drop (program : List Asm)
    (lookup : CertLookup) (entries : List FrozenStackEntry) (n : Nat)
    (hhead : frozenEntryChecks program lookup (entries.take n) = true)
    (htail : frozenEntryChecks program lookup (entries.drop n) = true) :
    frozenEntryChecks program lookup entries = true := by
  unfold frozenEntryChecks at hhead htail ⊢
  exact all_take_drop _ _ _ hhead htail

/-- Compose ten independently checked ten-entry blocks. Keeping the closed
blocks as separate opaque declarations bounds elaboration without requiring a
separate source file for every hundred entries. -/
theorem frozenEntryChecks_ten_parts (program : List Asm)
    (lookup : CertLookup) (entries : List FrozenStackEntry)
    (h0 : frozenEntryChecks program lookup ((entries.drop 0).take 10) = true)
    (h1 : frozenEntryChecks program lookup ((entries.drop 10).take 10) = true)
    (h2 : frozenEntryChecks program lookup ((entries.drop 20).take 10) = true)
    (h3 : frozenEntryChecks program lookup ((entries.drop 30).take 10) = true)
    (h4 : frozenEntryChecks program lookup ((entries.drop 40).take 10) = true)
    (h5 : frozenEntryChecks program lookup ((entries.drop 50).take 10) = true)
    (h6 : frozenEntryChecks program lookup ((entries.drop 60).take 10) = true)
    (h7 : frozenEntryChecks program lookup ((entries.drop 70).take 10) = true)
    (h8 : frozenEntryChecks program lookup ((entries.drop 80).take 10) = true)
    (h9 : frozenEntryChecks program lookup (entries.drop 90) = true) :
    frozenEntryChecks program lookup entries = true := by
  have h80 := frozenEntryChecks_take_drop program lookup
    (entries.drop 80) 10 h8 (by simpa [List.drop_drop] using h9)
  have h70 := frozenEntryChecks_take_drop program lookup
    (entries.drop 70) 10 h7 (by simpa [List.drop_drop] using h80)
  have h60 := frozenEntryChecks_take_drop program lookup
    (entries.drop 60) 10 h6 (by simpa [List.drop_drop] using h70)
  have h50 := frozenEntryChecks_take_drop program lookup
    (entries.drop 50) 10 h5 (by simpa [List.drop_drop] using h60)
  have h40 := frozenEntryChecks_take_drop program lookup
    (entries.drop 40) 10 h4 (by simpa [List.drop_drop] using h50)
  have h30 := frozenEntryChecks_take_drop program lookup
    (entries.drop 30) 10 h3 (by simpa [List.drop_drop] using h40)
  have h20 := frozenEntryChecks_take_drop program lookup
    (entries.drop 20) 10 h2 (by simpa [List.drop_drop] using h30)
  have h10 := frozenEntryChecks_take_drop program lookup
    (entries.drop 10) 10 h1 (by simpa [List.drop_drop] using h20)
  exact frozenEntryChecks_take_drop program lookup entries 10 h0
    (by simpa [List.drop_drop] using h10)

/-- Generate ten opaque ten-entry decision theorems and their public
100-entry composition theorem. The terms are parameters so challenge modules
retain precise control over the program, lookup, checker, and public statement. -/
syntax "prove_frozen_entry_chunk " ident " : " term " using " term
  " with " term " at " term " via " term : command

macro_rules
  | `(prove_frozen_entry_chunk $theoremName:ident : $goal:term
        using $entries:term with $checker:term at $program:term via $lookup:term) =>
    `(section
      set_option maxRecDepth 50000 in
      set_option maxHeartbeats 1000000 in
      private theorem frozenPart0 :
          $checker ((($entries).drop 0).take 10) = true := by
        with_unfolding_all decide
      set_option maxRecDepth 50000 in
      set_option maxHeartbeats 1000000 in
      private theorem frozenPart1 :
          $checker ((($entries).drop 10).take 10) = true := by
        with_unfolding_all decide
      set_option maxRecDepth 50000 in
      set_option maxHeartbeats 1000000 in
      private theorem frozenPart2 :
          $checker ((($entries).drop 20).take 10) = true := by
        with_unfolding_all decide
      set_option maxRecDepth 50000 in
      set_option maxHeartbeats 1000000 in
      private theorem frozenPart3 :
          $checker ((($entries).drop 30).take 10) = true := by
        with_unfolding_all decide
      set_option maxRecDepth 50000 in
      set_option maxHeartbeats 1000000 in
      private theorem frozenPart4 :
          $checker ((($entries).drop 40).take 10) = true := by
        with_unfolding_all decide
      set_option maxRecDepth 50000 in
      set_option maxHeartbeats 1000000 in
      private theorem frozenPart5 :
          $checker ((($entries).drop 50).take 10) = true := by
        with_unfolding_all decide
      set_option maxRecDepth 50000 in
      set_option maxHeartbeats 1000000 in
      private theorem frozenPart6 :
          $checker ((($entries).drop 60).take 10) = true := by
        with_unfolding_all decide
      set_option maxRecDepth 50000 in
      set_option maxHeartbeats 1000000 in
      private theorem frozenPart7 :
          $checker ((($entries).drop 70).take 10) = true := by
        with_unfolding_all decide
      set_option maxRecDepth 50000 in
      set_option maxHeartbeats 1000000 in
      private theorem frozenPart8 :
          $checker ((($entries).drop 80).take 10) = true := by
        with_unfolding_all decide
      set_option maxRecDepth 50000 in
      set_option maxHeartbeats 1000000 in
      private theorem frozenPart9 :
          $checker (($entries).drop 90) = true := by
        with_unfolding_all decide
      set_option maxRecDepth 50000 in
      theorem $theoremName : $goal := by
        exact Challenge.EvmProof.StackCertificate.frozenEntryChecks_ten_parts
          $program $lookup $entries frozenPart0 frozenPart1 frozenPart2
          frozenPart3 frozenPart4 frozenPart5 frozenPart6 frozenPart7
          frozenPart8 frozenPart9
      end)

/-! ## Soundness bridge from compact length keys -/

def certificateData (program : List Asm) (entries : List FrozenStackEntry) :
    CertData :=
  materializeStackCertificate program (entries.map thawStackEntry)

theorem frozenEntryChecks_eq_lengthEntryChecks (program : List Asm)
    (lookup : CertLookup) (entries : List FrozenStackEntry) :
    frozenEntryChecks program lookup entries =
      lengthEntryChecks program lookup (certificateData program entries).entries := by
  simp [frozenEntryChecks, lengthEntryChecks, certificateData,
    materializeStackCertificate, thawStackEntry, List.map_map,
    Function.comp_def]

def suffixLookup (program : List Asm) (entries : List FrozenStackEntry) :
    CertLookup := fun suffix =>
  if suffix <:+ program then lengthLookup entries suffix else none

def checkedCert (program : List Asm) (entries : List FrozenStackEntry) : Cert :=
  (suffixLookup program entries).toCert

theorem suffixLookup_eq {program : List Asm} {entries : List FrozenStackEntry}
    {suffix : List Asm} (h : suffix <:+ program) :
    suffixLookup program entries suffix = lengthLookup entries suffix := by
  simp [suffixLookup, h]

private theorem checkedCert_eq {program : List Asm}
    {entries : List FrozenStackEntry} {suffix : List Asm}
    (h : suffix <:+ program) :
    (checkedCert program entries).fl suffix =
        (lengthLookup entries).toCert.fl suffix ∧
      (checkedCert program entries).fbMax suffix =
        (lengthLookup entries).toCert.fbMax suffix ∧
      (checkedCert program entries).rl suffix =
        (lengthLookup entries).toCert.rl suffix := by
  simp [checkedCert, CertLookup.toCert, suffixLookup_eq h]

private theorem tail_suffix {program : List Asm} {instruction : Asm}
    {suffix : List Asm} (h : instruction :: suffix <:+ program) :
    suffix <:+ program :=
  IsTrans.trans suffix (instruction :: suffix) program
    (List.suffix_cons instruction suffix) h

theorem frameStep_checked_iff_length {program : List Asm}
    {entries : List FrozenStackEntry} {instruction : Asm}
    {suffix : List Asm} {stack : FLayout} {frameBase : Nat}
    {returns : FLayout} (hpos : instruction :: suffix <:+ program) :
    frameStep program (checkedCert program entries) instruction suffix
        stack frameBase returns ↔
      frameStep program (lengthLookup entries).toCert instruction suffix
        stack frameBase returns := by
  have hsuffix := tail_suffix hpos
  rcases checkedCert_eq hsuffix with ⟨hflc, hfbc, hrlc⟩
  cases instruction with
  | push | op | dup | swap | pop | label | pushLabel =>
      simp only [frameStep]
      rw [hflc, hfbc, hrlc]
  | dynJump => rfl
  | jump label =>
      simp only [frameStep]
      constructor
      · intro h
        rcases h with hlocal | hcall
        · rcases hlocal with ⟨target, hfind, hfl, hfb, hrl⟩
          have ht := findLabel_suffix hfind
          rcases checkedCert_eq ht with ⟨hflt, hfbt, hrlt⟩
          exact Or.inl ⟨target, hfind, hflt ▸ hfl, hfbt ▸ hfb, hrlt ▸ hrl⟩
        · rcases hcall with
            ⟨Sw, Smid, Lret, continuation, target, Sret, hfind, rfl, hS,
              hwords, hflt, hfbt, hrlt, hretwords, hfindRet, hflcont,
              hfbcont, hrlcont⟩
          have ht := findLabel_suffix hfind
          have hcontinuation := findLabel_suffix hfindRet
          rcases checkedCert_eq ht with ⟨hflt', hfbt', hrlt'⟩
          rcases checkedCert_eq hcontinuation with
            ⟨hflr, hfbr, hrlr⟩
          exact Or.inr ⟨Sw, Smid, Lret, continuation, target, Sret, hfind,
            rfl, hS, hwords, hflt' ▸ hflt, hfbt' ▸ hfbt, hrlt' ▸ hrlt,
            hretwords, hfindRet, hflr ▸ hflcont, hfbr ▸ hfbcont,
            hrlr ▸ hrlcont⟩
      · intro h
        rcases h with hlocal | hcall
        · rcases hlocal with ⟨target, hfind, hfl, hfb, hrl⟩
          have ht := findLabel_suffix hfind
          rcases checkedCert_eq ht with ⟨hflt, hfbt, hrlt⟩
          exact Or.inl ⟨target, hfind, hflt.symm ▸ hfl, hfbt.symm ▸ hfb,
            hrlt.symm ▸ hrl⟩
        · rcases hcall with
            ⟨Sw, Smid, Lret, continuation, target, Sret, hfind, rfl, hS,
              hwords, hflt, hfbt, hrlt, hretwords, hfindRet, hflcont,
              hfbcont, hrlcont⟩
          have ht := findLabel_suffix hfind
          have hcontinuation := findLabel_suffix hfindRet
          rcases checkedCert_eq ht with ⟨hflt', hfbt', hrlt'⟩
          rcases checkedCert_eq hcontinuation with
            ⟨hflr, hfbr, hrlr⟩
          exact Or.inr ⟨Sw, Smid, Lret, continuation, target, Sret, hfind,
            rfl, hS, hwords, hflt'.symm ▸ hflt, hfbt'.symm ▸ hfbt,
            hrlt'.symm ▸ hrlt, hretwords, hfindRet,
            hflr.symm ▸ hflcont, hfbr.symm ▸ hfbcont,
            hrlr.symm ▸ hrlcont⟩
  | jumpi label =>
      simp only [frameStep]
      constructor
      · rintro ⟨stack', hstack, ⟨target, hfind, hflt, hfbt, hrlt⟩,
          hfl, hfb, hrl⟩
        have ht := findLabel_suffix hfind
        rcases checkedCert_eq ht with ⟨hflt', hfbt', hrlt'⟩
        exact ⟨stack', hstack,
          ⟨target, hfind, hflt' ▸ hflt, hfbt' ▸ hfbt, hrlt' ▸ hrlt⟩,
          hflc ▸ hfl, hfbc ▸ hfb, hrlc ▸ hrl⟩
      · rintro ⟨stack', hstack, ⟨target, hfind, hflt, hfbt, hrlt⟩,
          hfl, hfb, hrl⟩
        have ht := findLabel_suffix hfind
        rcases checkedCert_eq ht with ⟨hflt', hfbt', hrlt'⟩
        exact ⟨stack', hstack,
          ⟨target, hfind, hflt'.symm ▸ hflt, hfbt'.symm ▸ hfbt,
            hrlt'.symm ▸ hrlt⟩, hflc.symm ▸ hfl, hfbc.symm ▸ hfb,
          hrlc.symm ▸ hrl⟩

private def certEntryOfFrozen (program : List Asm)
    (entry : FrozenStackEntry) : CertEntry :=
  let thawed := thawStackEntry entry
  (thawed.1, program.drop (program.length - thawed.1),
    thawed.2.1, thawed.2.2.1, thawed.2.2.2)

private theorem certificateEntries_eq (program : List Asm)
    (entries : List FrozenStackEntry) :
    (certificateData program entries).entries =
      entries.map (certEntryOfFrozen program) := by
  simp [certificateData, materializeStackCertificate, certEntryOfFrozen,
    List.map_map, Function.comp_def]

private theorem lengthLookup_some {entries : List FrozenStackEntry}
    {suffix : List Asm} {value : CertValue}
    (h : lengthLookup entries suffix = some value) :
    ∃ entry ∈ entries,
      entry.1 = suffix.length ∧
        thawCertValue (entry.2.1, entry.2.2.1, entry.2.2.2) = value := by
  unfold lengthLookup frozenLayoutAt at h
  rcases hfind : entries.find? (fun entry => entry.1 == suffix.length) with
    _ | entry
  · simp [hfind] at h
  · have hmem := List.mem_of_find?_eq_some hfind
    have hkey := List.find?_some hfind
    simp only [beq_iff_eq] at hkey
    simp only [hfind, Option.map_some] at h
    exact ⟨entry, hmem, hkey, Option.some.inj h⟩

theorem checkedCert_valid (program : List Asm)
    (entries : List FrozenStackEntry)
    (hchecks : lengthEntryChecks program (lengthLookup entries)
      (certificateData program entries).entries = true) :
    (checkedCert program entries).Valid program := by
  intro instruction suffix stack frameBase returns hfl hfb hrl
  have hpos : instruction :: suffix <:+ program := by
    change Option.map (fun value => value.1)
      (suffixLookup program entries (instruction :: suffix)) = some stack at hfl
    unfold suffixLookup at hfl
    split at hfl
    · assumption
    · simp at hfl
  have heq := checkedCert_eq (entries := entries) hpos
  have hlength : lengthLookup entries (instruction :: suffix) =
      some (stack, frameBase, returns) := by
    apply (CertLookup.eq_some_iff_fields (lengthLookup entries)
      _ _ _ _).mpr
    exact ⟨heq.1 ▸ hfl, heq.2.1 ▸ hfb, heq.2.2 ▸ hrl⟩
  obtain ⟨entry, hmem, hkey, hvalue⟩ := lengthLookup_some hlength
  have hcanon : program.drop (program.length - entry.1) =
      instruction :: suffix := by
    rw [hkey]
    exact (List.suffix_iff_eq_drop.mp hpos).symm
  have hentryMem : certEntryOfFrozen program entry ∈
      (certificateData program entries).entries := by
    rw [certificateEntries_eq]
    exact List.mem_map.mpr ⟨entry, hmem, rfl⟩
  have hchecked := (List.all_eq_true.mp hchecks)
    (certEntryOfFrozen program entry) hentryMem
  simp only [Bool.and_eq_true] at hchecked
  have hstep := hchecked.2
  dsimp [certEntryOfFrozen, thawStackEntry] at hstep hvalue
  rw [hcanon] at hstep
  change frameStepLookupB program (lengthLookup entries) instruction suffix
    (entry.2.1.map decodeStackSlot) entry.2.2.1
      (entry.2.2.2.map decodeStackSlot) = true at hstep
  rw [frameStepLookupB_eq_frameStepB] at hstep
  have hsemantic := frameStepB_sound hstep
  dsimp [thawCertValue] at hvalue
  rcases Prod.mk.inj hvalue with ⟨hstack, hframeReturns⟩
  rcases Prod.mk.inj hframeReturns with ⟨hframe, hreturns⟩
  subst stack
  subst frameBase
  subst returns
  exact (frameStep_checked_iff_length (entries := entries) hpos).mpr hsemantic

theorem checkedCert_bounded (program : List Asm)
    (entries : List FrozenStackEntry)
    (hchecks : lengthEntryChecks program (lengthLookup entries)
      (certificateData program entries).entries = true) :
    (checkedCert program entries).Bounded := by
  intro suffix stack frameBase hfl hfb
  have hpos : suffix <:+ program := by
    change Option.map (fun value => value.1)
      (suffixLookup program entries suffix) = some stack at hfl
    unfold suffixLookup at hfl
    split at hfl
    · assumption
    · simp at hfl
  have heq := checkedCert_eq (entries := entries) hpos
  have hfl' := heq.1 ▸ hfl
  have hfb' := heq.2.1 ▸ hfb
  change Option.map (fun value => value.1) (lengthLookup entries suffix) =
    some stack at hfl'
  change Option.map (fun value => value.2.1) (lengthLookup entries suffix) =
    some frameBase at hfb'
  rcases hlookup : lengthLookup entries suffix with _ | value
  · simp [hlookup] at hfl'
  · rcases value with ⟨stack', frameBase', returns'⟩
    simp only [hlookup, Option.map_some, Option.some.injEq] at hfl' hfb'
    subst stack'
    subst frameBase'
    obtain ⟨entry, hmem, -, hvalue⟩ := lengthLookup_some hlookup
    have hentryMem : certEntryOfFrozen program entry ∈
        (certificateData program entries).entries := by
      rw [certificateEntries_eq]
      exact List.mem_map.mpr ⟨entry, hmem, rfl⟩
    have hchecked := (List.all_eq_true.mp hchecks)
      (certEntryOfFrozen program entry) hentryMem
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hchecked
    dsimp [certEntryOfFrozen, thawStackEntry, thawCertValue] at hchecked hvalue
    rcases Prod.mk.inj hvalue with ⟨hstack, hframeReturns⟩
    rcases Prod.mk.inj hframeReturns with ⟨hframe, -⟩
    rw [hstack, hframe] at hchecked
    exact hchecked.1

theorem checkedCert_entry {program : List Asm}
    {entries : List FrozenStackEntry}
    (hentry : lengthLookup entries program = some ([], 0, [])) :
    (checkedCert program entries).fl program = some [] ∧
      (checkedCert program entries).fbMax program = some 0 ∧
      (checkedCert program entries).rl program = some [] := by
  simp [checkedCert, CertLookup.toCert,
    suffixLookup_eq (List.suffix_refl program), hentry]

variable [model : ExternalModel]

theorem assembly_stack_bound (program : List Asm)
    (entries : List FrozenStackEntry)
    (hchecks : lengthEntryChecks program (lengthLookup entries)
      (certificateData program entries).entries = true)
    (hentry : lengthLookup entries program = some ([], 0, []))
    (state : YulSemantics.EVM.EvmState) :
    ∀ mid, ASteps (model := model) program ⟨program, [], state⟩ mid →
      mid.stk.length ≤ 1023 := by
  rcases checkedCert_entry hentry with ⟨hfl, hfb, hrl⟩
  exact run_stack_bound2 (checkedCert_valid program entries hchecks)
    (checkedCert_bounded program entries hchecks) hfl hfb hrl state

end Challenge.EvmProof.StackCertificate
