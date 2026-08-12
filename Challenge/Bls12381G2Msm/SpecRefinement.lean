import Challenge.Bls12381G2Msm.Spec

set_option warningAsError true

/-!
# G2MSM specification adapter refinement

These compact equations isolate strict wire decoding from later concrete
execution proofs.  Consumers can reason about one term or the final adapter
without unfolding subgroup checks, scalar packaging, and the complete naive
MSM simultaneously.
-/

namespace Challenge.Bls12381G2Msm

open Challenge.Bls12381.ProofSupport

theorem pairBytes_eq :
    pairBytes = Codec.g2Bytes + Codec.scalarBytes := rfl

@[simp] theorem decodeTerms_zero (input : ByteArray) (offset : Nat) :
    decodeTerms input offset 0 = some [] := rfl

@[simp] theorem decodeTerms_succ (input : ByteArray) (offset count : Nat) :
    decodeTerms input offset (count + 1) =
      (do
        let term ← decodeTerm input offset
        let rest ← decodeTerms input (offset + pairBytes) count
        some (term :: rest)) := rfl

private theorem packagedScalar_eq_some_iff (input : ByteArray) (offset : Nat)
    (point : EvmSemantics.Crypto.Bls12381.G2Point) (term : Msm.G2WireTerm) :
    (match Codec.decodeScalar input (offset + Codec.g2Bytes) with
      | none => none
      | some _ => some (point, scalarAt input (offset + Codec.g2Bytes))) =
        some term ↔
      point = term.1 ∧
        Codec.decodeScalar input (offset + Codec.g2Bytes) = some term.2.val := by
  split
  · rename_i hscalar
    constructor
    · intro h
      exact ((Option.some_ne_none term) h.symm).elim
    · rintro ⟨_, hsome⟩
      exact ((Option.some_ne_none term.2.val)
        (hscalar.symm.trans hsome).symm).elim
  · rename_i scalar hscalar
    rw [hscalar]
    simp only [Option.some.injEq]
    have hvalue : Codec.scalarWindowValue input (offset + Codec.g2Bytes) =
        scalar :=
      (Codec.decodeScalar_eq_some_iff input
        (offset + Codec.g2Bytes) scalar).1 hscalar |>.2
    constructor
    · intro hterm
      refine ⟨congrArg Prod.fst hterm, ?_⟩
      exact hvalue.symm.trans
        (congrArg Fin.val (congrArg Prod.snd hterm))
    · rintro ⟨hpoint, hscalarTerm⟩
      apply Prod.ext
      · exact hpoint
      · apply Fin.ext
        exact hvalue.trans hscalarTerm

theorem decodeTerm_eq_some_iff (input : ByteArray) (offset : Nat)
    (term : Msm.G2WireTerm) :
    decodeTerm input offset = some term ↔
      Codec.decodeG2Subgroup input offset = some term.1 ∧
      Codec.decodeScalar input (offset + Codec.g2Bytes) = some term.2.val := by
  change (Codec.decodeG2Subgroup input offset).bind (fun point =>
      match Codec.decodeScalar input (offset + Codec.g2Bytes) with
      | none => none
      | some _ => some (point, scalarAt input (offset + Codec.g2Bytes))) =
        some term ↔ _
  rw [Option.bind_eq_some_iff]
  simp only [packagedScalar_eq_some_iff]
  constructor
  · rintro ⟨point, hpoint, hpointEq, hscalar⟩
    subst point
    exact ⟨hpoint, hscalar⟩
  · rintro ⟨hpoint, hscalar⟩
    exact ⟨term.1, hpoint, rfl, hscalar⟩

theorem decodeTerm_subgroup {input : ByteArray} {offset : Nat}
    {term : Msm.G2WireTerm}
    (hdecode : decodeTerm input offset = some term) :
    Subgroup.g2 term.1 = true := by
  have hpoint := (decodeTerm_eq_some_iff input offset term).1 hdecode |>.1
  exact (Codec.decodeG2Subgroup_eq_some_iff input offset term.1).1 hpoint |>.2

theorem decodeTerms_length {input : ByteArray} {offset count : Nat}
    {terms : List Msm.G2WireTerm}
    (hdecode : decodeTerms input offset count = some terms) :
    terms.length = count := by
  induction count generalizing offset terms with
  | zero =>
      simp only [decodeTerms_zero] at hdecode
      cases Option.some.inj hdecode
      rfl
  | succ count ih =>
      rw [show count + 1 = Nat.succ count by omega, decodeTerms_succ] at hdecode
      cases hterm : decodeTerm input offset with
      | none => simp [hterm] at hdecode
      | some term =>
          cases hrest : decodeTerms input (offset + pairBytes) count with
          | none => simp [hterm, hrest] at hdecode
          | some rest =>
              simp only [hterm, hrest] at hdecode
              cases Option.some.inj hdecode
              simp [ih hrest]

theorem spec_eq_some_iff {input output : ByteArray} :
    spec input = some output ↔
      input.size ≠ 0 ∧ input.size % pairBytes = 0 ∧
        ∃ terms, decodeTerms input 0 (input.size / pairBytes) = some terms ∧
          output = Codec.encodeG2 (Msm.g2Wire terms) := by
  unfold spec
  by_cases hbad : input.size = 0 ∨ input.size % pairBytes ≠ 0
  · rw [if_pos hbad]
    constructor
    · intro h
      exact ((Option.some_ne_none output) h.symm).elim
    · rintro ⟨hnonempty, hmultiple, _⟩
      exact (hbad.elim hnonempty fun hnot => hnot hmultiple).elim
  · have hnonempty : input.size ≠ 0 := fun h => hbad (Or.inl h)
    have hmultiple : input.size % pairBytes = 0 := by
      by_contra h
      exact hbad (Or.inr h)
    rw [if_neg hbad]
    change (decodeTerms input 0 (input.size / pairBytes)).bind
        (fun terms => some (Codec.encodeG2 (Msm.g2Wire terms))) = some output ↔ _
    rw [Option.bind_eq_some_iff]
    constructor
    · rintro ⟨terms, hterms, houtput⟩
      exact ⟨hnonempty, hmultiple, terms, hterms,
        (Option.some.inj houtput).symm⟩
    · rintro ⟨_, _, terms, hterms, houtput⟩
      exact ⟨terms, hterms, congrArg some houtput.symm⟩

theorem spec_eq_none_iff {input : ByteArray} :
    spec input = none ↔
      input.size = 0 ∨ input.size % pairBytes ≠ 0 ∨
        decodeTerms input 0 (input.size / pairBytes) = none := by
  unfold spec
  by_cases hbad : input.size = 0 ∨ input.size % pairBytes ≠ 0
  · rw [if_pos hbad]
    constructor
    · intro _
      exact hbad.elim Or.inl fun h => Or.inr (Or.inl h)
    · intro _
      rfl
  · have hnonempty : input.size ≠ 0 := fun h => hbad (Or.inl h)
    have hmultiple : input.size % pairBytes = 0 := by
      by_contra h
      exact hbad (Or.inr h)
    rw [if_neg hbad]
    cases hterms : decodeTerms input 0 (input.size / pairBytes) with
    | none => simp [hnonempty, hmultiple]
    | some terms => simp [hnonempty, hmultiple]

theorem spec_invalid_length {input : ByteArray}
    (hsize : input.size = 0 ∨ input.size % pairBytes ≠ 0) :
    spec input = none := by
  exact spec_eq_none_iff.mpr (hsize.elim Or.inl fun h => Or.inr (Or.inl h))

theorem spec_success {input : ByteArray} {terms : List Msm.G2WireTerm}
    (hnonempty : input.size ≠ 0)
    (hmultiple : input.size % pairBytes = 0)
    (hterms : decodeTerms input 0 (input.size / pairBytes) = some terms) :
    spec input = some (Codec.encodeG2 (Msm.g2Wire terms)) := by
  apply spec_eq_some_iff.mpr
  exact ⟨hnonempty, hmultiple, terms, hterms, rfl⟩

end Challenge.Bls12381G2Msm
