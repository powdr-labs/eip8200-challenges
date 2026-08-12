import Challenge.Bls12381.ProofSupport.CodecG1
import Challenge.Bls12381.ProofSupport.CodecG2
import Challenge.Bls12381.ProofSupport.Subgroup

set_option warningAsError true

/-! # Optional EIP-2537 subgroup-validation codec boundary

G1ADD/G2ADD use the ordinary point decoders. MSM and pairing use these
wrappers after the same on-curve wire decoding step.
-/

namespace Challenge.Bls12381.ProofSupport.Codec

open EvmSemantics.Crypto.Bls12381

def decodeG1Subgroup (input : ByteArray) (offset : Nat) : Option Point := do
  let point ← decodeG1 input offset
  if Subgroup.g1 point then some point else none

def decodeG2Subgroup (input : ByteArray) (offset : Nat) : Option G2Point := do
  let point ← decodeG2 input offset
  if Subgroup.g2 point then some point else none

theorem decodeG1Subgroup_eq_some_iff (input : ByteArray) (offset : Nat)
    (point : Point) :
    decodeG1Subgroup input offset = some point ↔
      decodeG1 input offset = some point ∧ Subgroup.g1 point = true := by
  constructor
  · intro h
    unfold decodeG1Subgroup at h
    cases hdecode : decodeG1 input offset with
    | none => simp [hdecode] at h
    | some decoded =>
        by_cases hsubgroup : Subgroup.g1 decoded = true
        · simp [hdecode, hsubgroup] at h
          have heq := h
          subst point
          exact ⟨rfl, hsubgroup⟩
        · simp [hdecode, hsubgroup] at h
  · rintro ⟨hdecode, hsubgroup⟩
    unfold decodeG1Subgroup
    simp [hdecode, hsubgroup]

theorem decodeG2Subgroup_eq_some_iff (input : ByteArray) (offset : Nat)
    (point : G2Point) :
    decodeG2Subgroup input offset = some point ↔
      decodeG2 input offset = some point ∧ Subgroup.g2 point = true := by
  constructor
  · intro h
    unfold decodeG2Subgroup at h
    cases hdecode : decodeG2 input offset with
    | none => simp [hdecode] at h
    | some decoded =>
        by_cases hsubgroup : Subgroup.g2 decoded = true
        · simp [hdecode, hsubgroup] at h
          have heq := h
          subst point
          exact ⟨rfl, hsubgroup⟩
        · simp [hdecode, hsubgroup] at h
  · rintro ⟨hdecode, hsubgroup⟩
    unfold decodeG2Subgroup
    simp [hdecode, hsubgroup]

theorem decodeG1Subgroup_forget {input : ByteArray} {offset : Nat}
    {point : Point} (hdecode : decodeG1Subgroup input offset = some point) :
    decodeG1 input offset = some point :=
  (decodeG1Subgroup_eq_some_iff input offset point).1 hdecode |>.1

theorem decodeG2Subgroup_forget {input : ByteArray} {offset : Nat}
    {point : G2Point} (hdecode : decodeG2Subgroup input offset = some point) :
    decodeG2 input offset = some point :=
  (decodeG2Subgroup_eq_some_iff input offset point).1 hdecode |>.1

end Challenge.Bls12381.ProofSupport.Codec
