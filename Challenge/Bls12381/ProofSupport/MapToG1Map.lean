import Challenge.Bls12381.ProofSupport.MapToG1Executable
import Challenge.Bls12381.ProofSupport.MapToG1IsogenyLawful
import Challenge.Bls12381.ProofSupport.MapToG1Sswu
import Challenge.Bls12381.ProofSupport.ScalarMulSemantics

set_option warningAsError true

/-!
# Shared lawful MAP_FP_TO_G1 operation

The final cofactor stage is proved equal to `hEff` scalar multiplication in
the independent Mathlib affine group model.  The stronger statement
`N • map(u) = 0` still requires a certified G1 group-exponent/order result;
it is deliberately documented rather than assumed.
-/

namespace Challenge.Bls12381.ProofSupport.MapToG1

theorem mapBeforeCofactor_onCurve (u : Field) :
    G1Affine.OnCurve (mapBeforeCofactor u) := by
  apply iso11_onCurve
  exact sswuSource_onCurve u

theorem map_onCurve (u : Field) : G1Affine.OnCurve (map u) := by
  exact ScalarMul.g1_onCurve hEff (mapBeforeCofactor u)
    (mapBeforeCofactor_onCurve u)

/-- The lawful map always converts to a codec-valid decoded G1 point. -/
theorem map_toWire_valid (u : Field) :
    Codec.ValidG1 (G1Affine.toWire (map u)) := by
  have hcurve := map_onCurve u
  cases hpoint : map u with
  | infinity => trivial
  | affine x y =>
      exact G1Affine.onCurve_toWire (by simpa [hpoint] using hcurve)

/-- The executable cofactor stage is exactly natural-number scalar
multiplication in the independent Mathlib affine group model. -/
theorem map_nsmul (u : Field) :
    AffineGroup.toMathlib G1Affine.curve ⟨map u, map_onCurve u⟩ =
      hEff • AffineGroup.toMathlib G1Affine.curve
        ⟨mapBeforeCofactor u, mapBeforeCofactor_onCurve u⟩ := by
  have h := ScalarMul.g1_nsmul hEff (mapBeforeCofactor u)
    (mapBeforeCofactor_onCurve u)
  exact h

theorem run_eq_some_iff (input output : ByteArray) :
    run input = some output ↔
      ∃ u, input.size = Codec.fpBytes ∧ Codec.decodeFp input 0 = some u ∧
        output = Codec.encodeG1 (G1Affine.toWire (map (PrimeField.finEquiv u))) := by
  simp [run]
  intro _
  cases hdecode : Codec.decodeFp input 0 with
  | none => simp
  | some u => simp [eq_comm]

theorem run_eq_none_of_wrong_length {input : ByteArray}
    (hsize : input.size ≠ Codec.fpBytes) : run input = none := by
  have hsize' : input.size ≠ 64 := by simpa [Codec.fpBytes] using hsize
  simp [run, Codec.fpBytes, hsize']

theorem run_eq_none_of_padding_nonzero {input : ByteArray} {i : Nat}
    (hsize : input.size = Codec.fpBytes) (hi : i < 16)
    (hnonzero : input[i]! ≠ 0) : run input = none := by
  have hdecode : Codec.decodeFp input 0 = none :=
    Codec.decodeFp_eq_none_of_padding_nonzero
      (offset := 0) (by simp [hsize]) hi (by simpa using hnonzero)
  simp [run, hsize, hdecode]

theorem run_eq_none_of_value_ge {input : ByteArray}
    (hsize : input.size = Codec.fpBytes)
    (hvalue : EvmSemantics.Crypto.Bls12381.p ≤ Codec.fpWindowValue input 0) :
    run input = none := by
  have hdecode : Codec.decodeFp input 0 = none :=
    Codec.decodeFp_eq_none_of_value_ge
      (offset := 0) (by simp [hsize]) hvalue
  simp [run, hsize, hdecode]

end Challenge.Bls12381.ProofSupport.MapToG1
