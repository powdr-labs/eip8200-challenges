import Challenge.Bls12381.ProofSupport.G1Affine
import Challenge.Bls12381.ProofSupport.G2Affine
import Challenge.Bls12381.ProofSupport.CodecScalar
import Challenge.Bls12381.ProofSupport.CodecG1Core
import Challenge.Bls12381.ProofSupport.CodecG2Core
import Challenge.Bls12381.ProofSupport.ScalarMulProgram

set_option warningAsError true

/-!
# Shared naive scalar multiplication

The executable algorithm is the direct interpreter of the one parametric
binary program in `ScalarMulProgram`; the state-writer interpreter audits every
operation invoked by that same control flow.  `binary_even` and `binary_odd`
universally characterize its double-and-add schedule.  Independent group
semantics live in the proof-only `ScalarMulSemantics` module so executable
consumers do not import Mathlib's algebraic-geometry stack.  This module makes
no equality claim about the pinned opaque-inverse scalar code.
-/

namespace Challenge.Bls12381.ProofSupport.ScalarMul

open EvmSemantics.Crypto.Bls12381

/-- An exact EIP-2537 scalar: an unreduced unsigned 256-bit integer. -/
abbrev Scalar256 := Fin (2 ^ 256)

/-- Package the exact scalar returned by the approved 32-byte codec. -/
def scalar256OfDecode {input : ByteArray} {offset scalar : Nat}
    (hdecode : Codec.decodeScalar input offset = some scalar) : Scalar256 :=
  ⟨scalar, Codec.decodeScalar_value_lt hdecode⟩

@[simp] theorem scalar256OfDecode_val {input : ByteArray} {offset scalar : Nat}
    (hdecode : Codec.decodeScalar input offset = some scalar) :
    (scalar256OfDecode hdecode).val = scalar := rfl

/-! ## Auditable binary scalar semantics -/

/-- Executable direct interpretation of the proof-friendly right-to-left
binary program.  This is the local mathematical scalar operation; no equality
to the pinned inverse-dependent curve scalar multiplication is claimed. -/
def binary {Point : Type} (zero : Point) (add : Point → Point → Point)
    (double : Point → Point) (scalar : Nat) (point : Point) : Point :=
  Id.run (Program.runWith (Program.directOps zero add double) scalar point)

@[simp] theorem binary_zero {Point : Type} (zero : Point)
    (add : Point → Point → Point) (double : Point → Point) (point : Point) :
    binary zero add double 0 point = zero := by
  exact Program.runWith_direct_zero zero add double point

@[simp] theorem binary_one {Point : Type} (zero : Point)
    (add : Point → Point → Point) (double : Point → Point) (point : Point) :
    binary zero add double 1 point = point := by
  exact Program.runWith_direct_one zero add double point

theorem binary_step {Point : Type} (zero : Point)
    (add : Point → Point → Point) (double : Point → Point)
    (scalar : Nat) (point : Point) (hscalar : scalar ≠ 0) :
    binary zero add double scalar point =
      if scalar = 1 then point
      else if scalar % 2 = 1 then
          add (binary zero add double (scalar / 2) (double point)) point
        else binary zero add double (scalar / 2) (double point) := by
  exact Program.runWith_direct_step zero add double scalar point hscalar

theorem binary_even {Point : Type} (zero : Point)
    (add : Point → Point → Point) (double : Point → Point)
    (scalar : Nat) (point : Point) :
    binary zero add double (2 * scalar) point =
      binary zero add double scalar (double point) := by
  cases scalar with
  | zero => simp
  | succ scalar =>
      rw [binary_step]
      · norm_num
      · omega

theorem binary_odd {Point : Type} (zero : Point)
    (add : Point → Point → Point) (double : Point → Point)
    (scalar : Nat) (point : Point) :
    binary zero add double (2 * scalar + 1) point =
      if scalar = 0 then point
      else add (binary zero add double scalar (double point)) point := by
  cases scalar with
  | zero => simp
  | succ scalar =>
      rw [binary_step]
      · rw [show (2 * (scalar + 1) + 1) ≠ 1 by omega |> if_neg]
        rw [show (2 * (scalar + 1) + 1) / 2 = scalar + 1 by omega]
        norm_num
      · omega

/-- Binary scalar multiplication preserves any invariant preserved by the
identity, addition, and doubling operations. -/
theorem binary_preserves {Point : Type} (zero : Point)
    (add : Point → Point → Point) (double : Point → Point)
    (Valid : Point → Prop)
    (hzero : Valid zero)
    (hadd : ∀ left right, Valid left → Valid right → Valid (add left right))
    (hdouble : ∀ point, Valid point → Valid (double point))
    (scalar : Nat) (point : Point) (hpoint : Valid point) :
    Valid (binary zero add double scalar point) := by
  induction scalar using Nat.strong_induction_on generalizing point with
  | h scalar ih =>
      by_cases hscalar : scalar = 0
      · subst scalar
        simpa using hzero
      · by_cases hone : scalar = 1
        · subst scalar
          simpa using hpoint
        rw [binary_step zero add double scalar point hscalar, if_neg hone]
        have hhalf : scalar / 2 < scalar :=
          Nat.div_lt_self (Nat.zero_lt_of_ne_zero hscalar) (by omega)
        have hrest :
            Valid (binary zero add double (scalar / 2) (double point)) :=
          ih (scalar / 2) hhalf (double point) (hdouble point hpoint)
        by_cases hodd : scalar % 2 = 1
        · rw [if_pos hodd]
          exact hadd _ _ hrest hpoint
        · rw [if_neg hodd]
          exact hrest

/-- Lifting an invariant-preserving binary recursion to the subtype of valid
points does not change its underlying executable point value. -/
theorem binary_lift_val {Point : Type} (zero : Point)
    (add : Point → Point → Point) (double : Point → Point)
    (Valid : Point → Prop)
    (hzero : Valid zero)
    (hadd : ∀ left right, Valid left → Valid right → Valid (add left right))
    (hdouble : ∀ point, Valid point → Valid (double point))
    (scalar : Nat) (point : Point) (hpoint : Valid point) :
    (binary (⟨zero, hzero⟩ : { point // Valid point })
      (fun (left right : { point // Valid point }) =>
        ⟨add left.1 right.1, hadd left.1 right.1 left.2 right.2⟩)
      (fun (lifted : { point // Valid point }) =>
        ⟨double lifted.1, hdouble lifted.1 lifted.2⟩)
      scalar (⟨point, hpoint⟩ : { point // Valid point })).1 =
      binary zero add double scalar point := by
  induction scalar using Nat.strong_induction_on generalizing point with
  | h scalar ih =>
      by_cases hscalar : scalar = 0
      · subst scalar
        simp
      · by_cases hone : scalar = 1
        · subst scalar
          simp
        rw [binary_step _ _ _ scalar _ hscalar,
          binary_step zero add double scalar point hscalar,
          if_neg hone, if_neg hone]
        have hhalf : scalar / 2 < scalar :=
          Nat.div_lt_self (Nat.zero_lt_of_ne_zero hscalar) (by omega)
        by_cases hodd : scalar % 2 = 1
        · rw [if_pos hodd, if_pos hodd]
          change add
              (binary _ _ _ (scalar / 2)
                (⟨double point, hdouble point hpoint⟩ :
                  { point // Valid point })).1 point =
            add (binary zero add double (scalar / 2) (double point)) point
          rw [ih (scalar / 2) hhalf (double point) (hdouble point hpoint)]
        · rw [if_neg hodd, if_neg hodd]
          exact ih (scalar / 2) hhalf (double point) (hdouble point hpoint)

/-! ## BLS12-381 curve instantiations -/

/-- Local binary G1 scalar operation used by the EIP adapter. -/
def g1 (scalar : Nat) (point : G1Affine.Point) : G1Affine.Point :=
  binary G1Affine.infinity G1Affine.add G1Affine.double scalar point

/-- Local binary G2 scalar operation used by the EIP adapter. -/
def g2 (scalar : Nat) (point : G2Affine.Point) : G2Affine.Point :=
  binary G2Affine.infinity G2Affine.add G2Affine.double scalar point

/-- Restrict G1 scalar multiplication to an exact EIP 256-bit scalar. -/
def g1Eip (scalar : Scalar256) (point : G1Affine.Point) : G1Affine.Point :=
  g1 scalar.val point

/-- Restrict G2 scalar multiplication to an exact EIP 256-bit scalar. -/
def g2Eip (scalar : Scalar256) (point : G2Affine.Point) : G2Affine.Point :=
  g2 scalar.val point

@[simp] theorem g1Eip_of_decode {input : ByteArray} {offset scalar : Nat}
    (hdecode : Codec.decodeScalar input offset = some scalar)
    (point : G1Affine.Point) :
    g1Eip (scalar256OfDecode hdecode) point = g1 scalar point := rfl

@[simp] theorem g2Eip_of_decode {input : ByteArray} {offset scalar : Nat}
    (hdecode : Codec.decodeScalar input offset = some scalar)
    (point : G2Affine.Point) :
    g2Eip (scalar256OfDecode hdecode) point = g2 scalar point := rfl

@[simp] theorem g1_zero (point : G1Affine.Point) :
    g1 0 point = G1Affine.infinity := binary_zero _ _ _ point

@[simp] theorem g2_zero (point : G2Affine.Point) :
    g2 0 point = G2Affine.infinity := binary_zero _ _ _ point

@[simp] theorem g1_one (point : G1Affine.Point) : g1 1 point = point := by
  simp [g1]

@[simp] theorem g2_one (point : G2Affine.Point) : g2 1 point = point := by
  simp [g2]

theorem g1_even (scalar : Nat) (point : G1Affine.Point) :
    g1 (2 * scalar) point = g1 scalar (G1Affine.double point) :=
  binary_even _ _ _ scalar point

theorem g2_even (scalar : Nat) (point : G2Affine.Point) :
    g2 (2 * scalar) point = g2 scalar (G2Affine.double point) :=
  binary_even _ _ _ scalar point

theorem g1_odd (scalar : Nat) (point : G1Affine.Point) :
    g1 (2 * scalar + 1) point =
      G1Affine.add (g1 scalar (G1Affine.double point)) point := by
  by_cases hscalar : scalar = 0
  · subst scalar
    simp [G1Affine.add]
  · simpa [g1, hscalar] using
      binary_odd G1Affine.infinity G1Affine.add G1Affine.double scalar point

theorem g2_odd (scalar : Nat) (point : G2Affine.Point) :
    g2 (2 * scalar + 1) point =
      G2Affine.add (g2 scalar (G2Affine.double point)) point := by
  by_cases hscalar : scalar = 0
  · subst scalar
    simp [G2Affine.add]
  · simpa [g2, hscalar] using
      binary_odd G2Affine.infinity G2Affine.add G2Affine.double scalar point

theorem g1_onCurve (scalar : Nat) (point : G1Affine.Point)
    (hpoint : G1Affine.OnCurve point) :
    G1Affine.OnCurve (g1 scalar point) :=
  binary_preserves _ _ _ G1Affine.OnCurve
    (LawfulAffine.onCurve_infinity G1Affine.curve)
    G1Affine.onCurve_add G1Affine.onCurve_double scalar point hpoint

theorem g2_onCurve (scalar : Nat) (point : G2Affine.Point)
    (hpoint : G2Affine.OnCurve point) :
    G2Affine.OnCurve (g2 scalar point) :=
  binary_preserves _ _ _ G2Affine.OnCurve
    (LawfulAffine.onCurve_infinity G2Affine.curve)
    G2Affine.onCurve_add G2Affine.onCurve_double scalar point hpoint

@[simp] theorem g1_infinity (scalar : Nat) :
    g1 scalar G1Affine.infinity = G1Affine.infinity := by
  apply binary_preserves _ _ _ (fun point => point = G1Affine.infinity)
  · rfl
  · intro left right hleft hright
    subst left
    subst right
    simp [G1Affine.add]
  · intro point hpoint
    subst point
    simp [G1Affine.double]
  · rfl

@[simp] theorem g2_infinity (scalar : Nat) :
    g2 scalar G2Affine.infinity = G2Affine.infinity := by
  apply binary_preserves _ _ _ (fun point => point = G2Affine.infinity)
  · rfl
  · intro left right hleft hright
    subst left
    subst right
    simp [G2Affine.add]
  · intro point hpoint
    subst point
    simp [G2Affine.double]
  · rfl

/-- Decode-level wire adapter for lawful G1 scalar multiplication. -/
def g1Wire (scalar : Nat) (point : EvmSemantics.Crypto.Bls12381.Point) :
    EvmSemantics.Crypto.Bls12381.Point :=
  G1Affine.toWire (g1 scalar (G1Affine.ofWire point))

/-- Decode-level wire adapter for lawful G2 scalar multiplication. -/
def g2Wire (scalar : Nat) (point : EvmSemantics.Crypto.Bls12381.G2Point) :
    EvmSemantics.Crypto.Bls12381.G2Point :=
  G2Affine.toWire (g2 scalar (G2Affine.ofWire point))

theorem g1Wire_refines (scalar : Nat)
    (point : EvmSemantics.Crypto.Bls12381.Point) :
    G1Affine.ofWire (g1Wire scalar point) =
      g1 scalar (G1Affine.ofWire point) := by
  simp [g1Wire]

theorem g2Wire_refines (scalar : Nat)
    (point : EvmSemantics.Crypto.Bls12381.G2Point) :
    G2Affine.ofWire (g2Wire scalar point) =
      g2 scalar (G2Affine.ofWire point) := by
  simp [g2Wire]

theorem g1Wire_valid (scalar : Nat)
    (point : EvmSemantics.Crypto.Bls12381.Point)
    (hpoint : Codec.ValidG1 point) : Codec.ValidG1 (g1Wire scalar point) := by
  have hinput : G1Affine.OnCurve (G1Affine.ofWire point) := by
    cases point with
    | infinity => exact LawfulAffine.onCurve_infinity G1Affine.curve
    | affine x y => exact G1Affine.onCurve_ofWire hpoint
  have houtput := g1_onCurve scalar (G1Affine.ofWire point) hinput
  unfold g1Wire
  cases hresult : g1 scalar (G1Affine.ofWire point) with
  | infinity => trivial
  | affine x y =>
      rw [hresult] at houtput
      exact G1Affine.onCurve_toWire houtput

theorem g2Wire_valid (scalar : Nat)
    (point : EvmSemantics.Crypto.Bls12381.G2Point)
    (hpoint : Codec.ValidG2 point) : Codec.ValidG2 (g2Wire scalar point) := by
  have hinput : G2Affine.OnCurve (G2Affine.ofWire point) := by
    cases point with
    | infinity => exact LawfulAffine.onCurve_infinity G2Affine.curve
    | affine x y => exact G2Affine.onCurve_ofWire hpoint
  have houtput := g2_onCurve scalar (G2Affine.ofWire point) hinput
  unfold g2Wire
  cases hresult : g2 scalar (G2Affine.ofWire point) with
  | infinity => trivial
  | affine x y =>
      rw [hresult] at houtput
      exact G2Affine.onCurve_toWire houtput

end Challenge.Bls12381.ProofSupport.ScalarMul
