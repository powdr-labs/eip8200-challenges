import Challenge.Bls12381.ProofSupport.ScalarMul

set_option warningAsError true

/-!
# BLS12-381 proof-visible subgroup predicates

EIP-2537 requires prime-order subgroup checks for MSM and pairing inputs, but
not for the two addition precompiles.  Keeping the predicates in the family
support layer prevents the individual challenge specifications from drifting
apart on this security-critical validation rule.  These predicates deliberately
use the approved local lawful-affine scalar operation.  The pinned predicates
ultimately depend on the opaque partial `FF.modInv.go`, so a universal kernel
proof connecting them to prime-order group semantics is unavailable; no
equality to those pinned predicates is claimed here.
-/

namespace Challenge.Bls12381.ProofSupport.Subgroup

open EvmSemantics.Crypto

/-- Prime-order G1 membership at the lawful decoded-affine boundary. -/
def g1Affine : G1Affine.Point → Bool
  | .infinity => true
  | point =>
      match ScalarMul.g1 Bls12381.N point with
      | .infinity => true
      | .affine _ _ => false

/-- Prime-order G2 membership at the lawful decoded-affine boundary. -/
def g2Affine : G2Affine.Point → Bool
  | .infinity => true
  | point =>
      match ScalarMul.g2 Bls12381.N point with
      | .infinity => true
      | .affine _ _ => false

/-- Membership in the prime-order G1 subgroup, including infinity. -/
def g1 (point : Bls12381.Point) : Bool :=
  g1Affine (G1Affine.ofWire point)

/-- Membership in the prime-order G2 subgroup, including infinity. -/
def g2 (point : Bls12381.G2Point) : Bool :=
  g2Affine (G2Affine.ofWire point)

theorem g1Affine_eq_true_iff (point : G1Affine.Point) :
    g1Affine point = true ↔
      ScalarMul.g1 Bls12381.N point = G1Affine.infinity := by
  cases point with
  | infinity => simp [g1Affine]
  | affine x y =>
      unfold g1Affine
      cases hresult : ScalarMul.g1 Bls12381.N (.affine x y) <;>
        simp [hresult]

theorem g2Affine_eq_true_iff (point : G2Affine.Point) :
    g2Affine point = true ↔
      ScalarMul.g2 Bls12381.N point = G2Affine.infinity := by
  cases point with
  | infinity => simp [g2Affine]
  | affine x y =>
      unfold g2Affine
      cases hresult : ScalarMul.g2 Bls12381.N (.affine x y) <;>
        simp [hresult]

theorem g1_eq_true_iff (point : Bls12381.Point) :
    g1 point = true ↔
      ScalarMul.g1 Bls12381.N (G1Affine.ofWire point) = G1Affine.infinity :=
  g1Affine_eq_true_iff (G1Affine.ofWire point)

theorem g2_eq_true_iff (point : Bls12381.G2Point) :
    g2 point = true ↔
      ScalarMul.g2 Bls12381.N (G2Affine.ofWire point) = G2Affine.infinity :=
  g2Affine_eq_true_iff (G2Affine.ofWire point)

@[simp] theorem g1_infinity : g1 (.infinity : Bls12381.Point) = true := rfl

@[simp] theorem g2_infinity : g2 (.infinity : Bls12381.G2Point) = true := rfl

end Challenge.Bls12381.ProofSupport.Subgroup
