import Mathlib.Algebra.Ring.Defs

set_option warningAsError true

/-! # Small constant-first polynomial evaluator for map-to-curve proofs -/

namespace Challenge.Bls12381.ProofSupport.MapPolynomial

variable {R : Type} [CommSemiring R]

/-- Evaluate a constant-first coefficient list. -/
def eval : List R → R → R
  | [], _ => 0
  | coefficient :: coefficients, x =>
      coefficient + x * eval coefficients x

/-- Homogeneous evaluation of a constant-first polynomial at `N / D`.
The result is the numerator after clearing `D ^ degree`. -/
def evalHom : List R → R → R → R
  | [], _, _ => 0
  | coefficient :: coefficients, numerator, denominator =>
      coefficient * denominator ^ coefficients.length +
        numerator * evalHom coefficients numerator denominator

/-- Coefficientwise addition, padding the shorter list with zeroes. -/
def add : List R → List R → List R
  | [], right => right
  | left, [] => left
  | a :: as, b :: bs => (a + b) :: add as bs

/-- Scale every coefficient. -/
def scale (a : R) : List R → List R
  | [] => []
  | b :: bs => (a * b) :: scale a bs

/-- Constant-first coefficient convolution. -/
def mul : List R → List R → List R
  | [], _ => []
  | _ :: _, [] => []
  | a :: as, right => add (scale a right) (0 :: mul as right)

/-- Natural power under coefficient convolution. -/
def pow : List R → Nat → List R
  | _, 0 => [1]
  | coefficients, n + 1 => mul coefficients (pow coefficients n)

end Challenge.Bls12381.ProofSupport.MapPolynomial
