import Challenge.Bls12381.ProofSupport.FpMontgomeryPowSourceBits
import Challenge.Bls12381.ProofSupport.FpMontgomeryLawful

set_option warningAsError true

/-! # Source-faithful Montgomery exponentiation loop -/

namespace Challenge.Bls12381.ProofSupport.Fp

/-- One `_modexp` bit iteration: square first, then multiply by the Montgomery
base exactly when the current high-to-low exponent bit is set. -/
def montgomeryBitStep (baseM acc : Limbs) (bit : Bool) : Limbs :=
  let squared := montMul2 acc acc
  if bit then montMul2 squared baseM else squared

/-- Process the remaining exponent bits in source order. -/
def foldMontgomeryBits (baseM : Limbs) : Limbs → List Bool → Limbs
  | acc, [] => acc
  | acc, bit :: bits =>
      foldMontgomeryBits baseM (montgomeryBitStep baseM acc bit) bits

/-- Source `_modexp` control flow over a big-endian exponent byte list. The
first significant one bit initializes the accumulator to `aM`; subsequent
bits execute square-then-conditional-multiply. -/
def montgomeryPow (base : Limbs) (exponent : List UInt8) : Limbs :=
  let baseM := montgomeryEncode base
  match sourceScanExponent exponent with
  | none => montgomeryOne
  | some (_, bits) => foldMontgomeryBits baseM baseM bits

theorem canonical_montgomeryBitStep {baseM acc : Limbs}
    (hbaseM : Canonical baseM) (hacc : Canonical acc) (bit : Bool) :
    Canonical (montgomeryBitStep baseM acc bit) := by
  cases bit <;> simp [montgomeryBitStep, canonical_montMul2, hbaseM, hacc]

theorem canonical_foldMontgomeryBits {baseM acc : Limbs}
    (hbaseM : Canonical baseM) (hacc : Canonical acc) (bits : List Bool) :
    Canonical (foldMontgomeryBits baseM acc bits) := by
  induction bits generalizing acc with
  | nil => exact hacc
  | cons bit bits ih =>
      exact ih (canonical_montgomeryBitStep hbaseM hacc bit)

theorem canonical_montgomeryPow {base : Limbs} (hbase : Canonical base)
    (exponent : List UInt8) : Canonical (montgomeryPow base exponent) := by
  unfold montgomeryPow
  split
  · exact canonical_montgomeryOne
  · exact canonical_foldMontgomeryBits
      (canonical_montgomeryEncode hbase)
      (canonical_montgomeryEncode hbase) _

end Challenge.Bls12381.ProofSupport.Fp
