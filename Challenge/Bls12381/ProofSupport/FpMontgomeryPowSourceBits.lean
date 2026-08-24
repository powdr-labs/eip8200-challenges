import Challenge.Bls12381.ProofSupport.FpMontgomeryPowBits
import Mathlib.Data.FinEnum

set_option warningAsError true

/-! # Exact SHR/AND bit scan used by BLS12-381 `_modexp` -/

namespace Challenge.Bls12381.ProofSupport.Fp

/-- Mirror `and(shr(bit, byte), 1)`: shift right first, mask its low bit, and
interpret the source's nonzero condition as a Boolean. -/
def sourceByteBit (byte : UInt8) (bit : Nat) : Bool :=
  decide ((((byte.toNat >>> bit) &&& 1) : Nat) = 1)

/-- Mirror the source loop that starts at seven, checks bits while the index is
positive, and decrements until the first set bit or the bit-zero fallback. -/
def sourceTopBitLoop (byte : UInt8) : Nat → Nat
  | 0 => 0
  | bit + 1 =>
      if sourceByteBit byte (bit + 1) then bit + 1
      else sourceTopBitLoop byte bit

def sourceTopBit (byte : UInt8) : Nat := sourceTopBitLoop byte 7

/-- Source order for `count` low bits: `count-1, ..., 0`. -/
def sourceBitsDown (byte : UInt8) : Nat → List Bool
  | 0 => []
  | bit + 1 => sourceByteBit byte bit :: sourceBitsDown byte bit

def sourceFirstRemainingBits (byte : UInt8) : List Bool :=
  sourceBitsDown byte (sourceTopBit byte)

def sourceLaterByteBits (byte : UInt8) : List Bool :=
  sourceBitsDown byte 8

/-- Exact source scan after its leading-zero-byte loop. -/
def sourceScanExponent (bytes : List UInt8) : Option (UInt8 × List Bool) :=
  match dropLeadingZeroBytes bytes with
  | [] => none
  | first :: rest => some (first,
      sourceFirstRemainingBits first ++ rest.flatMap sourceLaterByteBits)

/-! Each exhaustive theorem below is a small, kernel-checked certificate over
the 256 possible bytes. This directly pins the source's fixed eight-bit control
flow using ordinary kernel reduction and no axiom. -/

set_option maxRecDepth 4096 in
theorem sourceTopBit_eq_highestSetBit : ∀ byte : UInt8,
    byte.toNat ≠ 0 → sourceTopBit byte = highestSetBit byte := by
  decide

set_option maxRecDepth 4096 in
theorem sourceFirstRemainingBits_eq : ∀ byte : UInt8,
    sourceFirstRemainingBits byte = (significantByteBits byte).tail := by
  decide

set_option maxRecDepth 4096 in
theorem sourceLaterByteBits_eq : ∀ byte : UInt8,
    sourceLaterByteBits byte = byteBits byte := by
  decide

theorem sourceScanExponent_eq (bytes : List UInt8) :
    sourceScanExponent bytes = scanExponent bytes := by
  unfold sourceScanExponent scanExponent
  generalize hdrop : dropLeadingZeroBytes bytes = stripped
  cases stripped with
  | nil => rfl
  | cons first rest =>
      change some (first, sourceFirstRemainingBits first ++
        rest.flatMap sourceLaterByteBits) =
        some (first, (significantByteBits first).tail ++
          rest.flatMap byteBits)
      rw [sourceFirstRemainingBits_eq]
      have hbytes : sourceLaterByteBits = byteBits :=
        funext sourceLaterByteBits_eq
      rw [hbytes]

end Challenge.Bls12381.ProofSupport.Fp
