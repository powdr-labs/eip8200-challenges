import Challenge.Bls12381.ProofSupport.FpInv
import Challenge.YulProof.EvmState

set_option warningAsError true

/-! # Stable canonical result words for concrete G1ADD inversion -/

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM
open Challenge.Bls12381.ProofSupport

def fpInvInputLimbs (hi lo : U256) : Fp.Limbs :=
  { hi := YulEvmCompiler.conv hi, lo := YulEvmCompiler.conv lo }

def sourceWordOfUInt256 (word : EvmSemantics.UInt256) : U256 :=
  BitVec.ofNat 256 word.toNat

theorem conv_sourceWordOfUInt256 (word : EvmSemantics.UInt256) :
    YulEvmCompiler.conv (sourceWordOfUInt256 word) = word := by
  apply YulEvmCompiler.u256ext
  simp only [YulEvmCompiler.conv_toNat, sourceWordOfUInt256,
    BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt word.val.isLt

@[irreducible] def fpInvResultWords (hi lo : U256) : U256 × U256 :=
  let result := Fp.invCanonical (fpInvInputLimbs hi lo)
  (sourceWordOfUInt256 result.hi, sourceWordOfUInt256 result.lo)

@[irreducible] def fpInvOutputLimbs (hi lo : U256) : Fp.Limbs :=
  Fp.invCanonical (fpInvInputLimbs hi lo)

theorem fpInvResultWords_hi_conv (hi lo : U256) :
    YulEvmCompiler.conv (fpInvResultWords hi lo).1 =
      (Fp.invCanonical (fpInvInputLimbs hi lo)).hi := by
  unfold fpInvResultWords
  exact conv_sourceWordOfUInt256 _

theorem fpInvResultWords_lo_conv (hi lo : U256) :
    YulEvmCompiler.conv (fpInvResultWords hi lo).2 =
      (Fp.invCanonical (fpInvInputLimbs hi lo)).lo := by
  unfold fpInvResultWords
  exact conv_sourceWordOfUInt256 _

theorem fpInvOutputLimbs_hi (hi lo : U256) :
    (fpInvOutputLimbs hi lo).hi =
      (Fp.invCanonical (fpInvInputLimbs hi lo)).hi := by
  unfold fpInvOutputLimbs
  rfl

theorem fpInvOutputLimbs_lo (hi lo : U256) :
    (fpInvOutputLimbs hi lo).lo =
      (Fp.invCanonical (fpInvInputLimbs hi lo)).lo := by
  unfold fpInvOutputLimbs
  rfl

theorem fpInvResultWords_toOutput_hi (hi lo : U256) :
    YulEvmCompiler.conv (fpInvResultWords hi lo).1 =
      (fpInvOutputLimbs hi lo).hi := by
  rw [fpInvResultWords_hi_conv, fpInvOutputLimbs_hi]

theorem fpInvResultWords_toOutput_lo (hi lo : U256) :
    YulEvmCompiler.conv (fpInvResultWords hi lo).2 =
      (fpInvOutputLimbs hi lo).lo := by
  rw [fpInvResultWords_lo_conv, fpInvOutputLimbs_lo]

/-- The source-facing limb view of the state-free inversion result words. -/
def fpInvResultLimbs (hi lo : U256) : Fp.Limbs :=
  { hi := YulEvmCompiler.conv (fpInvResultWords hi lo).1
    lo := YulEvmCompiler.conv (fpInvResultWords hi lo).2 }

/-- Canonicality transported componentwise from the mathematical inversion
result.  Keeping this as a property avoids constructing an expensive aggregate
equality between the source-word and mathematical limb records. -/
theorem canonical_fpInvResultLimbs (hi lo : U256)
    (hcanonical : Fp.Canonical (fpInvInputLimbs hi lo)) :
    Fp.Canonical (fpInvResultLimbs hi lo) := by
  have hinv := Fp.canonical_invCanonical hcanonical
  constructor
  · change (YulEvmCompiler.conv (fpInvResultWords hi lo).1).toNat < 2 ^ 128
    rw [fpInvResultWords_hi_conv]
    exact hinv.1
  · change (YulEvmCompiler.conv (fpInvResultWords hi lo).2).toNat +
      Challenge.EvmProof.Limbs.radix *
        (YulEvmCompiler.conv (fpInvResultWords hi lo).1).toNat <
      EvmSemantics.Crypto.Bls12381.p
    rw [fpInvResultWords_hi_conv, fpInvResultWords_lo_conv]
    exact hinv.2

theorem value_fpInvResultLimbs (hi lo : U256) :
    Fp.value (fpInvResultLimbs hi lo) =
      Fp.value (Fp.invCanonical (fpInvInputLimbs hi lo)) := by
  change (YulEvmCompiler.conv (fpInvResultWords hi lo).2).toNat +
      Challenge.EvmProof.Limbs.radix *
        (YulEvmCompiler.conv (fpInvResultWords hi lo).1).toNat =
    (Fp.invCanonical (fpInvInputLimbs hi lo)).lo.toNat +
      Challenge.EvmProof.Limbs.radix *
        (Fp.invCanonical (fpInvInputLimbs hi lo)).hi.toNat
  exact congrArg₂
    (fun low high : EvmSemantics.UInt256 =>
      low.toNat + Challenge.EvmProof.Limbs.radix * high.toNat)
    (fpInvResultWords_lo_conv hi lo) (fpInvResultWords_hi_conv hi lo)

/-- Lawful-field meaning transported componentwise from the mathematical
inversion result, again without an aggregate limb equality. -/
theorem fpInvResultLimbs_toLawful (hi lo : U256)
    (hcanonical : Fp.Canonical (fpInvInputLimbs hi lo)) :
    (Fp.value (fpInvResultLimbs hi lo) : PrimeField.LawfulFp) =
      (Fp.value (fpInvInputLimbs hi lo) : PrimeField.LawfulFp)⁻¹ := by
  calc
    (Fp.value (fpInvResultLimbs hi lo) : PrimeField.LawfulFp) =
        (Fp.value (Fp.invCanonical (fpInvInputLimbs hi lo)) :
          PrimeField.LawfulFp) := congrArg
            (fun n : Nat => (n : PrimeField.LawfulFp))
            (value_fpInvResultLimbs hi lo)
    _ = (Fp.value (fpInvInputLimbs hi lo) : PrimeField.LawfulFp)⁻¹ :=
      Fp.lawful_invCanonical hcanonical

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
