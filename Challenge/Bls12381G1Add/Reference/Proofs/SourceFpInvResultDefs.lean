import Challenge.Bls12381.ProofSupport.FpInv
import Challenge.YulProof.EvmState

set_option warningAsError true

/-! # Stable canonical result words for native G1ADD inversion -/

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

/-- Compatibility wrapper for state graphs written before inversion became
stack-only.  New proofs should use `fpInvResultWords`. -/
def fpInvResult (_yst : EvmState) (hi lo : U256) : U256 × U256 :=
  fpInvResultWords hi lo

def fpInvFinalState (yst : EvmState) (_hi _lo : U256) : EvmState := yst

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

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
