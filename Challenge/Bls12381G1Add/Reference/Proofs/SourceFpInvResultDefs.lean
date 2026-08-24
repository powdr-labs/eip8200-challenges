import Challenge.Bls12381G1Add.Reference.Proofs.SourceFpInvExec

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

@[irreducible] def fpInvResult (_yst : EvmState) (hi lo : U256) : U256 × U256 :=
  let result := Fp.invCanonical (fpInvInputLimbs hi lo)
  (sourceWordOfUInt256 result.hi, sourceWordOfUInt256 result.lo)

def fpInvFinalState (yst : EvmState) (_hi _lo : U256) : EvmState := yst

def fpInvOutputLimbs (yst : EvmState) (hi lo : U256) : Fp.Limbs :=
  { hi := YulEvmCompiler.conv (fpInvResult yst hi lo).1
    lo := YulEvmCompiler.conv (fpInvResult yst hi lo).2 }

theorem fpInvResult_hi_conv (yst : EvmState) (hi lo : U256) :
    YulEvmCompiler.conv (fpInvResult yst hi lo).1 =
      (Fp.invCanonical (fpInvInputLimbs hi lo)).hi := by
  unfold fpInvResult
  exact conv_sourceWordOfUInt256 _

theorem fpInvResult_lo_conv (yst : EvmState) (hi lo : U256) :
    YulEvmCompiler.conv (fpInvResult yst hi lo).2 =
      (Fp.invCanonical (fpInvInputLimbs hi lo)).lo := by
  unfold fpInvResult
  exact conv_sourceWordOfUInt256 _

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
