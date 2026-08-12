import Challenge.Bls12381.ProofSupport.FpAddSub
import YulEvmCompiler.Value

set_option warningAsError true

/-! Word-level value and lawful-limb bridge for `fpGeModulus`. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics.EVM

def fpGeModulusValue (hi lo : U256) : U256 :=
  b2w (BitVec.ult
      (BitVec.ofNat 256 34565483545414906068789196026815425751) hi) |||
    (b2w (hi = BitVec.ofNat 256
      34565483545414906068789196026815425751) &&&
      b2w (b2w (BitVec.ult lo
        (BitVec.ofNat 256
          45442060874369865957053122457065728162598490762543039060009208264153100167851)) = 0))

theorem conv_fpGeModulusValue (hi lo : U256) :
    YulEvmCompiler.conv (fpGeModulusValue hi lo) =
    Challenge.Bls12381.ProofSupport.Fp.addNeedsCorrection
      { hi := YulEvmCompiler.conv hi, lo := YulEvmCompiler.conv lo } := by
  have hhi : YulEvmCompiler.conv (BitVec.ofNat 256
      34565483545414906068789196026815425751) =
      Challenge.Bls12381.ProofSupport.Fp.modulusHi := by
    rw [YulEvmCompiler.conv_eq_ofNat]
    rfl
  have hlo : YulEvmCompiler.conv (BitVec.ofNat 256
      45442060874369865957053122457065728162598490762543039060009208264153100167851) =
      Challenge.Bls12381.ProofSupport.Fp.modulusLo := by
    rw [YulEvmCompiler.conv_eq_ofNat]
    rfl
  unfold fpGeModulusValue
  rw [YulEvmCompiler.conv_or, YulEvmCompiler.conv_gt,
    YulEvmCompiler.conv_and, YulEvmCompiler.conv_eq,
    YulEvmCompiler.conv_iszero, YulEvmCompiler.conv_lt, hhi, hlo]
  rfl

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
