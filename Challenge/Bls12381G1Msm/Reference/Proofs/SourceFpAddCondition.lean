import Challenge.Bls12381G1Msm.Reference.Proofs.SourceFpAddHigh
import Challenge.Bls12381G1Msm.Reference.Proofs.SourceFpGeValue

set_option warningAsError true

/-! Opaque correction-condition evaluation for staged G1MSM `fpAdd`. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM
open Challenge.EvmProof

theorem eval_fpAddCondition (ahi alo bhi blo : U256) (yst : EvmState) :
    Interp.evalExpr modexpExec 32 fpAddBodyFuns
      (fpAddHighEnv ahi alo bhi blo) yst
      (.call "\x000" [.var "\x0038", .var "\x0039"]) =
    .ok (.vals [fpGeModulusValue (fpAddHighValue ahi alo bhi blo)
      (fpAddLowValue alo blo)] yst) := by
  rw [Interp.evalExpr]
  rfl

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
