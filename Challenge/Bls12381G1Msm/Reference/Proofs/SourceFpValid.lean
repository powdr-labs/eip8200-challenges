import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePredicates

set_option warningAsError true

/-! Executable semantics of the nested `fpValid` predicate. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM
open Challenge.EvmProof

theorem eval_fpValid (hi lo : U256) (yst : EvmState) :
    Interp.evalExpr modexpExec 64 sourceFuns
      [("hi", hi), ("lo", lo)] yst
      (.call "\x001" [.var "hi", .var "lo"]) =
    .ok (.vals [fpValidValue hi lo] yst) := by
  rw [Interp.evalExpr]
  rfl

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
