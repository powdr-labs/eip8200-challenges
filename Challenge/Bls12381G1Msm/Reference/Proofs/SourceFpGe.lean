import Challenge.Bls12381G1Msm.Reference.Proofs.SourceFpGeDefs
import Challenge.Bls12381G1Msm.Reference.Proofs.SourceFpGeValue

set_option warningAsError true

/-! Executable semantics of the frozen G1MSM `fpGeModulus` helper. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM
open Challenge.EvmProof

theorem eval_fpGeModulus (hi lo : U256) (yst : EvmState) :
    Interp.evalExpr modexpExec 64 sourceFuns
      [("hi", hi), ("lo", lo)] yst
      (.call "\x000" [.var "hi", .var "lo"]) =
    .ok (.vals [fpGeModulusValue hi lo] yst) := by
  simp [Interp.evalExpr, Interp.evalArgs, Interp.execStmt, Interp.execStmts,
    lookup_fpGe, fpGeDecl, fpGeBody_eq, fpGeStmt,
    modexpExec, modexpBuiltinFn, stepOp, bin, un, fpGeModulusValue,
    Dialect.zero, VEnv.get, VEnv.setMany, VEnv.set, bindZeros, restore]
  rfl

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
