import Challenge.Bls12381G2Msm.Reference.Proofs.Compilation
import Challenge.Bls12381G2Add.Reference.Proofs.SourceFpCore

set_option warningAsError true

/-!
# First frozen G2MSM Fp evaluator slice

The normalized G2MSM block uses different fresh local names from G2ADD because
it contains six additional top-level helpers.  The pure value graph is shared,
while these small evaluator endpoints are checked locally against the exact
G2MSM frozen block.
-/

namespace Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics

open EvmSemantics
open YulSemantics YulSemantics.EVM
open Challenge.EvmProof
open Challenge.Bls12381G2Msm.Reference.Proofs.Compilation

abbrev fpGeModulusValue :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fpGeModulusValue
abbrev fpZeroValue :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fpZeroValue

export Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
  (conv_fpGeModulusValue conv_fpZeroValue)

theorem eval_fpGeModulus (hi lo : U256) (yst : EvmState) :
    Interp.evalExpr modexpExec 64
      [hoist modexpExec.toDialect referenceCompiledBlock]
      [("hi", hi), ("lo", lo)] yst
      (.call "\x000" [.var "hi", .var "lo"]) =
    .ok (.vals [fpGeModulusValue hi lo] yst) := by
  rw [Interp.evalExpr]
  rfl

theorem eval_fpZero (hi lo : U256) (yst : EvmState) :
    Interp.evalExpr modexpExec 64
      [hoist modexpExec.toDialect referenceCompiledBlock]
      [("hi", hi), ("lo", lo)] yst
      (.call "\x002" [.var "hi", .var "lo"]) =
    .ok (.vals [fpZeroValue hi lo] yst) := by
  rw [Interp.evalExpr]
  rfl

end Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics
