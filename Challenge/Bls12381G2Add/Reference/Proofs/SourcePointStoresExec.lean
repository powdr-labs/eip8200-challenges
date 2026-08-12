import Challenge.Bls12381G2Add.Reference.Proofs.SourcePointStoresDefs

set_option warningAsError true

/-! # Execution of frozen G2ADD point output helpers -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

theorem eval_clearPoint (yst : EvmState) :
    Interp.evalExpr Challenge.EvmProof.modexpExec 68 fp2Funs [] yst
      (.call "\x0022" []) = .ok (.vals [] (clearPointState yst)) := by
  rw [Interp.evalExpr, lookup_clearPoint]
  rfl

theorem eval_copyPoint (point : U256) (yst : EvmState) :
    Interp.evalExpr Challenge.EvmProof.modexpExec 68 fp2Funs
      [("point", point)] yst (.call "\x0023" [.var "point"]) =
    .ok (.vals [] (copyPointState yst point)) := by
  rw [Interp.evalExpr, lookup_copyPoint]
  rfl

theorem eval_storePoint (x y : U256) (yst : EvmState) :
    Interp.evalExpr Challenge.EvmProof.modexpExec 68 fp2Funs
      [("x", x), ("y", y)] yst
      (.call "\x0024" [.var "x", .var "y"]) =
    .ok (.vals [] (storePointState yst x y)) := by
  rw [Interp.evalExpr, lookup_storePoint]
  rfl

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
