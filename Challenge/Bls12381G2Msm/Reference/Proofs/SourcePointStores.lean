import Challenge.Bls12381G2Msm.Reference.Proofs.SourcePointPredicates
import Challenge.Bls12381G2Add.Reference.Proofs.SourcePointStoresExec

set_option warningAsError true

/-! Frozen definitions and exact execution of G2MSM point output helpers. -/

namespace Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

abbrev clearPointState :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.clearPointState
abbrev copyPointState :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.copyPointState
abbrev storePointState :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.storePointState

def clearPointBody : Block Op :=
  match Compilation.referenceCompiledBlock[22]? with
  | some (Stmt.funDef _ _ _ body) => body
  | _ => []

def clearPointDecl : FDecl Challenge.EvmProof.modexpExec.toDialect :=
  { params := [], rets := [], body := clearPointBody }

theorem lookup_clearPoint : lookupFun fp2Funs "\x0022" =
    some (clearPointDecl, fp2Funs) := by rfl

def copyPointBody : Block Op :=
  match Compilation.referenceCompiledBlock[23]? with
  | some (Stmt.funDef _ _ _ body) => body
  | _ => []

def copyPointDecl : FDecl Challenge.EvmProof.modexpExec.toDialect :=
  { params := ["\x00134"], rets := [], body := copyPointBody }

theorem lookup_copyPoint : lookupFun fp2Funs "\x0023" =
    some (copyPointDecl, fp2Funs) := by rfl

def storePointBody : Block Op :=
  match Compilation.referenceCompiledBlock[24]? with
  | some (Stmt.funDef _ _ _ body) => body
  | _ => []

def storePointDecl : FDecl Challenge.EvmProof.modexpExec.toDialect :=
  { params := ["\x00135", "\x00136"], rets := [], body := storePointBody }

theorem lookup_storePoint : lookupFun fp2Funs "\x0024" =
    some (storePointDecl, fp2Funs) := by rfl

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

end Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics
