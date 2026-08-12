import Challenge.Bls12381G2Msm.Reference.Proofs.SourceFp2InvExec
import Challenge.Bls12381G2Add.Reference.Proofs.SourcePointPredicatesExec

set_option warningAsError true

/-! Frozen definitions and exact execution of G2MSM point predicates. -/

namespace Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

abbrev pointPaddingZeroValue :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.pointPaddingZeroValue
abbrev pointValidValue :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.pointValidValue
abbrev pointZeroValue :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.pointZeroValue
abbrev pointPaddingReadState :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.pointPaddingReadState
abbrev pointValidReadState :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.pointValidReadState
abbrev pointZeroReadState :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.pointZeroReadState

def pointPaddingZeroBody : Block Op :=
  match Compilation.referenceCompiledBlock[19]? with
  | some (Stmt.funDef _ _ _ body) => body
  | _ => []

def pointPaddingZeroDecl : FDecl Challenge.EvmProof.modexpExec.toDialect :=
  { params := ["\x00128"], rets := ["\x00129"], body := pointPaddingZeroBody }

theorem lookup_pointPaddingZero : lookupFun fp2Funs "\x0019" =
    some (pointPaddingZeroDecl, fp2Funs) := by rfl

def pointValidBody : Block Op :=
  match Compilation.referenceCompiledBlock[20]? with
  | some (Stmt.funDef _ _ _ body) => body
  | _ => []

def pointValidDecl : FDecl Challenge.EvmProof.modexpExec.toDialect :=
  { params := ["\x00130"], rets := ["\x00131"], body := pointValidBody }

theorem lookup_pointValid : lookupFun fp2Funs "\x0020" =
    some (pointValidDecl, fp2Funs) := by rfl

def pointZeroBody : Block Op :=
  match Compilation.referenceCompiledBlock[21]? with
  | some (Stmt.funDef _ _ _ body) => body
  | _ => []

def pointZeroDecl : FDecl Challenge.EvmProof.modexpExec.toDialect :=
  { params := ["\x00132"], rets := ["\x00133"], body := pointZeroBody }

theorem lookup_pointZero : lookupFun fp2Funs "\x0021" =
    some (pointZeroDecl, fp2Funs) := by rfl

theorem eval_pointPaddingZero (point : U256) (yst : EvmState) :
    Interp.evalExpr Challenge.EvmProof.modexpExec 68 fp2Funs
      [("point", point)] yst (.call "\x0019" [.var "point"]) =
    .ok (.vals [pointPaddingZeroValue yst point]
      (pointPaddingReadState yst point)) := by
  rw [Interp.evalExpr, lookup_pointPaddingZero]
  rfl

theorem eval_pointValid (point : U256) (yst : EvmState) :
    Interp.evalExpr Challenge.EvmProof.modexpExec 68 fp2Funs
      [("point", point)] yst (.call "\x0020" [.var "point"]) =
    .ok (.vals [pointValidValue yst point] (pointValidReadState yst point)) := by
  rw [Interp.evalExpr, lookup_pointValid]
  rfl

theorem eval_pointValid67 (point : U256) (yst : EvmState) :
    Interp.evalExpr Challenge.EvmProof.modexpExec 67 fp2Funs
      [("point", point)] yst (.call "\x0020" [.var "point"]) =
    .ok (.vals [pointValidValue yst point] (pointValidReadState yst point)) := by
  rw [Interp.evalExpr, lookup_pointValid]
  rfl

theorem eval_pointZero (point : U256) (yst : EvmState) :
    Interp.evalExpr Challenge.EvmProof.modexpExec 68 fp2Funs
      [("point", point)] yst (.call "\x0021" [.var "point"]) =
    .ok (.vals [pointZeroValue yst point] (pointZeroReadState yst point)) := by
  rw [Interp.evalExpr, lookup_pointZero]
  rfl

end Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics
