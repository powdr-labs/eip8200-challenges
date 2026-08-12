import Challenge.Bls12381G2Msm.Reference.Proofs.SourceFp2MulExec
import Challenge.Bls12381G2Msm.Reference.Proofs.SourceFp2AddExec
import Challenge.Bls12381G2Add.Reference.Proofs.SourceOnCurveExec

set_option warningAsError true

/-! Frozen G2MSM `onCurve` syntax and state graph. -/

namespace Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def onCurveFuns : FunEnv Challenge.EvmProof.modexpExec.toDialect := fp2MulFuns

def onCurveBody : Block Op :=
  match Compilation.referenceCompiledBlock[18]? with
  | some (Stmt.funDef _ _ _ body) => body
  | _ => []

def onCurveStmt0 : Stmt Op := onCurveBody[0]!
def onCurveStmt1 : Stmt Op := onCurveBody[1]!
def onCurveStmt2 : Stmt Op := onCurveBody[2]!
def onCurveStmt3 : Stmt Op := onCurveBody[3]!
def onCurveStmt4 : Stmt Op := onCurveBody[4]!
def onCurveStmt5 : Stmt Op := onCurveBody[5]!
def onCurveStmt6 : Stmt Op := onCurveBody[6]!
def onCurveStmt7 : Stmt Op := onCurveBody[7]!
def onCurveStmt8 : Stmt Op := onCurveBody[8]!

theorem onCurveBody_eq : onCurveBody =
    [onCurveStmt0, onCurveStmt1, onCurveStmt2, onCurveStmt3,
      onCurveStmt4, onCurveStmt5, onCurveStmt6, onCurveStmt7,
      onCurveStmt8] := by rfl

theorem hoist_onCurveBody :
    hoist Challenge.EvmProof.modexpExec.toDialect onCurveBody = [] := by rfl

def onCurveBodyFuns : FunEnv Challenge.EvmProof.modexpExec.toDialect :=
  [] :: onCurveFuns

theorem onCurveBodyFuns_eq :
    hoist Challenge.EvmProof.modexpExec.toDialect onCurveBody ::
      onCurveFuns = onCurveBodyFuns := by
  rw [hoist_onCurveBody]
  rfl

def onCurveDecl : FDecl Challenge.EvmProof.modexpExec.toDialect :=
  { params := ["\x00125", "\x00126"]
    rets := ["\x00127"]
    body := onCurveBody }

theorem lookup_onCurve : lookupFun onCurveFuns "\x0018" =
    some (onCurveDecl, onCurveFuns) := by rfl

def onCurveInitialEnv (x y : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  [("\x00125", x), ("\x00126", y), ("\x00127", 0)]

abbrev onCurveStateAfterY2 :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.onCurveStateAfterY2
abbrev onCurveStateAfterX2 :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.onCurveStateAfterX2
abbrev onCurveStateAfterX3 :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.onCurveStateAfterX3
abbrev onCurveStateAfterConstant :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.onCurveStateAfterConstant
abbrev onCurveStateAfterAdd :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.onCurveStateAfterAdd
abbrev onCurveFinalState :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.onCurveFinalState
abbrev onCurveResult :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.onCurveResult

end Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics
