import Challenge.Bls12381G1Msm.Reference.Proofs.SourceFpMulRefinement

set_option warningAsError true

/-! Frozen declaration boundary for the G1MSM `onCurve` helper. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM
open Challenge.Bls12381G1Msm.Reference.Proofs.Compilation

def onCurveBody : Block Op :=
  match referenceBackendBlock[7]? with
  | some (Stmt.funDef _ _ _ body) => body
  | _ => []

def onCurveStmt0 : Stmt Op := onCurveBody[0]!
def onCurveStmt1 : Stmt Op := onCurveBody[1]!
def onCurveStmt2 : Stmt Op := onCurveBody[2]!
def onCurveStmt3 : Stmt Op := onCurveBody[3]!
def onCurveStmt4 : Stmt Op := onCurveBody[4]!

theorem onCurveBody_eq : onCurveBody =
    [onCurveStmt0, onCurveStmt1, onCurveStmt2, onCurveStmt3,
      onCurveStmt4] := by
  rfl

theorem onCurveBody_length : onCurveBody.length = 5 := by
  rfl

theorem hoist_onCurveBody :
    hoist Challenge.EvmProof.modexpExec.toDialect onCurveBody = [] := by
  rfl

def onCurveBodyFuns : FunEnv Challenge.EvmProof.modexpExec.toDialect :=
  [] :: sourceFuns

def onCurveDecl : FDecl Challenge.EvmProof.modexpExec.toDialect :=
  { params := ["\x0086", "\x0087", "\x0088", "\x0089"]
    rets := ["\x0090"]
    body := onCurveBody }

theorem lookup_onCurve : lookupFun sourceFuns "\x0011" =
    some (onCurveDecl, sourceFuns) := by
  rfl

def onCurveInitialEnv (xhi xlo yhi ylo : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  [("\x0086", xhi), ("\x0087", xlo), ("\x0088", yhi), ("\x0089", ylo),
   ("\x0090", 0)]

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
