import Challenge.Bls12381G1Msm.Reference.Proofs.SourceOnCurveRefinement

set_option warningAsError true

/-! Frozen declaration boundary for the G1MSM `pointInfinity` helper. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM
open Challenge.Bls12381G1Msm.Reference.Proofs.Compilation

def pointInfinityBody : Block Op :=
  match referenceBackendBlock[8]? with
  | some (Stmt.funDef _ _ _ body) => body
  | _ => []

def pointInfinityStmt : Stmt Op := pointInfinityBody[0]!

theorem pointInfinityBody_eq : pointInfinityBody = [pointInfinityStmt] := by
  rfl

theorem hoist_pointInfinityBody :
    hoist Challenge.EvmProof.modexpExec.toDialect pointInfinityBody = [] := by
  rfl

def pointInfinityBodyFuns : FunEnv Challenge.EvmProof.modexpExec.toDialect :=
  [] :: sourceFuns

def pointInfinityDecl : FDecl Challenge.EvmProof.modexpExec.toDialect :=
  { params := ["\x00105"]
    rets := ["\x00106"]
    body := pointInfinityBody }

theorem lookup_pointInfinity : lookupFun sourceFuns "\x0015" =
    some (pointInfinityDecl, sourceFuns) := by
  rfl

def pointInfinityInitialEnv (ptr : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  [("\x00105", ptr), ("\x00106", 0)]

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
