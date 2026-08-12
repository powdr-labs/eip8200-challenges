import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddDefs

set_option warningAsError true

/-! Frozen declaration and loop boundaries for the naive 256-bit scalar multiplier. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM
open Challenge.Bls12381G1Msm.Reference.Proofs.Compilation

def scalarMulBody : Block Op :=
  match referenceBackendBlock[10]? with
  | some (Stmt.funDef _ _ _ body) => body
  | _ => []

def scalarMulStmt0 : Stmt Op := scalarMulBody[0]!
def scalarMulStmt1 : Stmt Op := scalarMulBody[1]!
def scalarMulStmt2 : Stmt Op := scalarMulBody[2]!
def scalarMulStmt3 : Stmt Op := scalarMulBody[3]!
def scalarMulStmt4 : Stmt Op := scalarMulBody[4]!
def scalarMulStmt5 : Stmt Op := scalarMulBody[5]!
def scalarMulStmt6 : Stmt Op := scalarMulBody[6]!
def scalarMulStmt7 : Stmt Op := scalarMulBody[7]!

def scalarMulLoopInit : Block Op :=
  match scalarMulStmt7 with
  | .forLoop init _ _ _ => init
  | _ => []

def scalarMulLoopCondition : Expr Op :=
  match scalarMulStmt7 with
  | .forLoop _ condition _ _ => condition
  | _ => .lit (.number 0)

def scalarMulLoopPost : Block Op :=
  match scalarMulStmt7 with
  | .forLoop _ _ post _ => post
  | _ => []

def scalarMulLoopBody : Block Op :=
  match scalarMulStmt7 with
  | .forLoop _ _ _ body => body
  | _ => []

def scalarMulDoubleStmt : Stmt Op := scalarMulLoopBody[0]!
def scalarMulAddStmt : Stmt Op := scalarMulLoopBody[1]!

theorem scalarMulBody_eq : scalarMulBody =
    [scalarMulStmt0, scalarMulStmt1, scalarMulStmt2, scalarMulStmt3,
     scalarMulStmt4, scalarMulStmt5, scalarMulStmt6, scalarMulStmt7] := by rfl

theorem scalarMulLoopInit_eq : scalarMulLoopInit = [] := by rfl

theorem scalarMulLoopCondition_eq : scalarMulLoopCondition = .var "\x00145" := by
  rfl

theorem scalarMulLoopPost_eq : scalarMulLoopPost =
    [.assign ["\x00145"]
      (.builtin .shr [.lit (.number 1), .var "\x00145"])] := by rfl

theorem scalarMulLoopBody_eq : scalarMulLoopBody =
    [scalarMulDoubleStmt, scalarMulAddStmt] := by rfl

def scalarMulInitBlock : Block Op :=
  [scalarMulStmt0, scalarMulStmt1, scalarMulStmt2, scalarMulStmt3,
    scalarMulStmt4, scalarMulStmt5, scalarMulStmt6]

theorem scalarMulBody_eq_init_loop : scalarMulBody =
    scalarMulInitBlock ++ [scalarMulStmt7] := by rfl

theorem hoist_scalarMulBody :
    hoist Challenge.EvmProof.modexpExec.toDialect scalarMulBody = [] := by rfl

def scalarMulBodyFuns : FunEnv Challenge.EvmProof.modexpExec.toDialect :=
  [] :: sourceFuns

def scalarMulDecl : FDecl Challenge.EvmProof.modexpExec.toDialect :=
  { params := ["\x00142", "\x00143", "\x00144"]
    rets := []
    body := scalarMulBody }

theorem lookup_scalarMul : lookupFun sourceFuns "\x0017" =
    some (scalarMulDecl, sourceFuns) := by rfl

def scalarMulInitialEnv (scalar point out : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  [("\x00142", scalar), ("\x00143", point), ("\x00144", out)]

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
