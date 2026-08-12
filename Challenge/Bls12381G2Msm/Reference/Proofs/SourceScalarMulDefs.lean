import Challenge.Bls12381G2Msm.Reference.Proofs.SourcePointAddExceptionalRun

set_option warningAsError true

/-! Frozen declaration and loop boundaries for naive 256-bit G2 scalar multiplication. -/

namespace Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def scalarMulFuns : FunEnv Challenge.EvmProof.modexpExec.toDialect :=
  pointAddFuns

def scalarMulBody : Block Op :=
  match Compilation.referenceCompiledBlock[30]? with
  | some (Stmt.funDef _ _ _ body) => body
  | _ => []

def scalarMulStmt0 : Stmt Op := scalarMulBody[0]!
def scalarMulStmt1 : Stmt Op := scalarMulBody[1]!
def scalarMulStmt2 : Stmt Op := scalarMulBody[2]!

def scalarMulLoopInit : Block Op :=
  match scalarMulStmt2 with
  | .forLoop init _ _ _ => init
  | _ => []

def scalarMulLoopCondition : Expr Op :=
  match scalarMulStmt2 with
  | .forLoop _ condition _ _ => condition
  | _ => .lit (.number 0)

def scalarMulLoopPost : Block Op :=
  match scalarMulStmt2 with
  | .forLoop _ _ post _ => post
  | _ => []

def scalarMulLoopBody : Block Op :=
  match scalarMulStmt2 with
  | .forLoop _ _ _ body => body
  | _ => []

def scalarMulDoubleStmt : Stmt Op := scalarMulLoopBody[0]!
def scalarMulAddStmt : Stmt Op := scalarMulLoopBody[1]!

theorem scalarMulBody_eq : scalarMulBody =
    [scalarMulStmt0, scalarMulStmt1, scalarMulStmt2] := by rfl

theorem scalarMulLoopInit_eq : scalarMulLoopInit = [] := by rfl

theorem scalarMulLoopCondition_eq :
    scalarMulLoopCondition = .var "\x00151" := by rfl

theorem scalarMulLoopPost_eq : scalarMulLoopPost =
    [.assign ["\x00151"]
      (.builtin .shr [.lit (.number 1), .var "\x00151"])] := by rfl

theorem scalarMulLoopBody_eq : scalarMulLoopBody =
    [scalarMulDoubleStmt, scalarMulAddStmt] := by rfl

def scalarMulInitBlock : Block Op := [scalarMulStmt0, scalarMulStmt1]

theorem scalarMulBody_eq_init_loop : scalarMulBody =
    scalarMulInitBlock ++ [scalarMulStmt2] := by rfl

theorem hoist_scalarMulBody :
    hoist Challenge.EvmProof.modexpExec.toDialect scalarMulBody = [] := by rfl

def scalarMulBodyFuns : FunEnv Challenge.EvmProof.modexpExec.toDialect :=
  [] :: scalarMulFuns

theorem scalarMulBodyFuns_eq :
    hoist Challenge.EvmProof.modexpExec.toDialect scalarMulBody ::
      scalarMulFuns = scalarMulBodyFuns := by
  rw [hoist_scalarMulBody]
  rfl

def scalarMulDecl : FDecl Challenge.EvmProof.modexpExec.toDialect :=
  { params := ["\x00148", "\x00149", "\x00150"]
    rets := []
    body := scalarMulBody }

theorem lookup_scalarMul : lookupFun scalarMulFuns "\x0030" =
    some (scalarMulDecl, scalarMulFuns) := by rfl

def scalarMulInitialEnv (scalar point out : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  [("\x00148", scalar), ("\x00149", point), ("\x00150", out)]

end Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics
