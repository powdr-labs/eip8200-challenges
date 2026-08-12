import Challenge.Bls12381G1Msm.Reference.Proofs.SourceFullMulCall

set_option warningAsError true

/-! Frozen declaration boundary for the G1MSM `fpMul` helper. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM
open Challenge.Bls12381G1Msm.Reference.Proofs.Compilation

def fpMulBody : Block Op :=
  match referenceBackendBlock[6]? with
  | some (Stmt.funDef _ _ _ body) => body
  | _ => []

def fpMulStmt0 : Stmt Op := fpMulBody[0]!
def fpMulStmt1 : Stmt Op := fpMulBody[1]!
def fpMulStmt2 : Stmt Op := fpMulBody[2]!
def fpMulStmt3 : Stmt Op := fpMulBody[3]!
def fpMulStmt4 : Stmt Op := fpMulBody[4]!
def fpMulStmt5 : Stmt Op := fpMulBody[5]!
def fpMulStmt6 : Stmt Op := fpMulBody[6]!
def fpMulStmt7 : Stmt Op := fpMulBody[7]!
def fpMulStmt8 : Stmt Op := fpMulBody[8]!

theorem fpMulBody_eq : fpMulBody =
    [fpMulStmt0, fpMulStmt1, fpMulStmt2, fpMulStmt3, fpMulStmt4,
      fpMulStmt5, fpMulStmt6, fpMulStmt7, fpMulStmt8] := by
  rfl

theorem fpMulBody_length : fpMulBody.length = 9 := by
  rfl

theorem hoist_fpMulBody :
    hoist Challenge.EvmProof.modexpExec.toDialect fpMulBody = [] := by
  rfl

def fpMulBodyFuns : FunEnv Challenge.EvmProof.modexpExec.toDialect :=
  [] :: sourceFuns

def fpMulDecl : FDecl Challenge.EvmProof.modexpExec.toDialect :=
  { params := ["\x0073", "\x0074", "\x0075", "\x0076"]
    rets := ["\x0077", "\x0078"]
    body := fpMulBody }

theorem lookup_fpMul : lookupFun sourceFuns "\x009" =
    some (fpMulDecl, sourceFuns) := by
  rfl

def fpMulInitialEnv (ahi alo bhi blo : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  [("\x0073", ahi), ("\x0074", alo), ("\x0075", bhi), ("\x0076", blo),
   ("\x0077", 0), ("\x0078", 0)]

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
