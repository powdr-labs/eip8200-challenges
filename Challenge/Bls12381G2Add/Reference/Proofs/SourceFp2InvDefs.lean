import Challenge.Bls12381G2Add.Reference.Proofs.SourceFp2MulCorrect

set_option warningAsError true
/-! # Frozen G2ADD `fp2Inv` syntax boundary -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
open YulSemantics YulSemantics.EVM

def fp2InvFuns : FunEnv Challenge.EvmProof.modexpExec.toDialect :=
  [hoist Challenge.EvmProof.modexpExec.toDialect
    Compilation.referenceCompiledBlock]

def fp2InvBody : Block Op :=
  match Compilation.referenceCompiledBlock[17]? with
  | some (Stmt.funDef _ _ _ body) => body
  | _ => []

def fp2InvStmt0 : Stmt Op := fp2InvBody[0]!
def fp2InvStmt1 : Stmt Op := fp2InvBody[1]!
def fp2InvStmt2 : Stmt Op := fp2InvBody[2]!
def fp2InvStmt3 : Stmt Op := fp2InvBody[3]!
def fp2InvStmt4 : Stmt Op := fp2InvBody[4]!
def fp2InvStmt5 : Stmt Op := fp2InvBody[5]!
def fp2InvStmt6 : Stmt Op := fp2InvBody[6]!
def fp2InvStmt7 : Stmt Op := fp2InvBody[7]!
def fp2InvStmt8 : Stmt Op := fp2InvBody[8]!
def fp2InvStmt9 : Stmt Op := fp2InvBody[9]!
def fp2InvStmt10 : Stmt Op := fp2InvBody[10]!
def fp2InvStmt11 : Stmt Op := fp2InvBody[11]!
def fp2InvStmt12 : Stmt Op := fp2InvBody[12]!
def fp2InvStmt13 : Stmt Op := fp2InvBody[13]!
def fp2InvStmt14 : Stmt Op := fp2InvBody[14]!
def fp2InvStmt15 : Stmt Op := fp2InvBody[15]!
def fp2InvStmt16 : Stmt Op := fp2InvBody[16]!

theorem fp2InvBody_eq : fp2InvBody =
    [fp2InvStmt0, fp2InvStmt1, fp2InvStmt2, fp2InvStmt3,
      fp2InvStmt4, fp2InvStmt5, fp2InvStmt6, fp2InvStmt7,
      fp2InvStmt8, fp2InvStmt9, fp2InvStmt10, fp2InvStmt11,
      fp2InvStmt12, fp2InvStmt13, fp2InvStmt14, fp2InvStmt15,
      fp2InvStmt16] := by rfl

theorem hoist_fp2InvBody :
    hoist Challenge.EvmProof.modexpExec.toDialect fp2InvBody = [] := by rfl

def fp2InvBodyFuns : FunEnv Challenge.EvmProof.modexpExec.toDialect :=
  [] :: fp2InvFuns

theorem fp2InvBodyFuns_eq :
    hoist Challenge.EvmProof.modexpExec.toDialect fp2InvBody :: fp2InvFuns =
      fp2InvBodyFuns := by rw [hoist_fp2InvBody]; rfl

def fp2InvDecl : FDecl Challenge.EvmProof.modexpExec.toDialect :=
  { params := ["\x00115", "\x00116"]
    rets := []
    body := fp2InvBody }

theorem lookup_fp2Inv : lookupFun fp2InvFuns "\x0017" =
    some (fp2InvDecl, fp2InvFuns) := by rfl

def fp2InvInitialEnv (out a : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  [("\x00115", out), ("\x00116", a)]

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
