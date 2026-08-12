import Challenge.Bls12381G2Add.Reference.Proofs.SourceFp2SubRefinement

set_option warningAsError true

/-!
# Frozen G2ADD `fp2Mul` syntax boundary

The 24-statement Karatsuba schedule is named here without unfolding the
interpreter.  Its scratch-memory and MODEXP phases are proved in later staged
modules so no single elaboration crosses both boundaries.
-/

namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def fp2MulFuns : FunEnv Challenge.EvmProof.modexpExec.toDialect := fp2Funs

def fp2MulBody : Block Op :=
  match Compilation.referenceCompiledBlock[16]? with
  | some (Stmt.funDef _ _ _ body) => body
  | _ => []

def fp2MulStmt0 : Stmt Op := fp2MulBody[0]!
def fp2MulStmt1 : Stmt Op := fp2MulBody[1]!
def fp2MulStmt2 : Stmt Op := fp2MulBody[2]!
def fp2MulStmt3 : Stmt Op := fp2MulBody[3]!
def fp2MulStmt4 : Stmt Op := fp2MulBody[4]!
def fp2MulStmt5 : Stmt Op := fp2MulBody[5]!
def fp2MulStmt6 : Stmt Op := fp2MulBody[6]!
def fp2MulStmt7 : Stmt Op := fp2MulBody[7]!
def fp2MulStmt8 : Stmt Op := fp2MulBody[8]!
def fp2MulStmt9 : Stmt Op := fp2MulBody[9]!
def fp2MulStmt10 : Stmt Op := fp2MulBody[10]!
def fp2MulStmt11 : Stmt Op := fp2MulBody[11]!
def fp2MulStmt12 : Stmt Op := fp2MulBody[12]!
def fp2MulStmt13 : Stmt Op := fp2MulBody[13]!
def fp2MulStmt14 : Stmt Op := fp2MulBody[14]!
def fp2MulStmt15 : Stmt Op := fp2MulBody[15]!
def fp2MulStmt16 : Stmt Op := fp2MulBody[16]!
def fp2MulStmt17 : Stmt Op := fp2MulBody[17]!
def fp2MulStmt18 : Stmt Op := fp2MulBody[18]!
def fp2MulStmt19 : Stmt Op := fp2MulBody[19]!
def fp2MulStmt20 : Stmt Op := fp2MulBody[20]!
def fp2MulStmt21 : Stmt Op := fp2MulBody[21]!
def fp2MulStmt22 : Stmt Op := fp2MulBody[22]!
def fp2MulStmt23 : Stmt Op := fp2MulBody[23]!

theorem fp2MulBody_eq : fp2MulBody =
    [fp2MulStmt0, fp2MulStmt1, fp2MulStmt2, fp2MulStmt3,
      fp2MulStmt4, fp2MulStmt5, fp2MulStmt6, fp2MulStmt7,
      fp2MulStmt8, fp2MulStmt9, fp2MulStmt10, fp2MulStmt11,
      fp2MulStmt12, fp2MulStmt13, fp2MulStmt14, fp2MulStmt15,
      fp2MulStmt16, fp2MulStmt17, fp2MulStmt18, fp2MulStmt19,
      fp2MulStmt20, fp2MulStmt21, fp2MulStmt22, fp2MulStmt23] := by
  rfl

theorem hoist_fp2MulBody :
    hoist Challenge.EvmProof.modexpExec.toDialect fp2MulBody = [] := by
  rfl

def fp2MulBodyFuns : FunEnv Challenge.EvmProof.modexpExec.toDialect :=
  [] :: fp2MulFuns

theorem fp2MulBodyFuns_eq :
    hoist Challenge.EvmProof.modexpExec.toDialect fp2MulBody :: fp2MulFuns =
      fp2MulBodyFuns := by
  rw [hoist_fp2MulBody]
  rfl

def fp2MulDecl : FDecl Challenge.EvmProof.modexpExec.toDialect :=
  { params := ["\x00110", "\x00111", "\x00112"]
    rets := []
    body := fp2MulBody }

theorem lookup_fp2Mul : lookupFun fp2MulFuns "\x0016" =
    some (fp2MulDecl, fp2MulFuns) := by
  rfl

def fp2MulInitialEnv (out a b : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  [("\x00110", out), ("\x00111", a), ("\x00112", b)]

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
