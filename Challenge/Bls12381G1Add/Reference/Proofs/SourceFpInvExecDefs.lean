import Challenge.Bls12381G1Add.Reference.Proofs.SourceStore

set_option warningAsError true

/-! # Frozen G1ADD `fpInv` body -/

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def fpInvFuns : FunEnv Challenge.EvmProof.modexpExec.toDialect :=
  [hoist Challenge.EvmProof.modexpExec.toDialect
    Compilation.referenceCompiledBlock]

def fpInvBody : Block Op :=
  match Compilation.referenceCompiledBlock[10]? with
  | some (Stmt.funDef _ _ _ body) => body
  | _ => []

def fpInvStmt0 : Stmt Op := fpInvBody[0]!
def fpInvStmt1 : Stmt Op := fpInvBody[1]!
def fpInvStmt2 : Stmt Op := fpInvBody[2]!
def fpInvStmt3 : Stmt Op := fpInvBody[3]!
def fpInvStmt4 : Stmt Op := fpInvBody[4]!
def fpInvStmt5 : Stmt Op := fpInvBody[5]!
def fpInvStmt6 : Stmt Op := fpInvBody[6]!
def fpInvStmt7 : Stmt Op := fpInvBody[7]!
def fpInvStmt8 : Stmt Op := fpInvBody[8]!

/-- The frozen inversion helper has the exact nine-statement source schedule. -/
theorem fpInvBody_eq : fpInvBody =
    [fpInvStmt0, fpInvStmt1, fpInvStmt2, fpInvStmt3, fpInvStmt4,
      fpInvStmt5, fpInvStmt6, fpInvStmt7, fpInvStmt8] := by
  rfl

theorem hoist_fpInvBody :
    hoist Challenge.EvmProof.modexpExec.toDialect fpInvBody = [] := by
  rfl

def fpInvBodyFuns : FunEnv Challenge.EvmProof.modexpExec.toDialect :=
  [] :: fpInvFuns

theorem fpInvBodyFuns_eq :
    hoist Challenge.EvmProof.modexpExec.toDialect fpInvBody :: fpInvFuns =
      fpInvBodyFuns := by
  rw [hoist_fpInvBody]
  rfl

def fpInvDecl : FDecl Challenge.EvmProof.modexpExec.toDialect :=
  { params := ["\x0077", "\x0078"]
    rets := ["\x0079", "\x0080"]
    body := fpInvBody }

theorem lookup_fpInv : lookupFun fpInvFuns "\x0010" =
    some (fpInvDecl, fpInvFuns) := by
  rfl

def fpInvInitialEnv (hi lo : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  [("\x0077", hi), ("\x0078", lo), ("\x0079", 0), ("\x0080", 0)]

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
