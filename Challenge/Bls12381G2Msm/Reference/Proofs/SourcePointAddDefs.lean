import Challenge.Bls12381G2Msm.Reference.Proofs.SourceMsmPointHelpers

set_option warningAsError true

/-! Frozen declaration and branch boundaries for G2MSM `pointAdd`. -/

namespace Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def pointAddFuns : FunEnv Challenge.EvmProof.modexpExec.toDialect := fp2Funs

def pointAddBody : Block Op :=
  match Compilation.referenceCompiledBlock[29]? with
  | some (Stmt.funDef _ _ _ body) => body
  | _ => []

def pointAddStmt0 : Stmt Op := pointAddBody[0]!
def pointAddStmt1 : Stmt Op := pointAddBody[1]!
def pointAddStmt2 : Stmt Op := pointAddBody[2]!
def pointAddStmt3 : Stmt Op := pointAddBody[3]!
def pointAddStmt4 : Stmt Op := pointAddBody[4]!
def pointAddStmt5 : Stmt Op := pointAddBody[5]!
def pointAddStmt6 : Stmt Op := pointAddBody[6]!
def pointAddStmt7 : Stmt Op := pointAddBody[7]!
def pointAddStmt8 : Stmt Op := pointAddBody[8]!
def pointAddStmt9 : Stmt Op := pointAddBody[9]!
def pointAddStmt10 : Stmt Op := pointAddBody[10]!
def pointAddStmt11 : Stmt Op := pointAddBody[11]!
def pointAddStmt12 : Stmt Op := pointAddBody[12]!
def pointAddStmt13 : Stmt Op := pointAddBody[13]!

theorem pointAddBody_eq : pointAddBody =
    [pointAddStmt0, pointAddStmt1, pointAddStmt2, pointAddStmt3,
      pointAddStmt4, pointAddStmt5, pointAddStmt6, pointAddStmt7,
      pointAddStmt8, pointAddStmt9, pointAddStmt10, pointAddStmt11,
      pointAddStmt12, pointAddStmt13] := by rfl

theorem hoist_pointAddBody :
    hoist Challenge.EvmProof.modexpExec.toDialect pointAddBody = [] := by rfl

def pointAddBodyFuns : FunEnv Challenge.EvmProof.modexpExec.toDialect :=
  [] :: pointAddFuns

theorem pointAddBodyFuns_eq :
    hoist Challenge.EvmProof.modexpExec.toDialect pointAddBody :: pointAddFuns =
      pointAddBodyFuns := by
  rw [hoist_pointAddBody]
  rfl

def pointAddDecl : FDecl Challenge.EvmProof.modexpExec.toDialect :=
  { params := ["\x00145", "\x00146", "\x00147"]
    rets := []
    body := pointAddBody }

theorem lookup_pointAdd : lookupFun pointAddFuns "\x0029" =
    some (pointAddDecl, pointAddFuns) := by rfl

def pointAddInitialEnv (out left right : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  [("\x00145", out), ("\x00146", left), ("\x00147", right)]

def pointAddLeftInfinityCondition : Expr Op :=
  match pointAddStmt3 with
  | .cond condition _ => condition
  | _ => .lit (.number 0)

def pointAddLeftInfinityBody : Block Op :=
  match pointAddStmt3 with
  | .cond _ body => body
  | _ => []

theorem pointAddStmt3_eq : pointAddStmt3 =
    .cond pointAddLeftInfinityCondition pointAddLeftInfinityBody := by rfl

theorem pointAddLeftInfinityCondition_eq : pointAddLeftInfinityCondition =
    .call "\x0028" [.builtin .mload [.lit (.number 1952)]] := by rfl

theorem pointAddLeftInfinityBody_eq : pointAddLeftInfinityBody =
    [.exprStmt (.call "\x0027"
      [.builtin .mload [.lit (.number 1920)],
        .builtin .mload [.lit (.number 1984)]]), .leave] := by rfl

def pointAddRightInfinityCondition : Expr Op :=
  match pointAddStmt4 with
  | .cond condition _ => condition
  | _ => .lit (.number 0)

def pointAddRightInfinityBody : Block Op :=
  match pointAddStmt4 with
  | .cond _ body => body
  | _ => []

theorem pointAddStmt4_eq : pointAddStmt4 =
    .cond pointAddRightInfinityCondition pointAddRightInfinityBody := by rfl

theorem pointAddRightInfinityCondition_eq : pointAddRightInfinityCondition =
    .call "\x0028" [.builtin .mload [.lit (.number 1984)]] := by rfl

theorem pointAddRightInfinityBody_eq : pointAddRightInfinityBody =
    [.exprStmt (.call "\x0027"
      [.builtin .mload [.lit (.number 1920)],
        .builtin .mload [.lit (.number 1952)]]), .leave] := by rfl

end Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics
