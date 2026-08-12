import Challenge.Bls12381G2Msm.Reference.Proofs.SourcePointAddIdentity

set_option warningAsError true

/-! Frozen finite-branch boundaries for G2MSM `pointAdd`. -/

namespace Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def pointAddEqualCondition : Expr Op :=
  match pointAddStmt5 with
  | .cond condition _ => condition
  | _ => .lit (.number 0)

def pointAddEqualBody : Block Op :=
  match pointAddStmt5 with
  | .cond _ body => body
  | _ => []

theorem pointAddStmt5_eq : pointAddStmt5 =
    .cond pointAddEqualCondition pointAddEqualBody := by rfl

theorem pointAddEqualCondition_eq : pointAddEqualCondition =
    .call "\x0013"
      [.builtin .mload [.lit (.number 1952)],
        .builtin .mload [.lit (.number 1984)]] := by rfl

def pointAddEqualStmt0 : Stmt Op := pointAddEqualBody[0]!
def pointAddEqualStmt1 : Stmt Op := pointAddEqualBody[1]!
def pointAddEqualStmt2 : Stmt Op := pointAddEqualBody[2]!
def pointAddEqualStmt3 : Stmt Op := pointAddEqualBody[3]!
def pointAddEqualStmt4 : Stmt Op := pointAddEqualBody[4]!
def pointAddEqualStmt5 : Stmt Op := pointAddEqualBody[5]!
def pointAddEqualStmt6 : Stmt Op := pointAddEqualBody[6]!
def pointAddEqualStmt7 : Stmt Op := pointAddEqualBody[7]!

theorem pointAddEqualBody_eq : pointAddEqualBody =
    [pointAddEqualStmt0, pointAddEqualStmt1, pointAddEqualStmt2,
      pointAddEqualStmt3, pointAddEqualStmt4, pointAddEqualStmt5,
      pointAddEqualStmt6, pointAddEqualStmt7] := by rfl

def pointAddEqualYZeroCondition : Expr Op :=
  match pointAddEqualStmt1 with
  | .cond condition _ => condition
  | _ => .lit (.number 0)

def pointAddEqualYZeroBody : Block Op :=
  match pointAddEqualStmt1 with
  | .cond _ body => body
  | _ => []

theorem pointAddEqualYZeroStmt_eq : pointAddEqualStmt1 =
    .cond pointAddEqualYZeroCondition pointAddEqualYZeroBody := by rfl

theorem pointAddEqualYZeroCondition_eq : pointAddEqualYZeroCondition =
    .call "\x0012" [.lit (.number 2048)] := by rfl

theorem pointAddEqualYZeroBody_eq : pointAddEqualYZeroBody =
    [.exprStmt (.call "\x0026"
      [.builtin .mload [.lit (.number 1920)]]), .leave] := by rfl

def pointAddUnequalCondition : Expr Op :=
  match pointAddStmt6 with
  | .cond condition _ => condition
  | _ => .lit (.number 0)

def pointAddUnequalBody : Block Op :=
  match pointAddStmt6 with
  | .cond _ body => body
  | _ => []

theorem pointAddStmt6_eq : pointAddStmt6 =
    .cond pointAddUnequalCondition pointAddUnequalBody := by rfl

theorem pointAddUnequalCondition_eq : pointAddUnequalCondition =
    .builtin .iszero [.call "\x0013"
      [.builtin .mload [.lit (.number 1952)],
        .builtin .mload [.lit (.number 1984)]]] := by rfl

def pointAddUnequalStmt0 : Stmt Op := pointAddUnequalBody[0]!
def pointAddUnequalStmt1 : Stmt Op := pointAddUnequalBody[1]!
def pointAddUnequalStmt2 : Stmt Op := pointAddUnequalBody[2]!
def pointAddUnequalStmt3 : Stmt Op := pointAddUnequalBody[3]!

theorem pointAddUnequalBody_eq : pointAddUnequalBody =
    [pointAddUnequalStmt0, pointAddUnequalStmt1,
      pointAddUnequalStmt2, pointAddUnequalStmt3] := by rfl

end Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics
