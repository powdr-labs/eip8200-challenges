import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalLambda

set_option warningAsError true

/-! Frozen call boundary for the unequal-point slope square. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def pointAddUnequalX3Expr : Expr Op :=
  match pointAddUnequalX3Stmt with
  | .letDecl _ (some expr) => expr
  | _ => .lit (.number 0)

def pointAddUnequalX3Args : List (Expr Op) :=
  match pointAddUnequalX3Expr with
  | .call _ args => args
  | _ => []

theorem pointAddUnequalX3Stmt_eq : pointAddUnequalX3Stmt =
    .letDecl ["\x00136", "\x00137"] (some pointAddUnequalX3Expr) := by
  rfl

theorem pointAddUnequalX3Expr_eq : pointAddUnequalX3Expr =
    .call "\x009" pointAddUnequalX3Args := by
  rfl

theorem pointAddUnequalX3Args_eq : pointAddUnequalX3Args =
    [.var "\x00134", .var "\x00135",
      .var "\x00134", .var "\x00135"] := by
  rfl

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
