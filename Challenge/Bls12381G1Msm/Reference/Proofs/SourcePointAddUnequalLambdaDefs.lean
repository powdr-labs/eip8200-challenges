import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalInvFull

set_option warningAsError true

/-! Frozen call boundary for the unequal-point slope multiplication. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def pointAddUnequalLambdaExpr : Expr Op :=
  match pointAddUnequalLambdaStmt with
  | .letDecl _ (some expr) => expr
  | _ => .lit (.number 0)

def pointAddUnequalLambdaArgs : List (Expr Op) :=
  match pointAddUnequalLambdaExpr with
  | .call _ args => args
  | _ => []

theorem pointAddUnequalLambdaStmt_eq : pointAddUnequalLambdaStmt =
    .letDecl ["\x00134", "\x00135"]
      (some pointAddUnequalLambdaExpr) := by
  rfl

theorem pointAddUnequalLambdaExpr_eq : pointAddUnequalLambdaExpr =
    .call "\x009" pointAddUnequalLambdaArgs := by
  rfl

theorem pointAddUnequalLambdaArgs_eq : pointAddUnequalLambdaArgs =
    [.var "\x00128", .var "\x00129",
      .var "\x00132", .var "\x00133"] := by
  rfl

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
