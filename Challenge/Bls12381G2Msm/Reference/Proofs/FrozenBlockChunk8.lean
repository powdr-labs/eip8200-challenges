import YulParser.Compile

set_option warningAsError true

namespace Challenge.Bls12381G2Msm.Reference.Proofs.Compilation

open YulSemantics (Block)
open YulSemantics.EVM (Op)

/-- Generated normalized AST statements 32 through 35. -/
def frozenReferenceBlockChunk8 : Block Op :=
[YulSemantics.Stmt.cond
   (YulSemantics.Expr.builtin
     (YulSemantics.EVM.Op.or)
     [YulSemantics.Expr.builtin (YulSemantics.EVM.Op.iszero) [YulSemantics.Expr.var "\x00152"],
      YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mod)
        [YulSemantics.Expr.var "\x00152", YulSemantics.Expr.lit (YulSemantics.Literal.number 288)]])
   [YulSemantics.Stmt.exprStmt (YulSemantics.Expr.builtin (YulSemantics.EVM.Op.invalid) [])],
 YulSemantics.Stmt.letDecl ["\x00153"] (some (YulSemantics.Expr.lit (YulSemantics.Literal.number 3072))),
 YulSemantics.Stmt.letDecl ["\x00154"] (some (YulSemantics.Expr.lit (YulSemantics.Literal.number 3328))),
 YulSemantics.Stmt.letDecl ["\x00155"] (some (YulSemantics.Expr.lit (YulSemantics.Literal.number 3584)))]

end Challenge.Bls12381G2Msm.Reference.Proofs.Compilation

