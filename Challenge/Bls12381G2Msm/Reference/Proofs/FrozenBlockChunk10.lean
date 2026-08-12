import YulParser.Compile

set_option warningAsError true

namespace Challenge.Bls12381G2Msm.Reference.Proofs.Compilation

open YulSemantics (Block)
open YulSemantics.EVM (Op)

/-- Generated normalized AST statements 40 through 40. -/
def frozenReferenceBlockChunk10 : Block Op :=
[YulSemantics.Stmt.exprStmt
   (YulSemantics.Expr.builtin
     (YulSemantics.EVM.Op.ret)
     [YulSemantics.Expr.lit (YulSemantics.Literal.number 0), YulSemantics.Expr.lit (YulSemantics.Literal.number 256)])]

end Challenge.Bls12381G2Msm.Reference.Proofs.Compilation

