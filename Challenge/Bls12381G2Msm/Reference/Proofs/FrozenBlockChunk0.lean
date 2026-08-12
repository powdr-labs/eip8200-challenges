import YulParser.Compile

set_option warningAsError true

namespace Challenge.Bls12381G2Msm.Reference.Proofs.Compilation

open YulSemantics (Block)
open YulSemantics.EVM (Op)

/-- Generated normalized AST statements 0 through 3. -/
def frozenReferenceBlockChunk0 : Block Op :=
[YulSemantics.Stmt.funDef
   "\x000"
   ["\x0031", "\x0032"]
   ["\x0033"]
   [YulSemantics.Stmt.letDecl
      ["\x0034"]
      (some (YulSemantics.Expr.lit (YulSemantics.Literal.number 34565483545414906068789196026815425751))),
    YulSemantics.Stmt.letDecl
      ["\x0035"]
      (some (YulSemantics.Expr.lit
         (YulSemantics.Literal.number 45442060874369865957053122457065728162598490762543039060009208264153100167851))),
    YulSemantics.Stmt.assign
      ["\x0033"]
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.or)
        [YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.gt)
           [YulSemantics.Expr.var "\x0031", YulSemantics.Expr.var "\x0034"],
         YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.and)
           [YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.eq)
              [YulSemantics.Expr.var "\x0031", YulSemantics.Expr.var "\x0034"],
            YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.iszero)
              [YulSemantics.Expr.builtin
                 (YulSemantics.EVM.Op.lt)
                 [YulSemantics.Expr.var "\x0032", YulSemantics.Expr.var "\x0035"]]]])],
 YulSemantics.Stmt.funDef
   "\x001"
   ["\x0036", "\x0037"]
   ["\x0038"]
   [YulSemantics.Stmt.assign
      ["\x0038"]
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.iszero)
        [YulSemantics.Expr.call "\x000" [YulSemantics.Expr.var "\x0036", YulSemantics.Expr.var "\x0037"]])],
 YulSemantics.Stmt.funDef
   "\x002"
   ["\x0039", "\x0040"]
   ["\x0041"]
   [YulSemantics.Stmt.assign
      ["\x0041"]
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.and)
        [YulSemantics.Expr.builtin (YulSemantics.EVM.Op.iszero) [YulSemantics.Expr.var "\x0039"],
         YulSemantics.Expr.builtin (YulSemantics.EVM.Op.iszero) [YulSemantics.Expr.var "\x0040"]])],
 YulSemantics.Stmt.funDef
   "\x003"
   ["\x0042", "\x0043", "\x0044", "\x0045"]
   ["\x0046"]
   [YulSemantics.Stmt.assign
      ["\x0046"]
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.and)
        [YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.eq)
           [YulSemantics.Expr.var "\x0042", YulSemantics.Expr.var "\x0044"],
         YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.eq)
           [YulSemantics.Expr.var "\x0043", YulSemantics.Expr.var "\x0045"]])]]

end Challenge.Bls12381G2Msm.Reference.Proofs.Compilation

