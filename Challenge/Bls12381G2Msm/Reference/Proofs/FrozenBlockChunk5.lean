import YulParser.Compile

set_option warningAsError true

namespace Challenge.Bls12381G2Msm.Reference.Proofs.Compilation

open YulSemantics (Block)
open YulSemantics.EVM (Op)

/-- Generated normalized AST statements 20 through 23. -/
def frozenReferenceBlockChunk5 : Block Op :=
[YulSemantics.Stmt.funDef
   "\x0020"
   ["\x00130"]
   ["\x00131"]
   [YulSemantics.Stmt.assign
      ["\x00131"]
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.and)
        [YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.and)
           [YulSemantics.Expr.call "\x0011" [YulSemantics.Expr.var "\x00130"],
            YulSemantics.Expr.call
              "\x0011"
              [YulSemantics.Expr.builtin
                 (YulSemantics.EVM.Op.add)
                 [YulSemantics.Expr.var "\x00130", YulSemantics.Expr.lit (YulSemantics.Literal.number 128)]]],
         YulSemantics.Expr.call "\x0019" [YulSemantics.Expr.var "\x00130"]])],
 YulSemantics.Stmt.funDef
   "\x0021"
   ["\x00132"]
   ["\x00133"]
   [YulSemantics.Stmt.assign
      ["\x00133"]
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.and)
        [YulSemantics.Expr.call "\x0012" [YulSemantics.Expr.var "\x00132"],
         YulSemantics.Expr.call
           "\x0012"
           [YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.add)
              [YulSemantics.Expr.var "\x00132", YulSemantics.Expr.lit (YulSemantics.Literal.number 128)]]])],
 YulSemantics.Stmt.funDef
   "\x0022"
   []
   []
   [YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mstore)
        [YulSemantics.Expr.lit (YulSemantics.Literal.number 0), YulSemantics.Expr.lit (YulSemantics.Literal.number 0)]),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mstore)
        [YulSemantics.Expr.lit (YulSemantics.Literal.number 32),
         YulSemantics.Expr.lit (YulSemantics.Literal.number 0)]),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mstore)
        [YulSemantics.Expr.lit (YulSemantics.Literal.number 64),
         YulSemantics.Expr.lit (YulSemantics.Literal.number 0)]),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mstore)
        [YulSemantics.Expr.lit (YulSemantics.Literal.number 96),
         YulSemantics.Expr.lit (YulSemantics.Literal.number 0)]),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mstore)
        [YulSemantics.Expr.lit (YulSemantics.Literal.number 128),
         YulSemantics.Expr.lit (YulSemantics.Literal.number 0)]),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mstore)
        [YulSemantics.Expr.lit (YulSemantics.Literal.number 160),
         YulSemantics.Expr.lit (YulSemantics.Literal.number 0)]),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mstore)
        [YulSemantics.Expr.lit (YulSemantics.Literal.number 192),
         YulSemantics.Expr.lit (YulSemantics.Literal.number 0)]),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mstore)
        [YulSemantics.Expr.lit (YulSemantics.Literal.number 224),
         YulSemantics.Expr.lit (YulSemantics.Literal.number 0)])],
 YulSemantics.Stmt.funDef
   "\x0023"
   ["\x00134"]
   []
   [YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mstore)
        [YulSemantics.Expr.lit (YulSemantics.Literal.number 0),
         YulSemantics.Expr.builtin (YulSemantics.EVM.Op.mload) [YulSemantics.Expr.var "\x00134"]]),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mstore)
        [YulSemantics.Expr.lit (YulSemantics.Literal.number 32),
         YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.mload)
           [YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.add)
              [YulSemantics.Expr.var "\x00134", YulSemantics.Expr.lit (YulSemantics.Literal.number 32)]]]),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mstore)
        [YulSemantics.Expr.lit (YulSemantics.Literal.number 64),
         YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.mload)
           [YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.add)
              [YulSemantics.Expr.var "\x00134", YulSemantics.Expr.lit (YulSemantics.Literal.number 64)]]]),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mstore)
        [YulSemantics.Expr.lit (YulSemantics.Literal.number 96),
         YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.mload)
           [YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.add)
              [YulSemantics.Expr.var "\x00134", YulSemantics.Expr.lit (YulSemantics.Literal.number 96)]]]),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mstore)
        [YulSemantics.Expr.lit (YulSemantics.Literal.number 128),
         YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.mload)
           [YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.add)
              [YulSemantics.Expr.var "\x00134", YulSemantics.Expr.lit (YulSemantics.Literal.number 128)]]]),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mstore)
        [YulSemantics.Expr.lit (YulSemantics.Literal.number 160),
         YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.mload)
           [YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.add)
              [YulSemantics.Expr.var "\x00134", YulSemantics.Expr.lit (YulSemantics.Literal.number 160)]]]),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mstore)
        [YulSemantics.Expr.lit (YulSemantics.Literal.number 192),
         YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.mload)
           [YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.add)
              [YulSemantics.Expr.var "\x00134", YulSemantics.Expr.lit (YulSemantics.Literal.number 192)]]]),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mstore)
        [YulSemantics.Expr.lit (YulSemantics.Literal.number 224),
         YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.mload)
           [YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.add)
              [YulSemantics.Expr.var "\x00134", YulSemantics.Expr.lit (YulSemantics.Literal.number 224)]]])]]

end Challenge.Bls12381G2Msm.Reference.Proofs.Compilation

