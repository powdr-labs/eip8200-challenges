import YulParser.Compile

set_option warningAsError true

namespace Challenge.Bls12381G2Msm.Reference.Proofs.Compilation

open YulSemantics (Block)
open YulSemantics.EVM (Op)

/-- Generated normalized AST statements 36 through 39. -/
def frozenReferenceBlockChunk9 : Block Op :=
[YulSemantics.Stmt.letDecl ["\x00156"] (some (YulSemantics.Expr.lit (YulSemantics.Literal.number 3840))),
 YulSemantics.Stmt.exprStmt (YulSemantics.Expr.call "\x0026" [YulSemantics.Expr.var "\x00156"]),
 YulSemantics.Stmt.forLoop
   [YulSemantics.Stmt.letDecl ["\x00157"] (some (YulSemantics.Expr.lit (YulSemantics.Literal.number 0)))]
   (YulSemantics.Expr.builtin
     (YulSemantics.EVM.Op.lt)
     [YulSemantics.Expr.var "\x00157", YulSemantics.Expr.var "\x00152"])
   [YulSemantics.Stmt.assign
      ["\x00157"]
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.add)
        [YulSemantics.Expr.var "\x00157", YulSemantics.Expr.lit (YulSemantics.Literal.number 288)])]
   [YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mstore)
        [YulSemantics.Expr.var "\x00153",
         YulSemantics.Expr.builtin (YulSemantics.EVM.Op.calldataload) [YulSemantics.Expr.var "\x00157"]]),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mstore)
        [YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.add)
           [YulSemantics.Expr.var "\x00153", YulSemantics.Expr.lit (YulSemantics.Literal.number 32)],
         YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.calldataload)
           [YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.add)
              [YulSemantics.Expr.var "\x00157", YulSemantics.Expr.lit (YulSemantics.Literal.number 32)]]]),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mstore)
        [YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.add)
           [YulSemantics.Expr.var "\x00153", YulSemantics.Expr.lit (YulSemantics.Literal.number 64)],
         YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.calldataload)
           [YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.add)
              [YulSemantics.Expr.var "\x00157", YulSemantics.Expr.lit (YulSemantics.Literal.number 64)]]]),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mstore)
        [YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.add)
           [YulSemantics.Expr.var "\x00153", YulSemantics.Expr.lit (YulSemantics.Literal.number 96)],
         YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.calldataload)
           [YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.add)
              [YulSemantics.Expr.var "\x00157", YulSemantics.Expr.lit (YulSemantics.Literal.number 96)]]]),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mstore)
        [YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.add)
           [YulSemantics.Expr.var "\x00153", YulSemantics.Expr.lit (YulSemantics.Literal.number 128)],
         YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.calldataload)
           [YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.add)
              [YulSemantics.Expr.var "\x00157", YulSemantics.Expr.lit (YulSemantics.Literal.number 128)]]]),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mstore)
        [YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.add)
           [YulSemantics.Expr.var "\x00153", YulSemantics.Expr.lit (YulSemantics.Literal.number 160)],
         YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.calldataload)
           [YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.add)
              [YulSemantics.Expr.var "\x00157", YulSemantics.Expr.lit (YulSemantics.Literal.number 160)]]]),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mstore)
        [YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.add)
           [YulSemantics.Expr.var "\x00153", YulSemantics.Expr.lit (YulSemantics.Literal.number 192)],
         YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.calldataload)
           [YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.add)
              [YulSemantics.Expr.var "\x00157", YulSemantics.Expr.lit (YulSemantics.Literal.number 192)]]]),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mstore)
        [YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.add)
           [YulSemantics.Expr.var "\x00153", YulSemantics.Expr.lit (YulSemantics.Literal.number 224)],
         YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.calldataload)
           [YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.add)
              [YulSemantics.Expr.var "\x00157", YulSemantics.Expr.lit (YulSemantics.Literal.number 224)]]]),
    YulSemantics.Stmt.cond
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.iszero)
        [YulSemantics.Expr.call "\x0020" [YulSemantics.Expr.var "\x00153"]])
      [YulSemantics.Stmt.exprStmt (YulSemantics.Expr.builtin (YulSemantics.EVM.Op.invalid) [])],
    YulSemantics.Stmt.cond
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.and)
        [YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.iszero)
           [YulSemantics.Expr.call "\x0028" [YulSemantics.Expr.var "\x00153"]],
         YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.iszero)
           [YulSemantics.Expr.call
              "\x0018"
              [YulSemantics.Expr.var "\x00153",
               YulSemantics.Expr.builtin
                 (YulSemantics.EVM.Op.add)
                 [YulSemantics.Expr.var "\x00153", YulSemantics.Expr.lit (YulSemantics.Literal.number 128)]]]])
      [YulSemantics.Stmt.exprStmt (YulSemantics.Expr.builtin (YulSemantics.EVM.Op.invalid) [])],
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.call
        "\x0030"
        [YulSemantics.Expr.lit
           (YulSemantics.Literal.number 52435875175126190479447740508185965837690552500527637822603658699938581184513),
         YulSemantics.Expr.var "\x00153",
         YulSemantics.Expr.var "\x00154"]),
    YulSemantics.Stmt.cond
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.iszero)
        [YulSemantics.Expr.call "\x0028" [YulSemantics.Expr.var "\x00154"]])
      [YulSemantics.Stmt.exprStmt (YulSemantics.Expr.builtin (YulSemantics.EVM.Op.invalid) [])],
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.call
        "\x0030"
        [YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.calldataload)
           [YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.add)
              [YulSemantics.Expr.var "\x00157", YulSemantics.Expr.lit (YulSemantics.Literal.number 256)]],
         YulSemantics.Expr.var "\x00153",
         YulSemantics.Expr.var "\x00155"]),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.call
        "\x0029"
        [YulSemantics.Expr.var "\x00156", YulSemantics.Expr.var "\x00156", YulSemantics.Expr.var "\x00155"])],
 YulSemantics.Stmt.exprStmt
   (YulSemantics.Expr.call
     "\x0027"
     [YulSemantics.Expr.lit (YulSemantics.Literal.number 0), YulSemantics.Expr.var "\x00156"])]

end Challenge.Bls12381G2Msm.Reference.Proofs.Compilation

