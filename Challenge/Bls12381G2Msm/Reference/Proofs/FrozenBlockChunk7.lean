import YulParser.Compile

set_option warningAsError true

namespace Challenge.Bls12381G2Msm.Reference.Proofs.Compilation

open YulSemantics (Block)
open YulSemantics.EVM (Op)

/-- Generated normalized AST statements 28 through 31. -/
def frozenReferenceBlockChunk7 : Block Op :=
[YulSemantics.Stmt.funDef
   "\x0028"
   ["\x00143"]
   ["\x00144"]
   [YulSemantics.Stmt.assign
      ["\x00144"]
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.and)
        [YulSemantics.Expr.call "\x0012" [YulSemantics.Expr.var "\x00143"],
         YulSemantics.Expr.call
           "\x0012"
           [YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.add)
              [YulSemantics.Expr.var "\x00143", YulSemantics.Expr.lit (YulSemantics.Literal.number 128)]]])],
 YulSemantics.Stmt.funDef
   "\x0029"
   ["\x00145", "\x00146", "\x00147"]
   []
   [YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mstore)
        [YulSemantics.Expr.lit (YulSemantics.Literal.number 1920), YulSemantics.Expr.var "\x00145"]),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mstore)
        [YulSemantics.Expr.lit (YulSemantics.Literal.number 1952), YulSemantics.Expr.var "\x00146"]),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mstore)
        [YulSemantics.Expr.lit (YulSemantics.Literal.number 1984), YulSemantics.Expr.var "\x00147"]),
    YulSemantics.Stmt.cond
      (YulSemantics.Expr.call
        "\x0028"
        [YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.mload)
           [YulSemantics.Expr.lit (YulSemantics.Literal.number 1952)]])
      [YulSemantics.Stmt.exprStmt
         (YulSemantics.Expr.call
           "\x0027"
           [YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.mload)
              [YulSemantics.Expr.lit (YulSemantics.Literal.number 1920)],
            YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.mload)
              [YulSemantics.Expr.lit (YulSemantics.Literal.number 1984)]]),
       YulSemantics.Stmt.leave],
    YulSemantics.Stmt.cond
      (YulSemantics.Expr.call
        "\x0028"
        [YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.mload)
           [YulSemantics.Expr.lit (YulSemantics.Literal.number 1984)]])
      [YulSemantics.Stmt.exprStmt
         (YulSemantics.Expr.call
           "\x0027"
           [YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.mload)
              [YulSemantics.Expr.lit (YulSemantics.Literal.number 1920)],
            YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.mload)
              [YulSemantics.Expr.lit (YulSemantics.Literal.number 1952)]]),
       YulSemantics.Stmt.leave],
    YulSemantics.Stmt.cond
      (YulSemantics.Expr.call
        "\x0013"
        [YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.mload)
           [YulSemantics.Expr.lit (YulSemantics.Literal.number 1952)],
         YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.mload)
           [YulSemantics.Expr.lit (YulSemantics.Literal.number 1984)]])
      [YulSemantics.Stmt.exprStmt
         (YulSemantics.Expr.call
           "\x0014"
           [YulSemantics.Expr.lit (YulSemantics.Literal.number 2048),
            YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.add)
              [YulSemantics.Expr.builtin
                 (YulSemantics.EVM.Op.mload)
                 [YulSemantics.Expr.lit (YulSemantics.Literal.number 1952)],
               YulSemantics.Expr.lit (YulSemantics.Literal.number 128)],
            YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.add)
              [YulSemantics.Expr.builtin
                 (YulSemantics.EVM.Op.mload)
                 [YulSemantics.Expr.lit (YulSemantics.Literal.number 1984)],
               YulSemantics.Expr.lit (YulSemantics.Literal.number 128)]]),
       YulSemantics.Stmt.cond
         (YulSemantics.Expr.call "\x0012" [YulSemantics.Expr.lit (YulSemantics.Literal.number 2048)])
         [YulSemantics.Stmt.exprStmt
            (YulSemantics.Expr.call
              "\x0026"
              [YulSemantics.Expr.builtin
                 (YulSemantics.EVM.Op.mload)
                 [YulSemantics.Expr.lit (YulSemantics.Literal.number 1920)]]),
          YulSemantics.Stmt.leave],
       YulSemantics.Stmt.exprStmt
         (YulSemantics.Expr.call
           "\x0016"
           [YulSemantics.Expr.lit (YulSemantics.Literal.number 2176),
            YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.mload)
              [YulSemantics.Expr.lit (YulSemantics.Literal.number 1952)],
            YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.mload)
              [YulSemantics.Expr.lit (YulSemantics.Literal.number 1952)]]),
       YulSemantics.Stmt.exprStmt
         (YulSemantics.Expr.call
           "\x0014"
           [YulSemantics.Expr.lit (YulSemantics.Literal.number 2304),
            YulSemantics.Expr.lit (YulSemantics.Literal.number 2176),
            YulSemantics.Expr.lit (YulSemantics.Literal.number 2176)]),
       YulSemantics.Stmt.exprStmt
         (YulSemantics.Expr.call
           "\x0014"
           [YulSemantics.Expr.lit (YulSemantics.Literal.number 2304),
            YulSemantics.Expr.lit (YulSemantics.Literal.number 2304),
            YulSemantics.Expr.lit (YulSemantics.Literal.number 2176)]),
       YulSemantics.Stmt.exprStmt
         (YulSemantics.Expr.call
           "\x0014"
           [YulSemantics.Expr.lit (YulSemantics.Literal.number 2432),
            YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.add)
              [YulSemantics.Expr.builtin
                 (YulSemantics.EVM.Op.mload)
                 [YulSemantics.Expr.lit (YulSemantics.Literal.number 1952)],
               YulSemantics.Expr.lit (YulSemantics.Literal.number 128)],
            YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.add)
              [YulSemantics.Expr.builtin
                 (YulSemantics.EVM.Op.mload)
                 [YulSemantics.Expr.lit (YulSemantics.Literal.number 1952)],
               YulSemantics.Expr.lit (YulSemantics.Literal.number 128)]]),
       YulSemantics.Stmt.exprStmt
         (YulSemantics.Expr.call
           "\x0017"
           [YulSemantics.Expr.lit (YulSemantics.Literal.number 2560),
            YulSemantics.Expr.lit (YulSemantics.Literal.number 2432)]),
       YulSemantics.Stmt.exprStmt
         (YulSemantics.Expr.call
           "\x0016"
           [YulSemantics.Expr.lit (YulSemantics.Literal.number 2048),
            YulSemantics.Expr.lit (YulSemantics.Literal.number 2304),
            YulSemantics.Expr.lit (YulSemantics.Literal.number 2560)])],
    YulSemantics.Stmt.cond
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.iszero)
        [YulSemantics.Expr.call
           "\x0013"
           [YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.mload)
              [YulSemantics.Expr.lit (YulSemantics.Literal.number 1952)],
            YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.mload)
              [YulSemantics.Expr.lit (YulSemantics.Literal.number 1984)]]])
      [YulSemantics.Stmt.exprStmt
         (YulSemantics.Expr.call
           "\x0015"
           [YulSemantics.Expr.lit (YulSemantics.Literal.number 2304),
            YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.add)
              [YulSemantics.Expr.builtin
                 (YulSemantics.EVM.Op.mload)
                 [YulSemantics.Expr.lit (YulSemantics.Literal.number 1984)],
               YulSemantics.Expr.lit (YulSemantics.Literal.number 128)],
            YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.add)
              [YulSemantics.Expr.builtin
                 (YulSemantics.EVM.Op.mload)
                 [YulSemantics.Expr.lit (YulSemantics.Literal.number 1952)],
               YulSemantics.Expr.lit (YulSemantics.Literal.number 128)]]),
       YulSemantics.Stmt.exprStmt
         (YulSemantics.Expr.call
           "\x0015"
           [YulSemantics.Expr.lit (YulSemantics.Literal.number 2432),
            YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.mload)
              [YulSemantics.Expr.lit (YulSemantics.Literal.number 1984)],
            YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.mload)
              [YulSemantics.Expr.lit (YulSemantics.Literal.number 1952)]]),
       YulSemantics.Stmt.exprStmt
         (YulSemantics.Expr.call
           "\x0017"
           [YulSemantics.Expr.lit (YulSemantics.Literal.number 2560),
            YulSemantics.Expr.lit (YulSemantics.Literal.number 2432)]),
       YulSemantics.Stmt.exprStmt
         (YulSemantics.Expr.call
           "\x0016"
           [YulSemantics.Expr.lit (YulSemantics.Literal.number 2048),
            YulSemantics.Expr.lit (YulSemantics.Literal.number 2304),
            YulSemantics.Expr.lit (YulSemantics.Literal.number 2560)])],
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.call
        "\x0016"
        [YulSemantics.Expr.lit (YulSemantics.Literal.number 2688),
         YulSemantics.Expr.lit (YulSemantics.Literal.number 2048),
         YulSemantics.Expr.lit (YulSemantics.Literal.number 2048)]),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.call
        "\x0015"
        [YulSemantics.Expr.lit (YulSemantics.Literal.number 2688),
         YulSemantics.Expr.lit (YulSemantics.Literal.number 2688),
         YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.mload)
           [YulSemantics.Expr.lit (YulSemantics.Literal.number 1952)]]),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.call
        "\x0015"
        [YulSemantics.Expr.lit (YulSemantics.Literal.number 2688),
         YulSemantics.Expr.lit (YulSemantics.Literal.number 2688),
         YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.mload)
           [YulSemantics.Expr.lit (YulSemantics.Literal.number 1984)]]),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.call
        "\x0015"
        [YulSemantics.Expr.lit (YulSemantics.Literal.number 2816),
         YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.mload)
           [YulSemantics.Expr.lit (YulSemantics.Literal.number 1952)],
         YulSemantics.Expr.lit (YulSemantics.Literal.number 2688)]),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.call
        "\x0016"
        [YulSemantics.Expr.lit (YulSemantics.Literal.number 2944),
         YulSemantics.Expr.lit (YulSemantics.Literal.number 2048),
         YulSemantics.Expr.lit (YulSemantics.Literal.number 2816)]),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.call
        "\x0015"
        [YulSemantics.Expr.lit (YulSemantics.Literal.number 2944),
         YulSemantics.Expr.lit (YulSemantics.Literal.number 2944),
         YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.add)
           [YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.mload)
              [YulSemantics.Expr.lit (YulSemantics.Literal.number 1952)],
            YulSemantics.Expr.lit (YulSemantics.Literal.number 128)]]),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.call
        "\x0025"
        [YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.mload)
           [YulSemantics.Expr.lit (YulSemantics.Literal.number 1920)],
         YulSemantics.Expr.lit (YulSemantics.Literal.number 2688),
         YulSemantics.Expr.lit (YulSemantics.Literal.number 2944)])],
 YulSemantics.Stmt.funDef
   "\x0030"
   ["\x00148", "\x00149", "\x00150"]
   []
   [YulSemantics.Stmt.exprStmt (YulSemantics.Expr.call "\x0026" [YulSemantics.Expr.var "\x00150"]),
    YulSemantics.Stmt.letDecl
      ["\x00151"]
      (some (YulSemantics.Expr.builtin
         (YulSemantics.EVM.Op.shl)
         [YulSemantics.Expr.lit (YulSemantics.Literal.number 255),
          YulSemantics.Expr.lit (YulSemantics.Literal.number 1)])),
    YulSemantics.Stmt.forLoop
      []
      (YulSemantics.Expr.var "\x00151")
      [YulSemantics.Stmt.assign
         ["\x00151"]
         (YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.shr)
           [YulSemantics.Expr.lit (YulSemantics.Literal.number 1), YulSemantics.Expr.var "\x00151"])]
      [YulSemantics.Stmt.exprStmt
         (YulSemantics.Expr.call
           "\x0029"
           [YulSemantics.Expr.var "\x00150", YulSemantics.Expr.var "\x00150", YulSemantics.Expr.var "\x00150"]),
       YulSemantics.Stmt.cond
         (YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.and)
           [YulSemantics.Expr.var "\x00148", YulSemantics.Expr.var "\x00151"])
         [YulSemantics.Stmt.exprStmt
            (YulSemantics.Expr.call
              "\x0029"
              [YulSemantics.Expr.var "\x00150", YulSemantics.Expr.var "\x00150", YulSemantics.Expr.var "\x00149"])]]],
 YulSemantics.Stmt.letDecl ["\x00152"] (some (YulSemantics.Expr.builtin (YulSemantics.EVM.Op.calldatasize) []))]

end Challenge.Bls12381G2Msm.Reference.Proofs.Compilation

