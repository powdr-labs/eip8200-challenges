import YulParser.Compile

set_option warningAsError true

namespace Challenge.Bls12381G2Msm.Reference.Proofs.Compilation

open YulSemantics (Block)
open YulSemantics.EVM (Op)

/-- Generated normalized AST statements 8 through 11. -/
def frozenReferenceBlockChunk2 : Block Op :=
[YulSemantics.Stmt.funDef
   "\x008"
   ["\x0085"]
   []
   [YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.call
        "\x007"
        [YulSemantics.Expr.var "\x0085",
         YulSemantics.Expr.lit (YulSemantics.Literal.number 34565483545414906068789196026815425751),
         YulSemantics.Expr.lit
           (YulSemantics.Literal.number
             45442060874369865957053122457065728162598490762543039060009208264153100167851)])],
 YulSemantics.Stmt.funDef
   "\x009"
   ["\x0086", "\x0087", "\x0088", "\x0089"]
   ["\x0090", "\x0091"]
   [YulSemantics.Stmt.letDecl
      ["\x0092", "\x0093", "\x0094"]
      (some (YulSemantics.Expr.call
         "\x006"
         [YulSemantics.Expr.var "\x0086",
          YulSemantics.Expr.var "\x0087",
          YulSemantics.Expr.var "\x0088",
          YulSemantics.Expr.var "\x0089"])),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mstore)
        [YulSemantics.Expr.lit (YulSemantics.Literal.number 1024),
         YulSemantics.Expr.lit (YulSemantics.Literal.number 96)]),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mstore)
        [YulSemantics.Expr.lit (YulSemantics.Literal.number 1056),
         YulSemantics.Expr.lit (YulSemantics.Literal.number 1)]),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mstore)
        [YulSemantics.Expr.lit (YulSemantics.Literal.number 1088),
         YulSemantics.Expr.lit (YulSemantics.Literal.number 48)]),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mstore)
        [YulSemantics.Expr.lit (YulSemantics.Literal.number 1120), YulSemantics.Expr.var "\x0092"]),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mstore)
        [YulSemantics.Expr.lit (YulSemantics.Literal.number 1152), YulSemantics.Expr.var "\x0093"]),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mstore)
        [YulSemantics.Expr.lit (YulSemantics.Literal.number 1184), YulSemantics.Expr.var "\x0094"]),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mstore8)
        [YulSemantics.Expr.lit (YulSemantics.Literal.number 1216),
         YulSemantics.Expr.lit (YulSemantics.Literal.number 1)]),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.call "\x008" [YulSemantics.Expr.lit (YulSemantics.Literal.number 1217)]),
    YulSemantics.Stmt.cond
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.iszero)
        [YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.staticcall)
           [YulSemantics.Expr.lit (YulSemantics.Literal.number 500),
            YulSemantics.Expr.lit (YulSemantics.Literal.number 5),
            YulSemantics.Expr.lit (YulSemantics.Literal.number 1024),
            YulSemantics.Expr.lit (YulSemantics.Literal.number 241),
            YulSemantics.Expr.lit (YulSemantics.Literal.number 1280),
            YulSemantics.Expr.lit (YulSemantics.Literal.number 48)]])
      [YulSemantics.Stmt.exprStmt (YulSemantics.Expr.builtin (YulSemantics.EVM.Op.invalid) [])],
    YulSemantics.Stmt.assign
      ["\x0090"]
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.shr)
        [YulSemantics.Expr.lit (YulSemantics.Literal.number 128),
         YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.mload)
           [YulSemantics.Expr.lit (YulSemantics.Literal.number 1280)]]),
    YulSemantics.Stmt.assign
      ["\x0091"]
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mload)
        [YulSemantics.Expr.lit (YulSemantics.Literal.number 1296)])],
 YulSemantics.Stmt.funDef
   "\x0010"
   ["\x0095", "\x0096"]
   ["\x0097", "\x0098"]
   [YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mstore)
        [YulSemantics.Expr.lit (YulSemantics.Literal.number 1024),
         YulSemantics.Expr.lit (YulSemantics.Literal.number 48)]),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mstore)
        [YulSemantics.Expr.lit (YulSemantics.Literal.number 1056),
         YulSemantics.Expr.lit (YulSemantics.Literal.number 48)]),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mstore)
        [YulSemantics.Expr.lit (YulSemantics.Literal.number 1088),
         YulSemantics.Expr.lit (YulSemantics.Literal.number 48)]),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.call
        "\x007"
        [YulSemantics.Expr.lit (YulSemantics.Literal.number 1120),
         YulSemantics.Expr.var "\x0095",
         YulSemantics.Expr.var "\x0096"]),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.call
        "\x007"
        [YulSemantics.Expr.lit (YulSemantics.Literal.number 1168),
         YulSemantics.Expr.lit (YulSemantics.Literal.number 34565483545414906068789196026815425751),
         YulSemantics.Expr.lit
           (YulSemantics.Literal.number
             45442060874369865957053122457065728162598490762543039060009208264153100167849)]),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.call "\x008" [YulSemantics.Expr.lit (YulSemantics.Literal.number 1216)]),
    YulSemantics.Stmt.cond
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.iszero)
        [YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.staticcall)
           [YulSemantics.Expr.lit (YulSemantics.Literal.number 36576),
            YulSemantics.Expr.lit (YulSemantics.Literal.number 5),
            YulSemantics.Expr.lit (YulSemantics.Literal.number 1024),
            YulSemantics.Expr.lit (YulSemantics.Literal.number 240),
            YulSemantics.Expr.lit (YulSemantics.Literal.number 1280),
            YulSemantics.Expr.lit (YulSemantics.Literal.number 48)]])
      [YulSemantics.Stmt.exprStmt (YulSemantics.Expr.builtin (YulSemantics.EVM.Op.invalid) [])],
    YulSemantics.Stmt.assign
      ["\x0097"]
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.shr)
        [YulSemantics.Expr.lit (YulSemantics.Literal.number 128),
         YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.mload)
           [YulSemantics.Expr.lit (YulSemantics.Literal.number 1280)]]),
    YulSemantics.Stmt.assign
      ["\x0098"]
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mload)
        [YulSemantics.Expr.lit (YulSemantics.Literal.number 1296)])],
 YulSemantics.Stmt.funDef
   "\x0011"
   ["\x0099"]
   ["\x00100"]
   [YulSemantics.Stmt.assign
      ["\x00100"]
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.and)
        [YulSemantics.Expr.call
           "\x001"
           [YulSemantics.Expr.builtin (YulSemantics.EVM.Op.mload) [YulSemantics.Expr.var "\x0099"],
            YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.mload)
              [YulSemantics.Expr.builtin
                 (YulSemantics.EVM.Op.add)
                 [YulSemantics.Expr.var "\x0099", YulSemantics.Expr.lit (YulSemantics.Literal.number 32)]]],
         YulSemantics.Expr.call
           "\x001"
           [YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.mload)
              [YulSemantics.Expr.builtin
                 (YulSemantics.EVM.Op.add)
                 [YulSemantics.Expr.var "\x0099", YulSemantics.Expr.lit (YulSemantics.Literal.number 64)]],
            YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.mload)
              [YulSemantics.Expr.builtin
                 (YulSemantics.EVM.Op.add)
                 [YulSemantics.Expr.var "\x0099", YulSemantics.Expr.lit (YulSemantics.Literal.number 96)]]]])]]

end Challenge.Bls12381G2Msm.Reference.Proofs.Compilation

