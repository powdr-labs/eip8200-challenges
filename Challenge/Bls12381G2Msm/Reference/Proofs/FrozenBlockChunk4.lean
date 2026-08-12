import YulParser.Compile

set_option warningAsError true

namespace Challenge.Bls12381G2Msm.Reference.Proofs.Compilation

open YulSemantics (Block)
open YulSemantics.EVM (Op)

/-- Generated normalized AST statements 16 through 19. -/
def frozenReferenceBlockChunk4 : Block Op :=
[YulSemantics.Stmt.funDef
   "\x0016"
   ["\x00116", "\x00117", "\x00118"]
   []
   [YulSemantics.Stmt.letDecl
      ["\x00119", "\x00120"]
      (some (YulSemantics.Expr.call
         "\x009"
         [YulSemantics.Expr.builtin (YulSemantics.EVM.Op.mload) [YulSemantics.Expr.var "\x00117"],
          YulSemantics.Expr.builtin
            (YulSemantics.EVM.Op.mload)
            [YulSemantics.Expr.builtin
               (YulSemantics.EVM.Op.add)
               [YulSemantics.Expr.var "\x00117", YulSemantics.Expr.lit (YulSemantics.Literal.number 32)]],
          YulSemantics.Expr.builtin (YulSemantics.EVM.Op.mload) [YulSemantics.Expr.var "\x00118"],
          YulSemantics.Expr.builtin
            (YulSemantics.EVM.Op.mload)
            [YulSemantics.Expr.builtin
               (YulSemantics.EVM.Op.add)
               [YulSemantics.Expr.var "\x00118", YulSemantics.Expr.lit (YulSemantics.Literal.number 32)]]])),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mstore)
        [YulSemantics.Expr.lit (YulSemantics.Literal.number 1536), YulSemantics.Expr.var "\x00119"]),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mstore)
        [YulSemantics.Expr.lit (YulSemantics.Literal.number 1568), YulSemantics.Expr.var "\x00120"]),
    YulSemantics.Stmt.assign
      ["\x00119", "\x00120"]
      (YulSemantics.Expr.call
        "\x009"
        [YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.mload)
           [YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.add)
              [YulSemantics.Expr.var "\x00117", YulSemantics.Expr.lit (YulSemantics.Literal.number 64)]],
         YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.mload)
           [YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.add)
              [YulSemantics.Expr.var "\x00117", YulSemantics.Expr.lit (YulSemantics.Literal.number 96)]],
         YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.mload)
           [YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.add)
              [YulSemantics.Expr.var "\x00118", YulSemantics.Expr.lit (YulSemantics.Literal.number 64)]],
         YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.mload)
           [YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.add)
              [YulSemantics.Expr.var "\x00118", YulSemantics.Expr.lit (YulSemantics.Literal.number 96)]]]),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mstore)
        [YulSemantics.Expr.lit (YulSemantics.Literal.number 1600), YulSemantics.Expr.var "\x00119"]),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mstore)
        [YulSemantics.Expr.lit (YulSemantics.Literal.number 1632), YulSemantics.Expr.var "\x00120"]),
    YulSemantics.Stmt.assign
      ["\x00119", "\x00120"]
      (YulSemantics.Expr.call
        "\x005"
        [YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.mload)
           [YulSemantics.Expr.lit (YulSemantics.Literal.number 1536)],
         YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.mload)
           [YulSemantics.Expr.lit (YulSemantics.Literal.number 1568)],
         YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.mload)
           [YulSemantics.Expr.lit (YulSemantics.Literal.number 1600)],
         YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.mload)
           [YulSemantics.Expr.lit (YulSemantics.Literal.number 1632)]]),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mstore)
        [YulSemantics.Expr.var "\x00116", YulSemantics.Expr.var "\x00119"]),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mstore)
        [YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.add)
           [YulSemantics.Expr.var "\x00116", YulSemantics.Expr.lit (YulSemantics.Literal.number 32)],
         YulSemantics.Expr.var "\x00120"]),
    YulSemantics.Stmt.assign
      ["\x00119", "\x00120"]
      (YulSemantics.Expr.call
        "\x004"
        [YulSemantics.Expr.builtin (YulSemantics.EVM.Op.mload) [YulSemantics.Expr.var "\x00117"],
         YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.mload)
           [YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.add)
              [YulSemantics.Expr.var "\x00117", YulSemantics.Expr.lit (YulSemantics.Literal.number 32)]],
         YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.mload)
           [YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.add)
              [YulSemantics.Expr.var "\x00117", YulSemantics.Expr.lit (YulSemantics.Literal.number 64)]],
         YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.mload)
           [YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.add)
              [YulSemantics.Expr.var "\x00117", YulSemantics.Expr.lit (YulSemantics.Literal.number 96)]]]),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mstore)
        [YulSemantics.Expr.lit (YulSemantics.Literal.number 1664), YulSemantics.Expr.var "\x00119"]),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mstore)
        [YulSemantics.Expr.lit (YulSemantics.Literal.number 1696), YulSemantics.Expr.var "\x00120"]),
    YulSemantics.Stmt.assign
      ["\x00119", "\x00120"]
      (YulSemantics.Expr.call
        "\x004"
        [YulSemantics.Expr.builtin (YulSemantics.EVM.Op.mload) [YulSemantics.Expr.var "\x00118"],
         YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.mload)
           [YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.add)
              [YulSemantics.Expr.var "\x00118", YulSemantics.Expr.lit (YulSemantics.Literal.number 32)]],
         YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.mload)
           [YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.add)
              [YulSemantics.Expr.var "\x00118", YulSemantics.Expr.lit (YulSemantics.Literal.number 64)]],
         YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.mload)
           [YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.add)
              [YulSemantics.Expr.var "\x00118", YulSemantics.Expr.lit (YulSemantics.Literal.number 96)]]]),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mstore)
        [YulSemantics.Expr.lit (YulSemantics.Literal.number 1728), YulSemantics.Expr.var "\x00119"]),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mstore)
        [YulSemantics.Expr.lit (YulSemantics.Literal.number 1760), YulSemantics.Expr.var "\x00120"]),
    YulSemantics.Stmt.assign
      ["\x00119", "\x00120"]
      (YulSemantics.Expr.call
        "\x009"
        [YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.mload)
           [YulSemantics.Expr.lit (YulSemantics.Literal.number 1664)],
         YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.mload)
           [YulSemantics.Expr.lit (YulSemantics.Literal.number 1696)],
         YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.mload)
           [YulSemantics.Expr.lit (YulSemantics.Literal.number 1728)],
         YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.mload)
           [YulSemantics.Expr.lit (YulSemantics.Literal.number 1760)]]),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mstore)
        [YulSemantics.Expr.lit (YulSemantics.Literal.number 1792), YulSemantics.Expr.var "\x00119"]),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mstore)
        [YulSemantics.Expr.lit (YulSemantics.Literal.number 1824), YulSemantics.Expr.var "\x00120"]),
    YulSemantics.Stmt.assign
      ["\x00119", "\x00120"]
      (YulSemantics.Expr.call
        "\x004"
        [YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.mload)
           [YulSemantics.Expr.lit (YulSemantics.Literal.number 1536)],
         YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.mload)
           [YulSemantics.Expr.lit (YulSemantics.Literal.number 1568)],
         YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.mload)
           [YulSemantics.Expr.lit (YulSemantics.Literal.number 1600)],
         YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.mload)
           [YulSemantics.Expr.lit (YulSemantics.Literal.number 1632)]]),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mstore)
        [YulSemantics.Expr.lit (YulSemantics.Literal.number 1856), YulSemantics.Expr.var "\x00119"]),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mstore)
        [YulSemantics.Expr.lit (YulSemantics.Literal.number 1888), YulSemantics.Expr.var "\x00120"]),
    YulSemantics.Stmt.assign
      ["\x00119", "\x00120"]
      (YulSemantics.Expr.call
        "\x005"
        [YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.mload)
           [YulSemantics.Expr.lit (YulSemantics.Literal.number 1792)],
         YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.mload)
           [YulSemantics.Expr.lit (YulSemantics.Literal.number 1824)],
         YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.mload)
           [YulSemantics.Expr.lit (YulSemantics.Literal.number 1856)],
         YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.mload)
           [YulSemantics.Expr.lit (YulSemantics.Literal.number 1888)]]),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mstore)
        [YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.add)
           [YulSemantics.Expr.var "\x00116", YulSemantics.Expr.lit (YulSemantics.Literal.number 64)],
         YulSemantics.Expr.var "\x00119"]),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mstore)
        [YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.add)
           [YulSemantics.Expr.var "\x00116", YulSemantics.Expr.lit (YulSemantics.Literal.number 96)],
         YulSemantics.Expr.var "\x00120"])],
 YulSemantics.Stmt.funDef
   "\x0017"
   ["\x00121", "\x00122"]
   []
   [YulSemantics.Stmt.letDecl
      ["\x00123", "\x00124"]
      (some (YulSemantics.Expr.call
         "\x009"
         [YulSemantics.Expr.builtin (YulSemantics.EVM.Op.mload) [YulSemantics.Expr.var "\x00122"],
          YulSemantics.Expr.builtin
            (YulSemantics.EVM.Op.mload)
            [YulSemantics.Expr.builtin
               (YulSemantics.EVM.Op.add)
               [YulSemantics.Expr.var "\x00122", YulSemantics.Expr.lit (YulSemantics.Literal.number 32)]],
          YulSemantics.Expr.builtin (YulSemantics.EVM.Op.mload) [YulSemantics.Expr.var "\x00122"],
          YulSemantics.Expr.builtin
            (YulSemantics.EVM.Op.mload)
            [YulSemantics.Expr.builtin
               (YulSemantics.EVM.Op.add)
               [YulSemantics.Expr.var "\x00122", YulSemantics.Expr.lit (YulSemantics.Literal.number 32)]]])),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mstore)
        [YulSemantics.Expr.lit (YulSemantics.Literal.number 1536), YulSemantics.Expr.var "\x00123"]),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mstore)
        [YulSemantics.Expr.lit (YulSemantics.Literal.number 1568), YulSemantics.Expr.var "\x00124"]),
    YulSemantics.Stmt.assign
      ["\x00123", "\x00124"]
      (YulSemantics.Expr.call
        "\x009"
        [YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.mload)
           [YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.add)
              [YulSemantics.Expr.var "\x00122", YulSemantics.Expr.lit (YulSemantics.Literal.number 64)]],
         YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.mload)
           [YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.add)
              [YulSemantics.Expr.var "\x00122", YulSemantics.Expr.lit (YulSemantics.Literal.number 96)]],
         YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.mload)
           [YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.add)
              [YulSemantics.Expr.var "\x00122", YulSemantics.Expr.lit (YulSemantics.Literal.number 64)]],
         YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.mload)
           [YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.add)
              [YulSemantics.Expr.var "\x00122", YulSemantics.Expr.lit (YulSemantics.Literal.number 96)]]]),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mstore)
        [YulSemantics.Expr.lit (YulSemantics.Literal.number 1600), YulSemantics.Expr.var "\x00123"]),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mstore)
        [YulSemantics.Expr.lit (YulSemantics.Literal.number 1632), YulSemantics.Expr.var "\x00124"]),
    YulSemantics.Stmt.assign
      ["\x00123", "\x00124"]
      (YulSemantics.Expr.call
        "\x004"
        [YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.mload)
           [YulSemantics.Expr.lit (YulSemantics.Literal.number 1536)],
         YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.mload)
           [YulSemantics.Expr.lit (YulSemantics.Literal.number 1568)],
         YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.mload)
           [YulSemantics.Expr.lit (YulSemantics.Literal.number 1600)],
         YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.mload)
           [YulSemantics.Expr.lit (YulSemantics.Literal.number 1632)]]),
    YulSemantics.Stmt.assign
      ["\x00123", "\x00124"]
      (YulSemantics.Expr.call "\x0010" [YulSemantics.Expr.var "\x00123", YulSemantics.Expr.var "\x00124"]),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mstore)
        [YulSemantics.Expr.lit (YulSemantics.Literal.number 1664), YulSemantics.Expr.var "\x00123"]),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mstore)
        [YulSemantics.Expr.lit (YulSemantics.Literal.number 1696), YulSemantics.Expr.var "\x00124"]),
    YulSemantics.Stmt.assign
      ["\x00123", "\x00124"]
      (YulSemantics.Expr.call
        "\x009"
        [YulSemantics.Expr.builtin (YulSemantics.EVM.Op.mload) [YulSemantics.Expr.var "\x00122"],
         YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.mload)
           [YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.add)
              [YulSemantics.Expr.var "\x00122", YulSemantics.Expr.lit (YulSemantics.Literal.number 32)]],
         YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.mload)
           [YulSemantics.Expr.lit (YulSemantics.Literal.number 1664)],
         YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.mload)
           [YulSemantics.Expr.lit (YulSemantics.Literal.number 1696)]]),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mstore)
        [YulSemantics.Expr.var "\x00121", YulSemantics.Expr.var "\x00123"]),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mstore)
        [YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.add)
           [YulSemantics.Expr.var "\x00121", YulSemantics.Expr.lit (YulSemantics.Literal.number 32)],
         YulSemantics.Expr.var "\x00124"]),
    YulSemantics.Stmt.assign
      ["\x00123", "\x00124"]
      (YulSemantics.Expr.call
        "\x005"
        [YulSemantics.Expr.lit (YulSemantics.Literal.number 0),
         YulSemantics.Expr.lit (YulSemantics.Literal.number 0),
         YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.mload)
           [YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.add)
              [YulSemantics.Expr.var "\x00122", YulSemantics.Expr.lit (YulSemantics.Literal.number 64)]],
         YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.mload)
           [YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.add)
              [YulSemantics.Expr.var "\x00122", YulSemantics.Expr.lit (YulSemantics.Literal.number 96)]]]),
    YulSemantics.Stmt.assign
      ["\x00123", "\x00124"]
      (YulSemantics.Expr.call
        "\x009"
        [YulSemantics.Expr.var "\x00123",
         YulSemantics.Expr.var "\x00124",
         YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.mload)
           [YulSemantics.Expr.lit (YulSemantics.Literal.number 1664)],
         YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.mload)
           [YulSemantics.Expr.lit (YulSemantics.Literal.number 1696)]]),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mstore)
        [YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.add)
           [YulSemantics.Expr.var "\x00121", YulSemantics.Expr.lit (YulSemantics.Literal.number 64)],
         YulSemantics.Expr.var "\x00123"]),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mstore)
        [YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.add)
           [YulSemantics.Expr.var "\x00121", YulSemantics.Expr.lit (YulSemantics.Literal.number 96)],
         YulSemantics.Expr.var "\x00124"])],
 YulSemantics.Stmt.funDef
   "\x0018"
   ["\x00125", "\x00126"]
   ["\x00127"]
   [YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.call
        "\x0016"
        [YulSemantics.Expr.lit (YulSemantics.Literal.number 2048),
         YulSemantics.Expr.var "\x00126",
         YulSemantics.Expr.var "\x00126"]),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.call
        "\x0016"
        [YulSemantics.Expr.lit (YulSemantics.Literal.number 2176),
         YulSemantics.Expr.var "\x00125",
         YulSemantics.Expr.var "\x00125"]),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.call
        "\x0016"
        [YulSemantics.Expr.lit (YulSemantics.Literal.number 2304),
         YulSemantics.Expr.lit (YulSemantics.Literal.number 2176),
         YulSemantics.Expr.var "\x00125"]),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mstore)
        [YulSemantics.Expr.lit (YulSemantics.Literal.number 2432),
         YulSemantics.Expr.lit (YulSemantics.Literal.number 0)]),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mstore)
        [YulSemantics.Expr.lit (YulSemantics.Literal.number 2464),
         YulSemantics.Expr.lit (YulSemantics.Literal.number 4)]),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mstore)
        [YulSemantics.Expr.lit (YulSemantics.Literal.number 2496),
         YulSemantics.Expr.lit (YulSemantics.Literal.number 0)]),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mstore)
        [YulSemantics.Expr.lit (YulSemantics.Literal.number 2528),
         YulSemantics.Expr.lit (YulSemantics.Literal.number 4)]),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.call
        "\x0014"
        [YulSemantics.Expr.lit (YulSemantics.Literal.number 2304),
         YulSemantics.Expr.lit (YulSemantics.Literal.number 2304),
         YulSemantics.Expr.lit (YulSemantics.Literal.number 2432)]),
    YulSemantics.Stmt.assign
      ["\x00127"]
      (YulSemantics.Expr.call
        "\x0013"
        [YulSemantics.Expr.lit (YulSemantics.Literal.number 2048),
         YulSemantics.Expr.lit (YulSemantics.Literal.number 2304)])],
 YulSemantics.Stmt.funDef
   "\x0019"
   ["\x00128"]
   ["\x00129"]
   [YulSemantics.Stmt.assign
      ["\x00129"]
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.iszero)
        [YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.or)
           [YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.or)
              [YulSemantics.Expr.builtin
                 (YulSemantics.EVM.Op.shr)
                 [YulSemantics.Expr.lit (YulSemantics.Literal.number 128),
                  YulSemantics.Expr.builtin (YulSemantics.EVM.Op.mload) [YulSemantics.Expr.var "\x00128"]],
               YulSemantics.Expr.builtin
                 (YulSemantics.EVM.Op.shr)
                 [YulSemantics.Expr.lit (YulSemantics.Literal.number 128),
                  YulSemantics.Expr.builtin
                    (YulSemantics.EVM.Op.mload)
                    [YulSemantics.Expr.builtin
                       (YulSemantics.EVM.Op.add)
                       [YulSemantics.Expr.var "\x00128", YulSemantics.Expr.lit (YulSemantics.Literal.number 64)]]]],
            YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.or)
              [YulSemantics.Expr.builtin
                 (YulSemantics.EVM.Op.shr)
                 [YulSemantics.Expr.lit (YulSemantics.Literal.number 128),
                  YulSemantics.Expr.builtin
                    (YulSemantics.EVM.Op.mload)
                    [YulSemantics.Expr.builtin
                       (YulSemantics.EVM.Op.add)
                       [YulSemantics.Expr.var "\x00128", YulSemantics.Expr.lit (YulSemantics.Literal.number 128)]]],
               YulSemantics.Expr.builtin
                 (YulSemantics.EVM.Op.shr)
                 [YulSemantics.Expr.lit (YulSemantics.Literal.number 128),
                  YulSemantics.Expr.builtin
                    (YulSemantics.EVM.Op.mload)
                    [YulSemantics.Expr.builtin
                       (YulSemantics.EVM.Op.add)
                       [YulSemantics.Expr.var "\x00128",
                        YulSemantics.Expr.lit (YulSemantics.Literal.number 192)]]]]]])]]

end Challenge.Bls12381G2Msm.Reference.Proofs.Compilation

