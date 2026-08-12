import YulParser.Compile

set_option warningAsError true

namespace Challenge.Bls12381G2Msm.Reference.Proofs.Compilation

open YulSemantics (Block)
open YulSemantics.EVM (Op)

/-- Generated normalized AST statements 12 through 15. -/
def frozenReferenceBlockChunk3 : Block Op :=
[YulSemantics.Stmt.funDef
   "\x0012"
   ["\x00101"]
   ["\x00102"]
   [YulSemantics.Stmt.assign
      ["\x00102"]
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.and)
        [YulSemantics.Expr.call
           "\x002"
           [YulSemantics.Expr.builtin (YulSemantics.EVM.Op.mload) [YulSemantics.Expr.var "\x00101"],
            YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.mload)
              [YulSemantics.Expr.builtin
                 (YulSemantics.EVM.Op.add)
                 [YulSemantics.Expr.var "\x00101", YulSemantics.Expr.lit (YulSemantics.Literal.number 32)]]],
         YulSemantics.Expr.call
           "\x002"
           [YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.mload)
              [YulSemantics.Expr.builtin
                 (YulSemantics.EVM.Op.add)
                 [YulSemantics.Expr.var "\x00101", YulSemantics.Expr.lit (YulSemantics.Literal.number 64)]],
            YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.mload)
              [YulSemantics.Expr.builtin
                 (YulSemantics.EVM.Op.add)
                 [YulSemantics.Expr.var "\x00101", YulSemantics.Expr.lit (YulSemantics.Literal.number 96)]]]])],
 YulSemantics.Stmt.funDef
   "\x0013"
   ["\x00103", "\x00104"]
   ["\x00105"]
   [YulSemantics.Stmt.assign
      ["\x00105"]
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.and)
        [YulSemantics.Expr.call
           "\x003"
           [YulSemantics.Expr.builtin (YulSemantics.EVM.Op.mload) [YulSemantics.Expr.var "\x00103"],
            YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.mload)
              [YulSemantics.Expr.builtin
                 (YulSemantics.EVM.Op.add)
                 [YulSemantics.Expr.var "\x00103", YulSemantics.Expr.lit (YulSemantics.Literal.number 32)]],
            YulSemantics.Expr.builtin (YulSemantics.EVM.Op.mload) [YulSemantics.Expr.var "\x00104"],
            YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.mload)
              [YulSemantics.Expr.builtin
                 (YulSemantics.EVM.Op.add)
                 [YulSemantics.Expr.var "\x00104", YulSemantics.Expr.lit (YulSemantics.Literal.number 32)]]],
         YulSemantics.Expr.call
           "\x003"
           [YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.mload)
              [YulSemantics.Expr.builtin
                 (YulSemantics.EVM.Op.add)
                 [YulSemantics.Expr.var "\x00103", YulSemantics.Expr.lit (YulSemantics.Literal.number 64)]],
            YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.mload)
              [YulSemantics.Expr.builtin
                 (YulSemantics.EVM.Op.add)
                 [YulSemantics.Expr.var "\x00103", YulSemantics.Expr.lit (YulSemantics.Literal.number 96)]],
            YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.mload)
              [YulSemantics.Expr.builtin
                 (YulSemantics.EVM.Op.add)
                 [YulSemantics.Expr.var "\x00104", YulSemantics.Expr.lit (YulSemantics.Literal.number 64)]],
            YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.mload)
              [YulSemantics.Expr.builtin
                 (YulSemantics.EVM.Op.add)
                 [YulSemantics.Expr.var "\x00104", YulSemantics.Expr.lit (YulSemantics.Literal.number 96)]]]])],
 YulSemantics.Stmt.funDef
   "\x0014"
   ["\x00106", "\x00107", "\x00108"]
   []
   [YulSemantics.Stmt.letDecl
      ["\x00109", "\x00110"]
      (some (YulSemantics.Expr.call
         "\x004"
         [YulSemantics.Expr.builtin (YulSemantics.EVM.Op.mload) [YulSemantics.Expr.var "\x00107"],
          YulSemantics.Expr.builtin
            (YulSemantics.EVM.Op.mload)
            [YulSemantics.Expr.builtin
               (YulSemantics.EVM.Op.add)
               [YulSemantics.Expr.var "\x00107", YulSemantics.Expr.lit (YulSemantics.Literal.number 32)]],
          YulSemantics.Expr.builtin (YulSemantics.EVM.Op.mload) [YulSemantics.Expr.var "\x00108"],
          YulSemantics.Expr.builtin
            (YulSemantics.EVM.Op.mload)
            [YulSemantics.Expr.builtin
               (YulSemantics.EVM.Op.add)
               [YulSemantics.Expr.var "\x00108", YulSemantics.Expr.lit (YulSemantics.Literal.number 32)]]])),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mstore)
        [YulSemantics.Expr.var "\x00106", YulSemantics.Expr.var "\x00109"]),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mstore)
        [YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.add)
           [YulSemantics.Expr.var "\x00106", YulSemantics.Expr.lit (YulSemantics.Literal.number 32)],
         YulSemantics.Expr.var "\x00110"]),
    YulSemantics.Stmt.assign
      ["\x00109", "\x00110"]
      (YulSemantics.Expr.call
        "\x004"
        [YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.mload)
           [YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.add)
              [YulSemantics.Expr.var "\x00107", YulSemantics.Expr.lit (YulSemantics.Literal.number 64)]],
         YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.mload)
           [YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.add)
              [YulSemantics.Expr.var "\x00107", YulSemantics.Expr.lit (YulSemantics.Literal.number 96)]],
         YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.mload)
           [YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.add)
              [YulSemantics.Expr.var "\x00108", YulSemantics.Expr.lit (YulSemantics.Literal.number 64)]],
         YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.mload)
           [YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.add)
              [YulSemantics.Expr.var "\x00108", YulSemantics.Expr.lit (YulSemantics.Literal.number 96)]]]),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mstore)
        [YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.add)
           [YulSemantics.Expr.var "\x00106", YulSemantics.Expr.lit (YulSemantics.Literal.number 64)],
         YulSemantics.Expr.var "\x00109"]),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mstore)
        [YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.add)
           [YulSemantics.Expr.var "\x00106", YulSemantics.Expr.lit (YulSemantics.Literal.number 96)],
         YulSemantics.Expr.var "\x00110"])],
 YulSemantics.Stmt.funDef
   "\x0015"
   ["\x00111", "\x00112", "\x00113"]
   []
   [YulSemantics.Stmt.letDecl
      ["\x00114", "\x00115"]
      (some (YulSemantics.Expr.call
         "\x005"
         [YulSemantics.Expr.builtin (YulSemantics.EVM.Op.mload) [YulSemantics.Expr.var "\x00112"],
          YulSemantics.Expr.builtin
            (YulSemantics.EVM.Op.mload)
            [YulSemantics.Expr.builtin
               (YulSemantics.EVM.Op.add)
               [YulSemantics.Expr.var "\x00112", YulSemantics.Expr.lit (YulSemantics.Literal.number 32)]],
          YulSemantics.Expr.builtin (YulSemantics.EVM.Op.mload) [YulSemantics.Expr.var "\x00113"],
          YulSemantics.Expr.builtin
            (YulSemantics.EVM.Op.mload)
            [YulSemantics.Expr.builtin
               (YulSemantics.EVM.Op.add)
               [YulSemantics.Expr.var "\x00113", YulSemantics.Expr.lit (YulSemantics.Literal.number 32)]]])),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mstore)
        [YulSemantics.Expr.var "\x00111", YulSemantics.Expr.var "\x00114"]),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mstore)
        [YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.add)
           [YulSemantics.Expr.var "\x00111", YulSemantics.Expr.lit (YulSemantics.Literal.number 32)],
         YulSemantics.Expr.var "\x00115"]),
    YulSemantics.Stmt.assign
      ["\x00114", "\x00115"]
      (YulSemantics.Expr.call
        "\x005"
        [YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.mload)
           [YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.add)
              [YulSemantics.Expr.var "\x00112", YulSemantics.Expr.lit (YulSemantics.Literal.number 64)]],
         YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.mload)
           [YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.add)
              [YulSemantics.Expr.var "\x00112", YulSemantics.Expr.lit (YulSemantics.Literal.number 96)]],
         YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.mload)
           [YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.add)
              [YulSemantics.Expr.var "\x00113", YulSemantics.Expr.lit (YulSemantics.Literal.number 64)]],
         YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.mload)
           [YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.add)
              [YulSemantics.Expr.var "\x00113", YulSemantics.Expr.lit (YulSemantics.Literal.number 96)]]]),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mstore)
        [YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.add)
           [YulSemantics.Expr.var "\x00111", YulSemantics.Expr.lit (YulSemantics.Literal.number 64)],
         YulSemantics.Expr.var "\x00114"]),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mstore)
        [YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.add)
           [YulSemantics.Expr.var "\x00111", YulSemantics.Expr.lit (YulSemantics.Literal.number 96)],
         YulSemantics.Expr.var "\x00115"])]]

end Challenge.Bls12381G2Msm.Reference.Proofs.Compilation

