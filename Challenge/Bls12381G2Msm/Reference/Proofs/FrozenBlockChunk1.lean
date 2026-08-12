import YulParser.Compile

set_option warningAsError true

namespace Challenge.Bls12381G2Msm.Reference.Proofs.Compilation

open YulSemantics (Block)
open YulSemantics.EVM (Op)

/-- Generated normalized AST statements 4 through 7. -/
def frozenReferenceBlockChunk1 : Block Op :=
[YulSemantics.Stmt.funDef
   "\x004"
   ["\x0047", "\x0048", "\x0049", "\x0050"]
   ["\x0051", "\x0052"]
   [YulSemantics.Stmt.assign
      ["\x0052"]
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.add)
        [YulSemantics.Expr.var "\x0048", YulSemantics.Expr.var "\x0050"]),
    YulSemantics.Stmt.assign
      ["\x0051"]
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.add)
        [YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.add)
           [YulSemantics.Expr.var "\x0047", YulSemantics.Expr.var "\x0049"],
         YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.lt)
           [YulSemantics.Expr.var "\x0052", YulSemantics.Expr.var "\x0048"]]),
    YulSemantics.Stmt.cond
      (YulSemantics.Expr.call "\x000" [YulSemantics.Expr.var "\x0051", YulSemantics.Expr.var "\x0052"])
      [YulSemantics.Stmt.letDecl
         ["\x0053"]
         (some (YulSemantics.Expr.lit (YulSemantics.Literal.number 34565483545414906068789196026815425751))),
       YulSemantics.Stmt.letDecl
         ["\x0054"]
         (some (YulSemantics.Expr.lit
            (YulSemantics.Literal.number
              45442060874369865957053122457065728162598490762543039060009208264153100167851))),
       YulSemantics.Stmt.letDecl
         ["\x0055"]
         (some (YulSemantics.Expr.builtin
            (YulSemantics.EVM.Op.sub)
            [YulSemantics.Expr.var "\x0052", YulSemantics.Expr.var "\x0054"])),
       YulSemantics.Stmt.assign
         ["\x0051"]
         (YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.sub)
           [YulSemantics.Expr.var "\x0051",
            YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.add)
              [YulSemantics.Expr.var "\x0053",
               YulSemantics.Expr.builtin
                 (YulSemantics.EVM.Op.gt)
                 [YulSemantics.Expr.var "\x0054", YulSemantics.Expr.var "\x0052"]]]),
       YulSemantics.Stmt.assign ["\x0052"] (YulSemantics.Expr.var "\x0055")]],
 YulSemantics.Stmt.funDef
   "\x005"
   ["\x0056", "\x0057", "\x0058", "\x0059"]
   ["\x0060", "\x0061"]
   [YulSemantics.Stmt.assign
      ["\x0061"]
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.sub)
        [YulSemantics.Expr.var "\x0057", YulSemantics.Expr.var "\x0059"]),
    YulSemantics.Stmt.assign
      ["\x0060"]
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.sub)
        [YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.sub)
           [YulSemantics.Expr.var "\x0056", YulSemantics.Expr.var "\x0058"],
         YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.gt)
           [YulSemantics.Expr.var "\x0059", YulSemantics.Expr.var "\x0057"]]),
    YulSemantics.Stmt.letDecl
      ["\x0062"]
      (some (YulSemantics.Expr.lit (YulSemantics.Literal.number 34565483545414906068789196026815425751))),
    YulSemantics.Stmt.cond
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.gt)
        [YulSemantics.Expr.var "\x0060", YulSemantics.Expr.var "\x0062"])
      [YulSemantics.Stmt.letDecl
         ["\x0063"]
         (some (YulSemantics.Expr.lit
            (YulSemantics.Literal.number
              45442060874369865957053122457065728162598490762543039060009208264153100167851))),
       YulSemantics.Stmt.letDecl
         ["\x0064"]
         (some (YulSemantics.Expr.builtin
            (YulSemantics.EVM.Op.add)
            [YulSemantics.Expr.var "\x0061", YulSemantics.Expr.var "\x0063"])),
       YulSemantics.Stmt.assign
         ["\x0060"]
         (YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.add)
           [YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.add)
              [YulSemantics.Expr.var "\x0060", YulSemantics.Expr.var "\x0062"],
            YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.lt)
              [YulSemantics.Expr.var "\x0064", YulSemantics.Expr.var "\x0061"]]),
       YulSemantics.Stmt.assign ["\x0061"] (YulSemantics.Expr.var "\x0064")]],
 YulSemantics.Stmt.funDef
   "\x006"
   ["\x0065", "\x0066", "\x0067", "\x0068"]
   ["\x0069", "\x0070", "\x0071"]
   [YulSemantics.Stmt.assign
      ["\x0071"]
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mul)
        [YulSemantics.Expr.var "\x0066", YulSemantics.Expr.var "\x0068"]),
    YulSemantics.Stmt.letDecl
      ["\x0072"]
      (some (YulSemantics.Expr.builtin
         (YulSemantics.EVM.Op.mulmod)
         [YulSemantics.Expr.var "\x0066",
          YulSemantics.Expr.var "\x0068",
          YulSemantics.Expr.builtin
            (YulSemantics.EVM.Op.not)
            [YulSemantics.Expr.lit (YulSemantics.Literal.number 0)]])),
    YulSemantics.Stmt.letDecl
      ["\x0073"]
      (some (YulSemantics.Expr.builtin
         (YulSemantics.EVM.Op.sub)
         [YulSemantics.Expr.builtin
            (YulSemantics.EVM.Op.sub)
            [YulSemantics.Expr.var "\x0072", YulSemantics.Expr.var "\x0071"],
          YulSemantics.Expr.builtin
            (YulSemantics.EVM.Op.lt)
            [YulSemantics.Expr.var "\x0072", YulSemantics.Expr.var "\x0071"]])),
    YulSemantics.Stmt.letDecl
      ["\x0074"]
      (some (YulSemantics.Expr.builtin
         (YulSemantics.EVM.Op.mul)
         [YulSemantics.Expr.var "\x0065", YulSemantics.Expr.var "\x0068"])),
    YulSemantics.Stmt.letDecl
      ["\x0075"]
      (some (YulSemantics.Expr.builtin
         (YulSemantics.EVM.Op.mulmod)
         [YulSemantics.Expr.var "\x0065",
          YulSemantics.Expr.var "\x0068",
          YulSemantics.Expr.builtin
            (YulSemantics.EVM.Op.not)
            [YulSemantics.Expr.lit (YulSemantics.Literal.number 0)]])),
    YulSemantics.Stmt.letDecl
      ["\x0076"]
      (some (YulSemantics.Expr.builtin
         (YulSemantics.EVM.Op.sub)
         [YulSemantics.Expr.builtin
            (YulSemantics.EVM.Op.sub)
            [YulSemantics.Expr.var "\x0075", YulSemantics.Expr.var "\x0074"],
          YulSemantics.Expr.builtin
            (YulSemantics.EVM.Op.lt)
            [YulSemantics.Expr.var "\x0075", YulSemantics.Expr.var "\x0074"]])),
    YulSemantics.Stmt.letDecl
      ["\x0077"]
      (some (YulSemantics.Expr.builtin
         (YulSemantics.EVM.Op.mul)
         [YulSemantics.Expr.var "\x0066", YulSemantics.Expr.var "\x0067"])),
    YulSemantics.Stmt.letDecl
      ["\x0078"]
      (some (YulSemantics.Expr.builtin
         (YulSemantics.EVM.Op.mulmod)
         [YulSemantics.Expr.var "\x0066",
          YulSemantics.Expr.var "\x0067",
          YulSemantics.Expr.builtin
            (YulSemantics.EVM.Op.not)
            [YulSemantics.Expr.lit (YulSemantics.Literal.number 0)]])),
    YulSemantics.Stmt.letDecl
      ["\x0079"]
      (some (YulSemantics.Expr.builtin
         (YulSemantics.EVM.Op.sub)
         [YulSemantics.Expr.builtin
            (YulSemantics.EVM.Op.sub)
            [YulSemantics.Expr.var "\x0078", YulSemantics.Expr.var "\x0077"],
          YulSemantics.Expr.builtin
            (YulSemantics.EVM.Op.lt)
            [YulSemantics.Expr.var "\x0078", YulSemantics.Expr.var "\x0077"]])),
    YulSemantics.Stmt.assign
      ["\x0070"]
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.add)
        [YulSemantics.Expr.var "\x0073", YulSemantics.Expr.var "\x0074"]),
    YulSemantics.Stmt.letDecl
      ["\x0080"]
      (some (YulSemantics.Expr.builtin
         (YulSemantics.EVM.Op.lt)
         [YulSemantics.Expr.var "\x0070", YulSemantics.Expr.var "\x0073"])),
    YulSemantics.Stmt.letDecl
      ["\x0081"]
      (some (YulSemantics.Expr.builtin
         (YulSemantics.EVM.Op.add)
         [YulSemantics.Expr.var "\x0070", YulSemantics.Expr.var "\x0077"])),
    YulSemantics.Stmt.assign
      ["\x0080"]
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.add)
        [YulSemantics.Expr.var "\x0080",
         YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.lt)
           [YulSemantics.Expr.var "\x0081", YulSemantics.Expr.var "\x0070"]]),
    YulSemantics.Stmt.assign ["\x0070"] (YulSemantics.Expr.var "\x0081"),
    YulSemantics.Stmt.assign
      ["\x0069"]
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.add)
        [YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.add)
           [YulSemantics.Expr.var "\x0076", YulSemantics.Expr.var "\x0079"],
         YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.add)
           [YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.mul)
              [YulSemantics.Expr.var "\x0065", YulSemantics.Expr.var "\x0067"],
            YulSemantics.Expr.var "\x0080"]])],
 YulSemantics.Stmt.funDef
   "\x007"
   ["\x0082", "\x0083", "\x0084"]
   []
   [YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mstore)
        [YulSemantics.Expr.var "\x0082",
         YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.shl)
           [YulSemantics.Expr.lit (YulSemantics.Literal.number 128), YulSemantics.Expr.var "\x0083"]]),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mstore)
        [YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.add)
           [YulSemantics.Expr.var "\x0082", YulSemantics.Expr.lit (YulSemantics.Literal.number 16)],
         YulSemantics.Expr.var "\x0084"])]]

end Challenge.Bls12381G2Msm.Reference.Proofs.Compilation

