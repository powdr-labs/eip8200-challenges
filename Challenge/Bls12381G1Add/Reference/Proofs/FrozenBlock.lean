import Challenge.Bls12381G1Add.ProofSupport.Yul

set_option warningAsError true

/-!
# Frozen normalized G1ADD block

This is generated ordinary Lean data for the exact normalized source AST.
-/

namespace Challenge.Bls12381G1Add.Reference.Proofs.Compilation

open YulSemantics (Block)
open YulSemantics.EVM (Op)

def frozenReferenceBlock : Block Op :=
[YulSemantics.Stmt.funDef
   "\x000"
   ["\x0013", "\x0014"]
   ["\x0015"]
   [YulSemantics.Stmt.letDecl
      ["\x0016"]
      (some (YulSemantics.Expr.lit (YulSemantics.Literal.number 34565483545414906068789196026815425751))),
    YulSemantics.Stmt.letDecl
      ["\x0017"]
      (some (YulSemantics.Expr.lit
         (YulSemantics.Literal.number 45442060874369865957053122457065728162598490762543039060009208264153100167851))),
    YulSemantics.Stmt.assign
      ["\x0015"]
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.or)
        [YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.gt)
           [YulSemantics.Expr.var "\x0013", YulSemantics.Expr.var "\x0016"],
         YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.and)
           [YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.eq)
              [YulSemantics.Expr.var "\x0013", YulSemantics.Expr.var "\x0016"],
            YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.iszero)
              [YulSemantics.Expr.builtin
                 (YulSemantics.EVM.Op.lt)
                 [YulSemantics.Expr.var "\x0014", YulSemantics.Expr.var "\x0017"]]]])],
 YulSemantics.Stmt.funDef
   "\x001"
   ["\x0018", "\x0019"]
   ["\x0020"]
   [YulSemantics.Stmt.assign
      ["\x0020"]
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.iszero)
        [YulSemantics.Expr.call "\x000" [YulSemantics.Expr.var "\x0018", YulSemantics.Expr.var "\x0019"]])],
 YulSemantics.Stmt.funDef
   "\x002"
   ["\x0021", "\x0022"]
   ["\x0023"]
   [YulSemantics.Stmt.assign
      ["\x0023"]
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.and)
        [YulSemantics.Expr.builtin (YulSemantics.EVM.Op.iszero) [YulSemantics.Expr.var "\x0021"],
         YulSemantics.Expr.builtin (YulSemantics.EVM.Op.iszero) [YulSemantics.Expr.var "\x0022"]])],
 YulSemantics.Stmt.funDef
   "\x003"
   ["\x0024", "\x0025", "\x0026", "\x0027"]
   ["\x0028"]
   [YulSemantics.Stmt.assign
      ["\x0028"]
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.and)
        [YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.eq)
           [YulSemantics.Expr.var "\x0024", YulSemantics.Expr.var "\x0026"],
         YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.eq)
           [YulSemantics.Expr.var "\x0025", YulSemantics.Expr.var "\x0027"]])],
 YulSemantics.Stmt.funDef
   "\x004"
   ["\x0029", "\x0030", "\x0031", "\x0032"]
   ["\x0033", "\x0034"]
   [YulSemantics.Stmt.assign
      ["\x0034"]
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.add)
        [YulSemantics.Expr.var "\x0030", YulSemantics.Expr.var "\x0032"]),
    YulSemantics.Stmt.assign
      ["\x0033"]
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.add)
        [YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.add)
           [YulSemantics.Expr.var "\x0029", YulSemantics.Expr.var "\x0031"],
         YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.lt)
           [YulSemantics.Expr.var "\x0034", YulSemantics.Expr.var "\x0030"]]),
    YulSemantics.Stmt.cond
      (YulSemantics.Expr.call "\x000" [YulSemantics.Expr.var "\x0033", YulSemantics.Expr.var "\x0034"])
      [YulSemantics.Stmt.letDecl
         ["\x0035"]
         (some (YulSemantics.Expr.lit (YulSemantics.Literal.number 34565483545414906068789196026815425751))),
       YulSemantics.Stmt.letDecl
         ["\x0036"]
         (some (YulSemantics.Expr.lit
            (YulSemantics.Literal.number
              45442060874369865957053122457065728162598490762543039060009208264153100167851))),
       YulSemantics.Stmt.letDecl
         ["\x0037"]
         (some (YulSemantics.Expr.builtin
            (YulSemantics.EVM.Op.sub)
            [YulSemantics.Expr.var "\x0034", YulSemantics.Expr.var "\x0036"])),
       YulSemantics.Stmt.assign
         ["\x0033"]
         (YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.sub)
           [YulSemantics.Expr.var "\x0033",
            YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.add)
              [YulSemantics.Expr.var "\x0035",
               YulSemantics.Expr.builtin
                 (YulSemantics.EVM.Op.gt)
                 [YulSemantics.Expr.var "\x0036", YulSemantics.Expr.var "\x0034"]]]),
       YulSemantics.Stmt.assign ["\x0034"] (YulSemantics.Expr.var "\x0037")]],
 YulSemantics.Stmt.funDef
   "\x005"
   ["\x0038", "\x0039", "\x0040", "\x0041"]
   ["\x0042", "\x0043"]
   [YulSemantics.Stmt.assign
      ["\x0043"]
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.sub)
        [YulSemantics.Expr.var "\x0039", YulSemantics.Expr.var "\x0041"]),
    YulSemantics.Stmt.assign
      ["\x0042"]
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.sub)
        [YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.sub)
           [YulSemantics.Expr.var "\x0038", YulSemantics.Expr.var "\x0040"],
         YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.gt)
           [YulSemantics.Expr.var "\x0041", YulSemantics.Expr.var "\x0039"]]),
    YulSemantics.Stmt.letDecl
      ["\x0044"]
      (some (YulSemantics.Expr.lit (YulSemantics.Literal.number 34565483545414906068789196026815425751))),
    YulSemantics.Stmt.cond
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.gt)
        [YulSemantics.Expr.var "\x0042", YulSemantics.Expr.var "\x0044"])
      [YulSemantics.Stmt.letDecl
         ["\x0045"]
         (some (YulSemantics.Expr.lit
            (YulSemantics.Literal.number
              45442060874369865957053122457065728162598490762543039060009208264153100167851))),
       YulSemantics.Stmt.letDecl
         ["\x0046"]
         (some (YulSemantics.Expr.builtin
            (YulSemantics.EVM.Op.add)
            [YulSemantics.Expr.var "\x0043", YulSemantics.Expr.var "\x0045"])),
       YulSemantics.Stmt.assign
         ["\x0042"]
         (YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.add)
           [YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.add)
              [YulSemantics.Expr.var "\x0042", YulSemantics.Expr.var "\x0044"],
            YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.lt)
              [YulSemantics.Expr.var "\x0046", YulSemantics.Expr.var "\x0043"]]),
       YulSemantics.Stmt.assign ["\x0043"] (YulSemantics.Expr.var "\x0046")]],
 YulSemantics.Stmt.funDef
   "\x006"
   ["\x0047", "\x0048", "\x0049", "\x0050"]
   ["\x0051", "\x0052", "\x0053"]
   [YulSemantics.Stmt.assign
      ["\x0053"]
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mul)
        [YulSemantics.Expr.var "\x0048", YulSemantics.Expr.var "\x0050"]),
    YulSemantics.Stmt.letDecl
      ["\x0054"]
      (some (YulSemantics.Expr.builtin
         (YulSemantics.EVM.Op.mulmod)
         [YulSemantics.Expr.var "\x0048",
          YulSemantics.Expr.var "\x0050",
          YulSemantics.Expr.builtin
            (YulSemantics.EVM.Op.not)
            [YulSemantics.Expr.lit (YulSemantics.Literal.number 0)]])),
    YulSemantics.Stmt.letDecl
      ["\x0055"]
      (some (YulSemantics.Expr.builtin
         (YulSemantics.EVM.Op.sub)
         [YulSemantics.Expr.builtin
            (YulSemantics.EVM.Op.sub)
            [YulSemantics.Expr.var "\x0054", YulSemantics.Expr.var "\x0053"],
          YulSemantics.Expr.builtin
            (YulSemantics.EVM.Op.lt)
            [YulSemantics.Expr.var "\x0054", YulSemantics.Expr.var "\x0053"]])),
    YulSemantics.Stmt.letDecl
      ["\x0056"]
      (some (YulSemantics.Expr.builtin
         (YulSemantics.EVM.Op.mul)
         [YulSemantics.Expr.var "\x0047", YulSemantics.Expr.var "\x0050"])),
    YulSemantics.Stmt.letDecl
      ["\x0057"]
      (some (YulSemantics.Expr.builtin
         (YulSemantics.EVM.Op.mulmod)
         [YulSemantics.Expr.var "\x0047",
          YulSemantics.Expr.var "\x0050",
          YulSemantics.Expr.builtin
            (YulSemantics.EVM.Op.not)
            [YulSemantics.Expr.lit (YulSemantics.Literal.number 0)]])),
    YulSemantics.Stmt.letDecl
      ["\x0058"]
      (some (YulSemantics.Expr.builtin
         (YulSemantics.EVM.Op.sub)
         [YulSemantics.Expr.builtin
            (YulSemantics.EVM.Op.sub)
            [YulSemantics.Expr.var "\x0057", YulSemantics.Expr.var "\x0056"],
          YulSemantics.Expr.builtin
            (YulSemantics.EVM.Op.lt)
            [YulSemantics.Expr.var "\x0057", YulSemantics.Expr.var "\x0056"]])),
    YulSemantics.Stmt.letDecl
      ["\x0059"]
      (some (YulSemantics.Expr.builtin
         (YulSemantics.EVM.Op.mul)
         [YulSemantics.Expr.var "\x0048", YulSemantics.Expr.var "\x0049"])),
    YulSemantics.Stmt.letDecl
      ["\x0060"]
      (some (YulSemantics.Expr.builtin
         (YulSemantics.EVM.Op.mulmod)
         [YulSemantics.Expr.var "\x0048",
          YulSemantics.Expr.var "\x0049",
          YulSemantics.Expr.builtin
            (YulSemantics.EVM.Op.not)
            [YulSemantics.Expr.lit (YulSemantics.Literal.number 0)]])),
    YulSemantics.Stmt.letDecl
      ["\x0061"]
      (some (YulSemantics.Expr.builtin
         (YulSemantics.EVM.Op.sub)
         [YulSemantics.Expr.builtin
            (YulSemantics.EVM.Op.sub)
            [YulSemantics.Expr.var "\x0060", YulSemantics.Expr.var "\x0059"],
          YulSemantics.Expr.builtin
            (YulSemantics.EVM.Op.lt)
            [YulSemantics.Expr.var "\x0060", YulSemantics.Expr.var "\x0059"]])),
    YulSemantics.Stmt.assign
      ["\x0052"]
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.add)
        [YulSemantics.Expr.var "\x0055", YulSemantics.Expr.var "\x0056"]),
    YulSemantics.Stmt.letDecl
      ["\x0062"]
      (some (YulSemantics.Expr.builtin
         (YulSemantics.EVM.Op.lt)
         [YulSemantics.Expr.var "\x0052", YulSemantics.Expr.var "\x0055"])),
    YulSemantics.Stmt.letDecl
      ["\x0063"]
      (some (YulSemantics.Expr.builtin
         (YulSemantics.EVM.Op.add)
         [YulSemantics.Expr.var "\x0052", YulSemantics.Expr.var "\x0059"])),
    YulSemantics.Stmt.assign
      ["\x0062"]
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.add)
        [YulSemantics.Expr.var "\x0062",
         YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.lt)
           [YulSemantics.Expr.var "\x0063", YulSemantics.Expr.var "\x0052"]]),
    YulSemantics.Stmt.assign ["\x0052"] (YulSemantics.Expr.var "\x0063"),
    YulSemantics.Stmt.assign
      ["\x0051"]
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.add)
        [YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.add)
           [YulSemantics.Expr.var "\x0058", YulSemantics.Expr.var "\x0061"],
         YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.add)
           [YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.mul)
              [YulSemantics.Expr.var "\x0047", YulSemantics.Expr.var "\x0049"],
            YulSemantics.Expr.var "\x0062"]])],
 YulSemantics.Stmt.funDef
   "\x007"
   ["\x0064", "\x0065", "\x0066"]
   []
   [YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mstore)
        [YulSemantics.Expr.var "\x0064",
         YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.shl)
           [YulSemantics.Expr.lit (YulSemantics.Literal.number 128), YulSemantics.Expr.var "\x0065"]]),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mstore)
        [YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.add)
           [YulSemantics.Expr.var "\x0064", YulSemantics.Expr.lit (YulSemantics.Literal.number 16)],
         YulSemantics.Expr.var "\x0066"])],
 YulSemantics.Stmt.funDef
   "\x008"
   ["\x0067"]
   []
   [YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.call
        "\x007"
        [YulSemantics.Expr.var "\x0067",
         YulSemantics.Expr.lit (YulSemantics.Literal.number 34565483545414906068789196026815425751),
         YulSemantics.Expr.lit
           (YulSemantics.Literal.number
             45442060874369865957053122457065728162598490762543039060009208264153100167851)])],
 YulSemantics.Stmt.funDef
   "\x009"
   ["\x0068", "\x0069", "\x0070", "\x0071"]
   ["\x0072", "\x0073"]
   [YulSemantics.Stmt.letDecl
      ["\x0074", "\x0075", "\x0076"]
      (some (YulSemantics.Expr.call
         "\x006"
         [YulSemantics.Expr.var "\x0068",
          YulSemantics.Expr.var "\x0069",
          YulSemantics.Expr.var "\x0070",
          YulSemantics.Expr.var "\x0071"])),
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
        [YulSemantics.Expr.lit (YulSemantics.Literal.number 1120), YulSemantics.Expr.var "\x0074"]),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mstore)
        [YulSemantics.Expr.lit (YulSemantics.Literal.number 1152), YulSemantics.Expr.var "\x0075"]),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mstore)
        [YulSemantics.Expr.lit (YulSemantics.Literal.number 1184), YulSemantics.Expr.var "\x0076"]),
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
      ["\x0072"]
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.shr)
        [YulSemantics.Expr.lit (YulSemantics.Literal.number 128),
         YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.mload)
           [YulSemantics.Expr.lit (YulSemantics.Literal.number 1280)]]),
    YulSemantics.Stmt.assign
      ["\x0073"]
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mload)
        [YulSemantics.Expr.lit (YulSemantics.Literal.number 1296)])],
 YulSemantics.Stmt.funDef
   "\x0010"
   ["\x0077", "\x0078"]
   ["\x0079", "\x0080"]
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
         YulSemantics.Expr.var "\x0077",
         YulSemantics.Expr.var "\x0078"]),
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
      ["\x0079"]
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.shr)
        [YulSemantics.Expr.lit (YulSemantics.Literal.number 128),
         YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.mload)
           [YulSemantics.Expr.lit (YulSemantics.Literal.number 1280)]]),
    YulSemantics.Stmt.assign
      ["\x0080"]
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mload)
        [YulSemantics.Expr.lit (YulSemantics.Literal.number 1296)])],
 YulSemantics.Stmt.funDef
   "\x0011"
   ["\x0081", "\x0082", "\x0083", "\x0084"]
   ["\x0085"]
   [YulSemantics.Stmt.letDecl
      ["\x0086", "\x0087"]
      (some (YulSemantics.Expr.call
         "\x009"
         [YulSemantics.Expr.var "\x0083",
          YulSemantics.Expr.var "\x0084",
          YulSemantics.Expr.var "\x0083",
          YulSemantics.Expr.var "\x0084"])),
    YulSemantics.Stmt.letDecl
      ["\x0088", "\x0089"]
      (some (YulSemantics.Expr.call
         "\x009"
         [YulSemantics.Expr.var "\x0081",
          YulSemantics.Expr.var "\x0082",
          YulSemantics.Expr.var "\x0081",
          YulSemantics.Expr.var "\x0082"])),
    YulSemantics.Stmt.letDecl
      ["\x0090", "\x0091"]
      (some (YulSemantics.Expr.call
         "\x009"
         [YulSemantics.Expr.var "\x0088",
          YulSemantics.Expr.var "\x0089",
          YulSemantics.Expr.var "\x0081",
          YulSemantics.Expr.var "\x0082"])),
    YulSemantics.Stmt.assign
      ["\x0090", "\x0091"]
      (YulSemantics.Expr.call
        "\x004"
        [YulSemantics.Expr.var "\x0090",
         YulSemantics.Expr.var "\x0091",
         YulSemantics.Expr.lit (YulSemantics.Literal.number 0),
         YulSemantics.Expr.lit (YulSemantics.Literal.number 4)]),
    YulSemantics.Stmt.assign
      ["\x0085"]
      (YulSemantics.Expr.call
        "\x003"
        [YulSemantics.Expr.var "\x0086",
         YulSemantics.Expr.var "\x0087",
         YulSemantics.Expr.var "\x0090",
         YulSemantics.Expr.var "\x0091"])],
 YulSemantics.Stmt.funDef
   "\x0012"
   ["\x0092", "\x0093", "\x0094", "\x0095"]
   []
   [YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mstore)
        [YulSemantics.Expr.lit (YulSemantics.Literal.number 0), YulSemantics.Expr.var "\x0092"]),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mstore)
        [YulSemantics.Expr.lit (YulSemantics.Literal.number 32), YulSemantics.Expr.var "\x0093"]),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mstore)
        [YulSemantics.Expr.lit (YulSemantics.Literal.number 64), YulSemantics.Expr.var "\x0094"]),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mstore)
        [YulSemantics.Expr.lit (YulSemantics.Literal.number 96), YulSemantics.Expr.var "\x0095"])],
 YulSemantics.Stmt.cond
   (YulSemantics.Expr.builtin
     (YulSemantics.EVM.Op.iszero)
     [YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.eq)
        [YulSemantics.Expr.builtin (YulSemantics.EVM.Op.calldatasize) [],
         YulSemantics.Expr.lit (YulSemantics.Literal.number 256)]])
   [YulSemantics.Stmt.exprStmt (YulSemantics.Expr.builtin (YulSemantics.EVM.Op.invalid) [])],
 YulSemantics.Stmt.exprStmt
   (YulSemantics.Expr.builtin
     (YulSemantics.EVM.Op.mstore)
     [YulSemantics.Expr.lit (YulSemantics.Literal.number 0),
      YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.calldataload)
        [YulSemantics.Expr.lit (YulSemantics.Literal.number 0)]]),
 YulSemantics.Stmt.exprStmt
   (YulSemantics.Expr.builtin
     (YulSemantics.EVM.Op.mstore)
     [YulSemantics.Expr.lit (YulSemantics.Literal.number 32),
      YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.calldataload)
        [YulSemantics.Expr.lit (YulSemantics.Literal.number 32)]]),
 YulSemantics.Stmt.exprStmt
   (YulSemantics.Expr.builtin
     (YulSemantics.EVM.Op.mstore)
     [YulSemantics.Expr.lit (YulSemantics.Literal.number 64),
      YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.calldataload)
        [YulSemantics.Expr.lit (YulSemantics.Literal.number 64)]]),
 YulSemantics.Stmt.exprStmt
   (YulSemantics.Expr.builtin
     (YulSemantics.EVM.Op.mstore)
     [YulSemantics.Expr.lit (YulSemantics.Literal.number 96),
      YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.calldataload)
        [YulSemantics.Expr.lit (YulSemantics.Literal.number 96)]]),
 YulSemantics.Stmt.exprStmt
   (YulSemantics.Expr.builtin
     (YulSemantics.EVM.Op.mstore)
     [YulSemantics.Expr.lit (YulSemantics.Literal.number 128),
      YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.calldataload)
        [YulSemantics.Expr.lit (YulSemantics.Literal.number 128)]]),
 YulSemantics.Stmt.exprStmt
   (YulSemantics.Expr.builtin
     (YulSemantics.EVM.Op.mstore)
     [YulSemantics.Expr.lit (YulSemantics.Literal.number 160),
      YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.calldataload)
        [YulSemantics.Expr.lit (YulSemantics.Literal.number 160)]]),
 YulSemantics.Stmt.exprStmt
   (YulSemantics.Expr.builtin
     (YulSemantics.EVM.Op.mstore)
     [YulSemantics.Expr.lit (YulSemantics.Literal.number 192),
      YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.calldataload)
        [YulSemantics.Expr.lit (YulSemantics.Literal.number 192)]]),
 YulSemantics.Stmt.exprStmt
   (YulSemantics.Expr.builtin
     (YulSemantics.EVM.Op.mstore)
     [YulSemantics.Expr.lit (YulSemantics.Literal.number 224),
      YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.calldataload)
        [YulSemantics.Expr.lit (YulSemantics.Literal.number 224)]]),
 YulSemantics.Stmt.cond
   (YulSemantics.Expr.builtin
     (YulSemantics.EVM.Op.or)
     [YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.or)
        [YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.shr)
           [YulSemantics.Expr.lit (YulSemantics.Literal.number 128),
            YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.mload)
              [YulSemantics.Expr.lit (YulSemantics.Literal.number 0)]],
         YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.shr)
           [YulSemantics.Expr.lit (YulSemantics.Literal.number 128),
            YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.mload)
              [YulSemantics.Expr.lit (YulSemantics.Literal.number 64)]]],
      YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.or)
        [YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.shr)
           [YulSemantics.Expr.lit (YulSemantics.Literal.number 128),
            YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.mload)
              [YulSemantics.Expr.lit (YulSemantics.Literal.number 128)]],
         YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.shr)
           [YulSemantics.Expr.lit (YulSemantics.Literal.number 128),
            YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.mload)
              [YulSemantics.Expr.lit (YulSemantics.Literal.number 192)]]]])
   [YulSemantics.Stmt.exprStmt (YulSemantics.Expr.builtin (YulSemantics.EVM.Op.invalid) [])],
 YulSemantics.Stmt.cond
   (YulSemantics.Expr.builtin
     (YulSemantics.EVM.Op.iszero)
     [YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.and)
        [YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.and)
           [YulSemantics.Expr.call
              "\x001"
              [YulSemantics.Expr.builtin
                 (YulSemantics.EVM.Op.mload)
                 [YulSemantics.Expr.lit (YulSemantics.Literal.number 0)],
               YulSemantics.Expr.builtin
                 (YulSemantics.EVM.Op.mload)
                 [YulSemantics.Expr.lit (YulSemantics.Literal.number 32)]],
            YulSemantics.Expr.call
              "\x001"
              [YulSemantics.Expr.builtin
                 (YulSemantics.EVM.Op.mload)
                 [YulSemantics.Expr.lit (YulSemantics.Literal.number 64)],
               YulSemantics.Expr.builtin
                 (YulSemantics.EVM.Op.mload)
                 [YulSemantics.Expr.lit (YulSemantics.Literal.number 96)]]],
         YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.and)
           [YulSemantics.Expr.call
              "\x001"
              [YulSemantics.Expr.builtin
                 (YulSemantics.EVM.Op.mload)
                 [YulSemantics.Expr.lit (YulSemantics.Literal.number 128)],
               YulSemantics.Expr.builtin
                 (YulSemantics.EVM.Op.mload)
                 [YulSemantics.Expr.lit (YulSemantics.Literal.number 160)]],
            YulSemantics.Expr.call
              "\x001"
              [YulSemantics.Expr.builtin
                 (YulSemantics.EVM.Op.mload)
                 [YulSemantics.Expr.lit (YulSemantics.Literal.number 192)],
               YulSemantics.Expr.builtin
                 (YulSemantics.EVM.Op.mload)
                 [YulSemantics.Expr.lit (YulSemantics.Literal.number 224)]]]]])
   [YulSemantics.Stmt.exprStmt (YulSemantics.Expr.builtin (YulSemantics.EVM.Op.invalid) [])],
 YulSemantics.Stmt.block
   [YulSemantics.Stmt.letDecl
      ["\x0096"]
      (some (YulSemantics.Expr.builtin
         (YulSemantics.EVM.Op.and)
         [YulSemantics.Expr.call
            "\x002"
            [YulSemantics.Expr.builtin
               (YulSemantics.EVM.Op.mload)
               [YulSemantics.Expr.lit (YulSemantics.Literal.number 0)],
             YulSemantics.Expr.builtin
               (YulSemantics.EVM.Op.mload)
               [YulSemantics.Expr.lit (YulSemantics.Literal.number 32)]],
          YulSemantics.Expr.call
            "\x002"
            [YulSemantics.Expr.builtin
               (YulSemantics.EVM.Op.mload)
               [YulSemantics.Expr.lit (YulSemantics.Literal.number 64)],
             YulSemantics.Expr.builtin
               (YulSemantics.EVM.Op.mload)
               [YulSemantics.Expr.lit (YulSemantics.Literal.number 96)]]])),
    YulSemantics.Stmt.letDecl
      ["\x0097"]
      (some (YulSemantics.Expr.builtin
         (YulSemantics.EVM.Op.and)
         [YulSemantics.Expr.call
            "\x002"
            [YulSemantics.Expr.builtin
               (YulSemantics.EVM.Op.mload)
               [YulSemantics.Expr.lit (YulSemantics.Literal.number 128)],
             YulSemantics.Expr.builtin
               (YulSemantics.EVM.Op.mload)
               [YulSemantics.Expr.lit (YulSemantics.Literal.number 160)]],
          YulSemantics.Expr.call
            "\x002"
            [YulSemantics.Expr.builtin
               (YulSemantics.EVM.Op.mload)
               [YulSemantics.Expr.lit (YulSemantics.Literal.number 192)],
             YulSemantics.Expr.builtin
               (YulSemantics.EVM.Op.mload)
               [YulSemantics.Expr.lit (YulSemantics.Literal.number 224)]]])),
    YulSemantics.Stmt.cond
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.and)
        [YulSemantics.Expr.builtin (YulSemantics.EVM.Op.iszero) [YulSemantics.Expr.var "\x0096"],
         YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.iszero)
           [YulSemantics.Expr.call
              "\x0011"
              [YulSemantics.Expr.builtin
                 (YulSemantics.EVM.Op.mload)
                 [YulSemantics.Expr.lit (YulSemantics.Literal.number 0)],
               YulSemantics.Expr.builtin
                 (YulSemantics.EVM.Op.mload)
                 [YulSemantics.Expr.lit (YulSemantics.Literal.number 32)],
               YulSemantics.Expr.builtin
                 (YulSemantics.EVM.Op.mload)
                 [YulSemantics.Expr.lit (YulSemantics.Literal.number 64)],
               YulSemantics.Expr.builtin
                 (YulSemantics.EVM.Op.mload)
                 [YulSemantics.Expr.lit (YulSemantics.Literal.number 96)]]]])
      [YulSemantics.Stmt.exprStmt (YulSemantics.Expr.builtin (YulSemantics.EVM.Op.invalid) [])],
    YulSemantics.Stmt.cond
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.and)
        [YulSemantics.Expr.builtin (YulSemantics.EVM.Op.iszero) [YulSemantics.Expr.var "\x0097"],
         YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.iszero)
           [YulSemantics.Expr.call
              "\x0011"
              [YulSemantics.Expr.builtin
                 (YulSemantics.EVM.Op.mload)
                 [YulSemantics.Expr.lit (YulSemantics.Literal.number 128)],
               YulSemantics.Expr.builtin
                 (YulSemantics.EVM.Op.mload)
                 [YulSemantics.Expr.lit (YulSemantics.Literal.number 160)],
               YulSemantics.Expr.builtin
                 (YulSemantics.EVM.Op.mload)
                 [YulSemantics.Expr.lit (YulSemantics.Literal.number 192)],
               YulSemantics.Expr.builtin
                 (YulSemantics.EVM.Op.mload)
                 [YulSemantics.Expr.lit (YulSemantics.Literal.number 224)]]]])
      [YulSemantics.Stmt.exprStmt (YulSemantics.Expr.builtin (YulSemantics.EVM.Op.invalid) [])],
    YulSemantics.Stmt.cond
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.and)
        [YulSemantics.Expr.var "\x0096", YulSemantics.Expr.var "\x0097"])
      [YulSemantics.Stmt.exprStmt
         (YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.ret)
           [YulSemantics.Expr.lit (YulSemantics.Literal.number 0),
            YulSemantics.Expr.lit (YulSemantics.Literal.number 128)])],
    YulSemantics.Stmt.cond
      (YulSemantics.Expr.var "\x0096")
      [YulSemantics.Stmt.exprStmt
         (YulSemantics.Expr.call
           "\x0012"
           [YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.mload)
              [YulSemantics.Expr.lit (YulSemantics.Literal.number 128)],
            YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.mload)
              [YulSemantics.Expr.lit (YulSemantics.Literal.number 160)],
            YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.mload)
              [YulSemantics.Expr.lit (YulSemantics.Literal.number 192)],
            YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.mload)
              [YulSemantics.Expr.lit (YulSemantics.Literal.number 224)]]),
       YulSemantics.Stmt.exprStmt
         (YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.ret)
           [YulSemantics.Expr.lit (YulSemantics.Literal.number 0),
            YulSemantics.Expr.lit (YulSemantics.Literal.number 128)])],
    YulSemantics.Stmt.cond
      (YulSemantics.Expr.var "\x0097")
      [YulSemantics.Stmt.exprStmt
         (YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.ret)
           [YulSemantics.Expr.lit (YulSemantics.Literal.number 0),
            YulSemantics.Expr.lit (YulSemantics.Literal.number 128)])]],
 YulSemantics.Stmt.letDecl ["\x0098", "\x0099"] none,
 YulSemantics.Stmt.cond
   (YulSemantics.Expr.call
     "\x003"
     [YulSemantics.Expr.builtin (YulSemantics.EVM.Op.mload) [YulSemantics.Expr.lit (YulSemantics.Literal.number 0)],
      YulSemantics.Expr.builtin (YulSemantics.EVM.Op.mload) [YulSemantics.Expr.lit (YulSemantics.Literal.number 32)],
      YulSemantics.Expr.builtin (YulSemantics.EVM.Op.mload) [YulSemantics.Expr.lit (YulSemantics.Literal.number 128)],
      YulSemantics.Expr.builtin (YulSemantics.EVM.Op.mload) [YulSemantics.Expr.lit (YulSemantics.Literal.number 160)]])
   [YulSemantics.Stmt.cond
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.iszero)
        [YulSemantics.Expr.call
           "\x003"
           [YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.mload)
              [YulSemantics.Expr.lit (YulSemantics.Literal.number 64)],
            YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.mload)
              [YulSemantics.Expr.lit (YulSemantics.Literal.number 96)],
            YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.mload)
              [YulSemantics.Expr.lit (YulSemantics.Literal.number 192)],
            YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.mload)
              [YulSemantics.Expr.lit (YulSemantics.Literal.number 224)]]])
      [YulSemantics.Stmt.exprStmt
         (YulSemantics.Expr.call
           "\x0012"
           [YulSemantics.Expr.lit (YulSemantics.Literal.number 0),
            YulSemantics.Expr.lit (YulSemantics.Literal.number 0),
            YulSemantics.Expr.lit (YulSemantics.Literal.number 0),
            YulSemantics.Expr.lit (YulSemantics.Literal.number 0)]),
       YulSemantics.Stmt.exprStmt
         (YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.ret)
           [YulSemantics.Expr.lit (YulSemantics.Literal.number 0),
            YulSemantics.Expr.lit (YulSemantics.Literal.number 128)])],
    YulSemantics.Stmt.cond
      (YulSemantics.Expr.call
        "\x002"
        [YulSemantics.Expr.builtin (YulSemantics.EVM.Op.mload) [YulSemantics.Expr.lit (YulSemantics.Literal.number 64)],
         YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.mload)
           [YulSemantics.Expr.lit (YulSemantics.Literal.number 96)]])
      [YulSemantics.Stmt.exprStmt
         (YulSemantics.Expr.call
           "\x0012"
           [YulSemantics.Expr.lit (YulSemantics.Literal.number 0),
            YulSemantics.Expr.lit (YulSemantics.Literal.number 0),
            YulSemantics.Expr.lit (YulSemantics.Literal.number 0),
            YulSemantics.Expr.lit (YulSemantics.Literal.number 0)]),
       YulSemantics.Stmt.exprStmt
         (YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.ret)
           [YulSemantics.Expr.lit (YulSemantics.Literal.number 0),
            YulSemantics.Expr.lit (YulSemantics.Literal.number 128)])],
    YulSemantics.Stmt.letDecl
      ["\x00100", "\x00101"]
      (some (YulSemantics.Expr.call
         "\x009"
         [YulSemantics.Expr.builtin (YulSemantics.EVM.Op.mload) [YulSemantics.Expr.lit (YulSemantics.Literal.number 0)],
          YulSemantics.Expr.builtin
            (YulSemantics.EVM.Op.mload)
            [YulSemantics.Expr.lit (YulSemantics.Literal.number 32)],
          YulSemantics.Expr.builtin (YulSemantics.EVM.Op.mload) [YulSemantics.Expr.lit (YulSemantics.Literal.number 0)],
          YulSemantics.Expr.builtin
            (YulSemantics.EVM.Op.mload)
            [YulSemantics.Expr.lit (YulSemantics.Literal.number 32)]])),
    YulSemantics.Stmt.letDecl
      ["\x00102", "\x00103"]
      (some (YulSemantics.Expr.call
         "\x004"
         [YulSemantics.Expr.var "\x00100",
          YulSemantics.Expr.var "\x00101",
          YulSemantics.Expr.var "\x00100",
          YulSemantics.Expr.var "\x00101"])),
    YulSemantics.Stmt.assign
      ["\x00102", "\x00103"]
      (YulSemantics.Expr.call
        "\x004"
        [YulSemantics.Expr.var "\x00102",
         YulSemantics.Expr.var "\x00103",
         YulSemantics.Expr.var "\x00100",
         YulSemantics.Expr.var "\x00101"]),
    YulSemantics.Stmt.letDecl
      ["\x00104", "\x00105"]
      (some (YulSemantics.Expr.call
         "\x004"
         [YulSemantics.Expr.builtin
            (YulSemantics.EVM.Op.mload)
            [YulSemantics.Expr.lit (YulSemantics.Literal.number 64)],
          YulSemantics.Expr.builtin
            (YulSemantics.EVM.Op.mload)
            [YulSemantics.Expr.lit (YulSemantics.Literal.number 96)],
          YulSemantics.Expr.builtin
            (YulSemantics.EVM.Op.mload)
            [YulSemantics.Expr.lit (YulSemantics.Literal.number 64)],
          YulSemantics.Expr.builtin
            (YulSemantics.EVM.Op.mload)
            [YulSemantics.Expr.lit (YulSemantics.Literal.number 96)]])),
    YulSemantics.Stmt.letDecl
      ["\x00106", "\x00107"]
      (some (YulSemantics.Expr.call "\x0010" [YulSemantics.Expr.var "\x00104", YulSemantics.Expr.var "\x00105"])),
    YulSemantics.Stmt.assign
      ["\x0098", "\x0099"]
      (YulSemantics.Expr.call
        "\x009"
        [YulSemantics.Expr.var "\x00102",
         YulSemantics.Expr.var "\x00103",
         YulSemantics.Expr.var "\x00106",
         YulSemantics.Expr.var "\x00107"])],
 YulSemantics.Stmt.cond
   (YulSemantics.Expr.builtin
     (YulSemantics.EVM.Op.iszero)
     [YulSemantics.Expr.call
        "\x003"
        [YulSemantics.Expr.builtin (YulSemantics.EVM.Op.mload) [YulSemantics.Expr.lit (YulSemantics.Literal.number 0)],
         YulSemantics.Expr.builtin (YulSemantics.EVM.Op.mload) [YulSemantics.Expr.lit (YulSemantics.Literal.number 32)],
         YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.mload)
           [YulSemantics.Expr.lit (YulSemantics.Literal.number 128)],
         YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.mload)
           [YulSemantics.Expr.lit (YulSemantics.Literal.number 160)]]])
   [YulSemantics.Stmt.letDecl
      ["\x00108", "\x00109"]
      (some (YulSemantics.Expr.call
         "\x005"
         [YulSemantics.Expr.builtin
            (YulSemantics.EVM.Op.mload)
            [YulSemantics.Expr.lit (YulSemantics.Literal.number 192)],
          YulSemantics.Expr.builtin
            (YulSemantics.EVM.Op.mload)
            [YulSemantics.Expr.lit (YulSemantics.Literal.number 224)],
          YulSemantics.Expr.builtin
            (YulSemantics.EVM.Op.mload)
            [YulSemantics.Expr.lit (YulSemantics.Literal.number 64)],
          YulSemantics.Expr.builtin
            (YulSemantics.EVM.Op.mload)
            [YulSemantics.Expr.lit (YulSemantics.Literal.number 96)]])),
    YulSemantics.Stmt.letDecl
      ["\x00110", "\x00111"]
      (some (YulSemantics.Expr.call
         "\x005"
         [YulSemantics.Expr.builtin
            (YulSemantics.EVM.Op.mload)
            [YulSemantics.Expr.lit (YulSemantics.Literal.number 128)],
          YulSemantics.Expr.builtin
            (YulSemantics.EVM.Op.mload)
            [YulSemantics.Expr.lit (YulSemantics.Literal.number 160)],
          YulSemantics.Expr.builtin (YulSemantics.EVM.Op.mload) [YulSemantics.Expr.lit (YulSemantics.Literal.number 0)],
          YulSemantics.Expr.builtin
            (YulSemantics.EVM.Op.mload)
            [YulSemantics.Expr.lit (YulSemantics.Literal.number 32)]])),
    YulSemantics.Stmt.letDecl
      ["\x00112", "\x00113"]
      (some (YulSemantics.Expr.call "\x0010" [YulSemantics.Expr.var "\x00110", YulSemantics.Expr.var "\x00111"])),
    YulSemantics.Stmt.assign
      ["\x0098", "\x0099"]
      (YulSemantics.Expr.call
        "\x009"
        [YulSemantics.Expr.var "\x00108",
         YulSemantics.Expr.var "\x00109",
         YulSemantics.Expr.var "\x00112",
         YulSemantics.Expr.var "\x00113"])],
 YulSemantics.Stmt.letDecl
   ["\x00114", "\x00115"]
   (some (YulSemantics.Expr.call
      "\x009"
      [YulSemantics.Expr.var "\x0098",
       YulSemantics.Expr.var "\x0099",
       YulSemantics.Expr.var "\x0098",
       YulSemantics.Expr.var "\x0099"])),
 YulSemantics.Stmt.assign
   ["\x00114", "\x00115"]
   (YulSemantics.Expr.call
     "\x005"
     [YulSemantics.Expr.var "\x00114",
      YulSemantics.Expr.var "\x00115",
      YulSemantics.Expr.builtin (YulSemantics.EVM.Op.mload) [YulSemantics.Expr.lit (YulSemantics.Literal.number 0)],
      YulSemantics.Expr.builtin (YulSemantics.EVM.Op.mload) [YulSemantics.Expr.lit (YulSemantics.Literal.number 32)]]),
 YulSemantics.Stmt.assign
   ["\x00114", "\x00115"]
   (YulSemantics.Expr.call
     "\x005"
     [YulSemantics.Expr.var "\x00114",
      YulSemantics.Expr.var "\x00115",
      YulSemantics.Expr.builtin (YulSemantics.EVM.Op.mload) [YulSemantics.Expr.lit (YulSemantics.Literal.number 128)],
      YulSemantics.Expr.builtin (YulSemantics.EVM.Op.mload) [YulSemantics.Expr.lit (YulSemantics.Literal.number 160)]]),
 YulSemantics.Stmt.letDecl
   ["\x00116", "\x00117"]
   (some (YulSemantics.Expr.call
      "\x005"
      [YulSemantics.Expr.builtin (YulSemantics.EVM.Op.mload) [YulSemantics.Expr.lit (YulSemantics.Literal.number 0)],
       YulSemantics.Expr.builtin (YulSemantics.EVM.Op.mload) [YulSemantics.Expr.lit (YulSemantics.Literal.number 32)],
       YulSemantics.Expr.var "\x00114",
       YulSemantics.Expr.var "\x00115"])),
 YulSemantics.Stmt.letDecl
   ["\x00118", "\x00119"]
   (some (YulSemantics.Expr.call
      "\x009"
      [YulSemantics.Expr.var "\x0098",
       YulSemantics.Expr.var "\x0099",
       YulSemantics.Expr.var "\x00116",
       YulSemantics.Expr.var "\x00117"])),
 YulSemantics.Stmt.assign
   ["\x00118", "\x00119"]
   (YulSemantics.Expr.call
     "\x005"
     [YulSemantics.Expr.var "\x00118",
      YulSemantics.Expr.var "\x00119",
      YulSemantics.Expr.builtin (YulSemantics.EVM.Op.mload) [YulSemantics.Expr.lit (YulSemantics.Literal.number 64)],
      YulSemantics.Expr.builtin (YulSemantics.EVM.Op.mload) [YulSemantics.Expr.lit (YulSemantics.Literal.number 96)]]),
 YulSemantics.Stmt.exprStmt
   (YulSemantics.Expr.call
     "\x0012"
     [YulSemantics.Expr.var "\x00114",
      YulSemantics.Expr.var "\x00115",
      YulSemantics.Expr.var "\x00118",
      YulSemantics.Expr.var "\x00119"]),
 YulSemantics.Stmt.exprStmt
   (YulSemantics.Expr.builtin
     (YulSemantics.EVM.Op.ret)
     [YulSemantics.Expr.lit (YulSemantics.Literal.number 0), YulSemantics.Expr.lit (YulSemantics.Literal.number 128)])]

end Challenge.Bls12381G1Add.Reference.Proofs.Compilation
