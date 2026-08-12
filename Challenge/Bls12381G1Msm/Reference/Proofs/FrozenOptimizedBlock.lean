import YulEvmCompiler.Optimizer.Implementation.Pipeline

set_option warningAsError true

namespace Challenge.Bls12381G1Msm.Reference.Proofs.Compilation

open YulSemantics (Block)
open YulSemantics.EVM (Op)

/-- Generated exact optimized AST compiled into the runtime. -/
def frozenReferenceOptimizedBlock : Block Op :=
[YulSemantics.Stmt.funDef
   "\x000"
   ["\x0018", "\x0019"]
   ["\x0020"]
   [YulSemantics.Stmt.assign
      ["\x0020"]
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.or)
        [YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.gt)
           [YulSemantics.Expr.var "\x0018",
            YulSemantics.Expr.lit (YulSemantics.Literal.number 34565483545414906068789196026815425751)],
         YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.and)
           [YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.eq)
              [YulSemantics.Expr.var "\x0018",
               YulSemantics.Expr.lit (YulSemantics.Literal.number 34565483545414906068789196026815425751)],
            YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.iszero)
              [YulSemantics.Expr.builtin
                 (YulSemantics.EVM.Op.lt)
                 [YulSemantics.Expr.var "\x0019",
                  YulSemantics.Expr.lit
                    (YulSemantics.Literal.number
                      45442060874369865957053122457065728162598490762543039060009208264153100167851)]]]])],
 YulSemantics.Stmt.funDef
   "\x001"
   ["\x0023", "\x0024"]
   ["\x0025"]
   [YulSemantics.Stmt.assign
      ["\x0025"]
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.iszero)
        [YulSemantics.Expr.call "\x000" [YulSemantics.Expr.var "\x0023", YulSemantics.Expr.var "\x0024"]])],
 YulSemantics.Stmt.funDef
   "\x002"
   ["\x0026", "\x0027"]
   ["\x0028"]
   [YulSemantics.Stmt.assign
      ["\x0028"]
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.and)
        [YulSemantics.Expr.builtin (YulSemantics.EVM.Op.iszero) [YulSemantics.Expr.var "\x0026"],
         YulSemantics.Expr.builtin (YulSemantics.EVM.Op.iszero) [YulSemantics.Expr.var "\x0027"]])],
 YulSemantics.Stmt.funDef
   "\x003"
   ["\x0029", "\x0030", "\x0031", "\x0032"]
   ["\x0033"]
   [YulSemantics.Stmt.assign
      ["\x0033"]
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.and)
        [YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.eq)
           [YulSemantics.Expr.var "\x0029", YulSemantics.Expr.var "\x0031"],
         YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.eq)
           [YulSemantics.Expr.var "\x0030", YulSemantics.Expr.var "\x0032"]])],
 YulSemantics.Stmt.funDef
   "\x004"
   ["\x0034", "\x0035", "\x0036", "\x0037"]
   ["\x0038", "\x0039"]
   [YulSemantics.Stmt.assign
      ["\x0039"]
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.add)
        [YulSemantics.Expr.var "\x0035", YulSemantics.Expr.var "\x0037"]),
    YulSemantics.Stmt.assign
      ["\x0038"]
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.add)
        [YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.add)
           [YulSemantics.Expr.var "\x0034", YulSemantics.Expr.var "\x0036"],
         YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.lt)
           [YulSemantics.Expr.var "\x0039", YulSemantics.Expr.var "\x0035"]]),
    YulSemantics.Stmt.cond
      (YulSemantics.Expr.call "\x000" [YulSemantics.Expr.var "\x0038", YulSemantics.Expr.var "\x0039"])
      [YulSemantics.Stmt.letDecl
         ["\x0042"]
         (some (YulSemantics.Expr.builtin
            (YulSemantics.EVM.Op.sub)
            [YulSemantics.Expr.var "\x0039",
             YulSemantics.Expr.lit
               (YulSemantics.Literal.number
                 45442060874369865957053122457065728162598490762543039060009208264153100167851)])),
       YulSemantics.Stmt.assign
         ["\x0038"]
         (YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.sub)
           [YulSemantics.Expr.var "\x0038",
            YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.add)
              [YulSemantics.Expr.lit (YulSemantics.Literal.number 34565483545414906068789196026815425751),
               YulSemantics.Expr.builtin
                 (YulSemantics.EVM.Op.gt)
                 [YulSemantics.Expr.lit
                    (YulSemantics.Literal.number
                      45442060874369865957053122457065728162598490762543039060009208264153100167851),
                  YulSemantics.Expr.var "\x0039"]]]),
       YulSemantics.Stmt.assign ["\x0039"] (YulSemantics.Expr.var "\x0042")]],
 YulSemantics.Stmt.funDef
   "\x006"
   ["\x0052", "\x0053", "\x0054", "\x0055"]
   ["\x0056", "\x0057", "\x0058"]
   [YulSemantics.Stmt.assign
      ["\x0058"]
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mul)
        [YulSemantics.Expr.var "\x0053", YulSemantics.Expr.var "\x0055"]),
    YulSemantics.Stmt.letDecl
      ["\x0059"]
      (some (YulSemantics.Expr.builtin
         (YulSemantics.EVM.Op.mulmod)
         [YulSemantics.Expr.var "\x0053",
          YulSemantics.Expr.var "\x0055",
          YulSemantics.Expr.lit
            (YulSemantics.Literal.number
              115792089237316195423570985008687907853269984665640564039457584007913129639935)])),
    YulSemantics.Stmt.letDecl
      ["\x0060"]
      (some (YulSemantics.Expr.builtin
         (YulSemantics.EVM.Op.sub)
         [YulSemantics.Expr.builtin
            (YulSemantics.EVM.Op.sub)
            [YulSemantics.Expr.var "\x0059", YulSemantics.Expr.var "\x0058"],
          YulSemantics.Expr.builtin
            (YulSemantics.EVM.Op.lt)
            [YulSemantics.Expr.var "\x0059", YulSemantics.Expr.var "\x0058"]])),
    YulSemantics.Stmt.letDecl
      ["\x0061"]
      (some (YulSemantics.Expr.builtin
         (YulSemantics.EVM.Op.mul)
         [YulSemantics.Expr.var "\x0052", YulSemantics.Expr.var "\x0055"])),
    YulSemantics.Stmt.letDecl
      ["\x0062"]
      (some (YulSemantics.Expr.builtin
         (YulSemantics.EVM.Op.mulmod)
         [YulSemantics.Expr.var "\x0052",
          YulSemantics.Expr.var "\x0055",
          YulSemantics.Expr.lit
            (YulSemantics.Literal.number
              115792089237316195423570985008687907853269984665640564039457584007913129639935)])),
    YulSemantics.Stmt.letDecl
      ["\x0063"]
      (some (YulSemantics.Expr.builtin
         (YulSemantics.EVM.Op.sub)
         [YulSemantics.Expr.builtin
            (YulSemantics.EVM.Op.sub)
            [YulSemantics.Expr.var "\x0062", YulSemantics.Expr.var "\x0061"],
          YulSemantics.Expr.builtin
            (YulSemantics.EVM.Op.lt)
            [YulSemantics.Expr.var "\x0062", YulSemantics.Expr.var "\x0061"]])),
    YulSemantics.Stmt.letDecl
      ["\x0064"]
      (some (YulSemantics.Expr.builtin
         (YulSemantics.EVM.Op.mul)
         [YulSemantics.Expr.var "\x0053", YulSemantics.Expr.var "\x0054"])),
    YulSemantics.Stmt.letDecl
      ["\x0065"]
      (some (YulSemantics.Expr.builtin
         (YulSemantics.EVM.Op.mulmod)
         [YulSemantics.Expr.var "\x0053",
          YulSemantics.Expr.var "\x0054",
          YulSemantics.Expr.lit
            (YulSemantics.Literal.number
              115792089237316195423570985008687907853269984665640564039457584007913129639935)])),
    YulSemantics.Stmt.letDecl
      ["\x0066"]
      (some (YulSemantics.Expr.builtin
         (YulSemantics.EVM.Op.sub)
         [YulSemantics.Expr.builtin
            (YulSemantics.EVM.Op.sub)
            [YulSemantics.Expr.var "\x0065", YulSemantics.Expr.var "\x0064"],
          YulSemantics.Expr.builtin
            (YulSemantics.EVM.Op.lt)
            [YulSemantics.Expr.var "\x0065", YulSemantics.Expr.var "\x0064"]])),
    YulSemantics.Stmt.assign
      ["\x0057"]
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.add)
        [YulSemantics.Expr.var "\x0060", YulSemantics.Expr.var "\x0061"]),
    YulSemantics.Stmt.letDecl
      ["\x0067"]
      (some (YulSemantics.Expr.builtin
         (YulSemantics.EVM.Op.lt)
         [YulSemantics.Expr.var "\x0057", YulSemantics.Expr.var "\x0060"])),
    YulSemantics.Stmt.letDecl
      ["\x0068"]
      (some (YulSemantics.Expr.builtin
         (YulSemantics.EVM.Op.add)
         [YulSemantics.Expr.var "\x0057", YulSemantics.Expr.var "\x0064"])),
    YulSemantics.Stmt.assign
      ["\x0067"]
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.add)
        [YulSemantics.Expr.var "\x0067",
         YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.lt)
           [YulSemantics.Expr.var "\x0068", YulSemantics.Expr.var "\x0057"]]),
    YulSemantics.Stmt.assign ["\x0057"] (YulSemantics.Expr.var "\x0068"),
    YulSemantics.Stmt.assign
      ["\x0056"]
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.add)
        [YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.add)
           [YulSemantics.Expr.var "\x0063", YulSemantics.Expr.var "\x0066"],
         YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.add)
           [YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.mul)
              [YulSemantics.Expr.var "\x0052", YulSemantics.Expr.var "\x0054"],
            YulSemantics.Expr.var "\x0067"]])],
 YulSemantics.Stmt.funDef
   "\x009"
   ["\x0073", "\x0074", "\x0075", "\x0076"]
   ["\x0077", "\x0078"]
   [YulSemantics.Stmt.letDecl
      ["\x0079", "\x0080", "\x0081"]
      (some (YulSemantics.Expr.call
         "\x006"
         [YulSemantics.Expr.var "\x0073",
          YulSemantics.Expr.var "\x0074",
          YulSemantics.Expr.var "\x0075",
          YulSemantics.Expr.var "\x0076"])),
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
        [YulSemantics.Expr.lit (YulSemantics.Literal.number 1120), YulSemantics.Expr.var "\x0079"]),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mstore)
        [YulSemantics.Expr.lit (YulSemantics.Literal.number 1152), YulSemantics.Expr.var "\x0080"]),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mstore)
        [YulSemantics.Expr.lit (YulSemantics.Literal.number 1184), YulSemantics.Expr.var "\x0081"]),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mstore8)
        [YulSemantics.Expr.lit (YulSemantics.Literal.number 1216),
         YulSemantics.Expr.lit (YulSemantics.Literal.number 1)]),
    YulSemantics.Stmt.letDecl [] none,
    YulSemantics.Stmt.letDecl [] none,
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mstore)
        [YulSemantics.Expr.lit (YulSemantics.Literal.number 1217),
         YulSemantics.Expr.lit
           (YulSemantics.Literal.number
             11762024554600535993938308040068522739871412259351471353901582648940435603456)]),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mstore)
        [YulSemantics.Expr.lit (YulSemantics.Literal.number 1233),
         YulSemantics.Expr.lit
           (YulSemantics.Literal.number
             45442060874369865957053122457065728162598490762543039060009208264153100167851)]),
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
      ["\x0077"]
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.shr)
        [YulSemantics.Expr.lit (YulSemantics.Literal.number 128),
         YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.mload)
           [YulSemantics.Expr.lit (YulSemantics.Literal.number 1280)]]),
    YulSemantics.Stmt.assign
      ["\x0078"]
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mload)
        [YulSemantics.Expr.lit (YulSemantics.Literal.number 1296)])],
 YulSemantics.Stmt.funDef
   "\x0011"
   ["\x0086", "\x0087", "\x0088", "\x0089"]
   ["\x0090"]
   [YulSemantics.Stmt.letDecl
      ["\x0091", "\x0092"]
      (some (YulSemantics.Expr.call
         "\x009"
         [YulSemantics.Expr.var "\x0088",
          YulSemantics.Expr.var "\x0089",
          YulSemantics.Expr.var "\x0088",
          YulSemantics.Expr.var "\x0089"])),
    YulSemantics.Stmt.letDecl
      ["\x0093", "\x0094"]
      (some (YulSemantics.Expr.call
         "\x009"
         [YulSemantics.Expr.var "\x0086",
          YulSemantics.Expr.var "\x0087",
          YulSemantics.Expr.var "\x0086",
          YulSemantics.Expr.var "\x0087"])),
    YulSemantics.Stmt.letDecl
      ["\x0095", "\x0096"]
      (some (YulSemantics.Expr.call
         "\x009"
         [YulSemantics.Expr.var "\x0093",
          YulSemantics.Expr.var "\x0094",
          YulSemantics.Expr.var "\x0086",
          YulSemantics.Expr.var "\x0087"])),
    YulSemantics.Stmt.assign
      ["\x0095", "\x0096"]
      (YulSemantics.Expr.call
        "\x004"
        [YulSemantics.Expr.var "\x0095",
         YulSemantics.Expr.var "\x0096",
         YulSemantics.Expr.lit (YulSemantics.Literal.number 0),
         YulSemantics.Expr.lit (YulSemantics.Literal.number 4)]),
    YulSemantics.Stmt.assign
      ["\x0090"]
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.and)
        [YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.eq)
           [YulSemantics.Expr.var "\x0091", YulSemantics.Expr.var "\x0095"],
         YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.eq)
           [YulSemantics.Expr.var "\x0092", YulSemantics.Expr.var "\x0096"]])],
 YulSemantics.Stmt.funDef
   "\x0015"
   ["\x00105"]
   ["\x00106"]
   [YulSemantics.Stmt.assign
      ["\x00106"]
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.and)
        [YulSemantics.Expr.call
           "\x002"
           [YulSemantics.Expr.builtin (YulSemantics.EVM.Op.mload) [YulSemantics.Expr.var "\x00105"],
            YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.mload)
              [YulSemantics.Expr.builtin
                 (YulSemantics.EVM.Op.add)
                 [YulSemantics.Expr.var "\x00105", YulSemantics.Expr.lit (YulSemantics.Literal.number 32)]]],
         YulSemantics.Expr.call
           "\x002"
           [YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.mload)
              [YulSemantics.Expr.builtin
                 (YulSemantics.EVM.Op.add)
                 [YulSemantics.Expr.var "\x00105", YulSemantics.Expr.lit (YulSemantics.Literal.number 64)]],
            YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.mload)
              [YulSemantics.Expr.builtin
                 (YulSemantics.EVM.Op.add)
                 [YulSemantics.Expr.var "\x00105", YulSemantics.Expr.lit (YulSemantics.Literal.number 96)]]]])],
 YulSemantics.Stmt.funDef
   "\x0016"
   ["\x00107", "\x00108", "\x00109"]
   []
   [YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mstore)
        [YulSemantics.Expr.lit (YulSemantics.Literal.number 1536), YulSemantics.Expr.var "\x00107"]),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mstore)
        [YulSemantics.Expr.lit (YulSemantics.Literal.number 1568), YulSemantics.Expr.var "\x00108"]),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mstore)
        [YulSemantics.Expr.lit (YulSemantics.Literal.number 1600), YulSemantics.Expr.var "\x00109"]),
    YulSemantics.Stmt.cond
      (YulSemantics.Expr.call
        "\x0015"
        [YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.mload)
           [YulSemantics.Expr.lit (YulSemantics.Literal.number 1568)]])
      [YulSemantics.Stmt.letDecl [] none,
       YulSemantics.Stmt.letDecl
         ["fc1_19"]
         (some (YulSemantics.Expr.builtin
            (YulSemantics.EVM.Op.mload)
            [YulSemantics.Expr.lit (YulSemantics.Literal.number 1600)])),
       YulSemantics.Stmt.letDecl
         ["fc1_20"]
         (some (YulSemantics.Expr.builtin
            (YulSemantics.EVM.Op.mload)
            [YulSemantics.Expr.lit (YulSemantics.Literal.number 1536)])),
       YulSemantics.Stmt.letDecl [] none,
       YulSemantics.Stmt.letDecl
         ["fc1_21"]
         (some (YulSemantics.Expr.builtin
            (YulSemantics.EVM.Op.mload)
            [YulSemantics.Expr.builtin
               (YulSemantics.EVM.Op.add)
               [YulSemantics.Expr.var "fc1_19", YulSemantics.Expr.lit (YulSemantics.Literal.number 96)]])),
       YulSemantics.Stmt.letDecl
         ["fc1_22"]
         (some (YulSemantics.Expr.builtin
            (YulSemantics.EVM.Op.mload)
            [YulSemantics.Expr.builtin
               (YulSemantics.EVM.Op.add)
               [YulSemantics.Expr.var "fc1_19", YulSemantics.Expr.lit (YulSemantics.Literal.number 64)]])),
       YulSemantics.Stmt.letDecl
         ["fc1_23"]
         (some (YulSemantics.Expr.builtin
            (YulSemantics.EVM.Op.mload)
            [YulSemantics.Expr.builtin
               (YulSemantics.EVM.Op.add)
               [YulSemantics.Expr.var "fc1_19", YulSemantics.Expr.lit (YulSemantics.Literal.number 32)]])),
       YulSemantics.Stmt.letDecl
         ["fc1_24"]
         (some (YulSemantics.Expr.builtin (YulSemantics.EVM.Op.mload) [YulSemantics.Expr.var "fc1_19"])),
       YulSemantics.Stmt.exprStmt
         (YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.mstore)
           [YulSemantics.Expr.var "fc1_20", YulSemantics.Expr.var "fc1_24"]),
       YulSemantics.Stmt.exprStmt
         (YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.mstore)
           [YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.add)
              [YulSemantics.Expr.var "fc1_20", YulSemantics.Expr.lit (YulSemantics.Literal.number 32)],
            YulSemantics.Expr.var "fc1_23"]),
       YulSemantics.Stmt.exprStmt
         (YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.mstore)
           [YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.add)
              [YulSemantics.Expr.var "fc1_20", YulSemantics.Expr.lit (YulSemantics.Literal.number 64)],
            YulSemantics.Expr.var "fc1_22"]),
       YulSemantics.Stmt.exprStmt
         (YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.mstore)
           [YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.add)
              [YulSemantics.Expr.var "fc1_20", YulSemantics.Expr.lit (YulSemantics.Literal.number 96)],
            YulSemantics.Expr.var "fc1_21"]),
       YulSemantics.Stmt.leave],
    YulSemantics.Stmt.cond
      (YulSemantics.Expr.call
        "\x0015"
        [YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.mload)
           [YulSemantics.Expr.lit (YulSemantics.Literal.number 1600)]])
      [YulSemantics.Stmt.letDecl [] none,
       YulSemantics.Stmt.letDecl
         ["fc1_31"]
         (some (YulSemantics.Expr.builtin
            (YulSemantics.EVM.Op.mload)
            [YulSemantics.Expr.lit (YulSemantics.Literal.number 1568)])),
       YulSemantics.Stmt.letDecl
         ["fc1_32"]
         (some (YulSemantics.Expr.builtin
            (YulSemantics.EVM.Op.mload)
            [YulSemantics.Expr.lit (YulSemantics.Literal.number 1536)])),
       YulSemantics.Stmt.letDecl [] none,
       YulSemantics.Stmt.letDecl
         ["fc1_33"]
         (some (YulSemantics.Expr.builtin
            (YulSemantics.EVM.Op.mload)
            [YulSemantics.Expr.builtin
               (YulSemantics.EVM.Op.add)
               [YulSemantics.Expr.var "fc1_31", YulSemantics.Expr.lit (YulSemantics.Literal.number 96)]])),
       YulSemantics.Stmt.letDecl
         ["fc1_34"]
         (some (YulSemantics.Expr.builtin
            (YulSemantics.EVM.Op.mload)
            [YulSemantics.Expr.builtin
               (YulSemantics.EVM.Op.add)
               [YulSemantics.Expr.var "fc1_31", YulSemantics.Expr.lit (YulSemantics.Literal.number 64)]])),
       YulSemantics.Stmt.letDecl
         ["fc1_35"]
         (some (YulSemantics.Expr.builtin
            (YulSemantics.EVM.Op.mload)
            [YulSemantics.Expr.builtin
               (YulSemantics.EVM.Op.add)
               [YulSemantics.Expr.var "fc1_31", YulSemantics.Expr.lit (YulSemantics.Literal.number 32)]])),
       YulSemantics.Stmt.letDecl
         ["fc1_36"]
         (some (YulSemantics.Expr.builtin (YulSemantics.EVM.Op.mload) [YulSemantics.Expr.var "fc1_31"])),
       YulSemantics.Stmt.exprStmt
         (YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.mstore)
           [YulSemantics.Expr.var "fc1_32", YulSemantics.Expr.var "fc1_36"]),
       YulSemantics.Stmt.exprStmt
         (YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.mstore)
           [YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.add)
              [YulSemantics.Expr.var "fc1_32", YulSemantics.Expr.lit (YulSemantics.Literal.number 32)],
            YulSemantics.Expr.var "fc1_35"]),
       YulSemantics.Stmt.exprStmt
         (YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.mstore)
           [YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.add)
              [YulSemantics.Expr.var "fc1_32", YulSemantics.Expr.lit (YulSemantics.Literal.number 64)],
            YulSemantics.Expr.var "fc1_34"]),
       YulSemantics.Stmt.exprStmt
         (YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.mstore)
           [YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.add)
              [YulSemantics.Expr.var "fc1_32", YulSemantics.Expr.lit (YulSemantics.Literal.number 96)],
            YulSemantics.Expr.var "fc1_33"]),
       YulSemantics.Stmt.leave],
    YulSemantics.Stmt.cond
      (YulSemantics.Expr.call
        "\x003"
        [YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.mload)
           [YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.mload)
              [YulSemantics.Expr.lit (YulSemantics.Literal.number 1568)]],
         YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.mload)
           [YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.add)
              [YulSemantics.Expr.builtin
                 (YulSemantics.EVM.Op.mload)
                 [YulSemantics.Expr.lit (YulSemantics.Literal.number 1568)],
               YulSemantics.Expr.lit (YulSemantics.Literal.number 32)]],
         YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.mload)
           [YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.mload)
              [YulSemantics.Expr.lit (YulSemantics.Literal.number 1600)]],
         YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.mload)
           [YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.add)
              [YulSemantics.Expr.builtin
                 (YulSemantics.EVM.Op.mload)
                 [YulSemantics.Expr.lit (YulSemantics.Literal.number 1600)],
               YulSemantics.Expr.lit (YulSemantics.Literal.number 32)]]])
      [YulSemantics.Stmt.letDecl
         ["\x00110", "\x00111"]
         (some (YulSemantics.Expr.call
            "\x004"
            [YulSemantics.Expr.builtin
               (YulSemantics.EVM.Op.mload)
               [YulSemantics.Expr.builtin
                  (YulSemantics.EVM.Op.add)
                  [YulSemantics.Expr.builtin
                     (YulSemantics.EVM.Op.mload)
                     [YulSemantics.Expr.lit (YulSemantics.Literal.number 1568)],
                   YulSemantics.Expr.lit (YulSemantics.Literal.number 64)]],
             YulSemantics.Expr.builtin
               (YulSemantics.EVM.Op.mload)
               [YulSemantics.Expr.builtin
                  (YulSemantics.EVM.Op.add)
                  [YulSemantics.Expr.builtin
                     (YulSemantics.EVM.Op.mload)
                     [YulSemantics.Expr.lit (YulSemantics.Literal.number 1568)],
                   YulSemantics.Expr.lit (YulSemantics.Literal.number 96)]],
             YulSemantics.Expr.builtin
               (YulSemantics.EVM.Op.mload)
               [YulSemantics.Expr.builtin
                  (YulSemantics.EVM.Op.add)
                  [YulSemantics.Expr.builtin
                     (YulSemantics.EVM.Op.mload)
                     [YulSemantics.Expr.lit (YulSemantics.Literal.number 1600)],
                   YulSemantics.Expr.lit (YulSemantics.Literal.number 64)]],
             YulSemantics.Expr.builtin
               (YulSemantics.EVM.Op.mload)
               [YulSemantics.Expr.builtin
                  (YulSemantics.EVM.Op.add)
                  [YulSemantics.Expr.builtin
                     (YulSemantics.EVM.Op.mload)
                     [YulSemantics.Expr.lit (YulSemantics.Literal.number 1600)],
                   YulSemantics.Expr.lit (YulSemantics.Literal.number 96)]]])),
       YulSemantics.Stmt.cond
         (YulSemantics.Expr.call "\x002" [YulSemantics.Expr.var "\x00110", YulSemantics.Expr.var "\x00111"])
         [YulSemantics.Stmt.letDecl [] none,
          YulSemantics.Stmt.letDecl
            ["fc1_43"]
            (some (YulSemantics.Expr.builtin
               (YulSemantics.EVM.Op.mload)
               [YulSemantics.Expr.lit (YulSemantics.Literal.number 1536)])),
          YulSemantics.Stmt.letDecl [] none,
          YulSemantics.Stmt.exprStmt
            (YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.mstore)
              [YulSemantics.Expr.var "fc1_43", YulSemantics.Expr.lit (YulSemantics.Literal.number 0)]),
          YulSemantics.Stmt.exprStmt
            (YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.mstore)
              [YulSemantics.Expr.builtin
                 (YulSemantics.EVM.Op.add)
                 [YulSemantics.Expr.var "fc1_43", YulSemantics.Expr.lit (YulSemantics.Literal.number 32)],
               YulSemantics.Expr.lit (YulSemantics.Literal.number 0)]),
          YulSemantics.Stmt.exprStmt
            (YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.mstore)
              [YulSemantics.Expr.builtin
                 (YulSemantics.EVM.Op.add)
                 [YulSemantics.Expr.var "fc1_43", YulSemantics.Expr.lit (YulSemantics.Literal.number 64)],
               YulSemantics.Expr.lit (YulSemantics.Literal.number 0)]),
          YulSemantics.Stmt.exprStmt
            (YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.mstore)
              [YulSemantics.Expr.builtin
                 (YulSemantics.EVM.Op.add)
                 [YulSemantics.Expr.var "fc1_43", YulSemantics.Expr.lit (YulSemantics.Literal.number 96)],
               YulSemantics.Expr.lit (YulSemantics.Literal.number 0)]),
          YulSemantics.Stmt.leave],
       YulSemantics.Stmt.letDecl
         ["\x00112", "\x00113"]
         (some (YulSemantics.Expr.call
            "\x009"
            [YulSemantics.Expr.builtin
               (YulSemantics.EVM.Op.mload)
               [YulSemantics.Expr.builtin
                  (YulSemantics.EVM.Op.mload)
                  [YulSemantics.Expr.lit (YulSemantics.Literal.number 1568)]],
             YulSemantics.Expr.builtin
               (YulSemantics.EVM.Op.mload)
               [YulSemantics.Expr.builtin
                  (YulSemantics.EVM.Op.add)
                  [YulSemantics.Expr.builtin
                     (YulSemantics.EVM.Op.mload)
                     [YulSemantics.Expr.lit (YulSemantics.Literal.number 1568)],
                   YulSemantics.Expr.lit (YulSemantics.Literal.number 32)]],
             YulSemantics.Expr.builtin
               (YulSemantics.EVM.Op.mload)
               [YulSemantics.Expr.builtin
                  (YulSemantics.EVM.Op.mload)
                  [YulSemantics.Expr.lit (YulSemantics.Literal.number 1568)]],
             YulSemantics.Expr.builtin
               (YulSemantics.EVM.Op.mload)
               [YulSemantics.Expr.builtin
                  (YulSemantics.EVM.Op.add)
                  [YulSemantics.Expr.builtin
                     (YulSemantics.EVM.Op.mload)
                     [YulSemantics.Expr.lit (YulSemantics.Literal.number 1568)],
                   YulSemantics.Expr.lit (YulSemantics.Literal.number 32)]]])),
       YulSemantics.Stmt.letDecl
         ["\x00114", "\x00115"]
         (some (YulSemantics.Expr.call
            "\x004"
            [YulSemantics.Expr.var "\x00112",
             YulSemantics.Expr.var "\x00113",
             YulSemantics.Expr.var "\x00112",
             YulSemantics.Expr.var "\x00113"])),
       YulSemantics.Stmt.assign
         ["\x00114", "\x00115"]
         (YulSemantics.Expr.call
           "\x004"
           [YulSemantics.Expr.var "\x00114",
            YulSemantics.Expr.var "\x00115",
            YulSemantics.Expr.var "\x00112",
            YulSemantics.Expr.var "\x00113"]),
       YulSemantics.Stmt.letDecl
         ["\x00116", "\x00117"]
         (some (YulSemantics.Expr.call
            "\x004"
            [YulSemantics.Expr.builtin
               (YulSemantics.EVM.Op.mload)
               [YulSemantics.Expr.builtin
                  (YulSemantics.EVM.Op.add)
                  [YulSemantics.Expr.builtin
                     (YulSemantics.EVM.Op.mload)
                     [YulSemantics.Expr.lit (YulSemantics.Literal.number 1568)],
                   YulSemantics.Expr.lit (YulSemantics.Literal.number 64)]],
             YulSemantics.Expr.builtin
               (YulSemantics.EVM.Op.mload)
               [YulSemantics.Expr.builtin
                  (YulSemantics.EVM.Op.add)
                  [YulSemantics.Expr.builtin
                     (YulSemantics.EVM.Op.mload)
                     [YulSemantics.Expr.lit (YulSemantics.Literal.number 1568)],
                   YulSemantics.Expr.lit (YulSemantics.Literal.number 96)]],
             YulSemantics.Expr.builtin
               (YulSemantics.EVM.Op.mload)
               [YulSemantics.Expr.builtin
                  (YulSemantics.EVM.Op.add)
                  [YulSemantics.Expr.builtin
                     (YulSemantics.EVM.Op.mload)
                     [YulSemantics.Expr.lit (YulSemantics.Literal.number 1568)],
                   YulSemantics.Expr.lit (YulSemantics.Literal.number 64)]],
             YulSemantics.Expr.builtin
               (YulSemantics.EVM.Op.mload)
               [YulSemantics.Expr.builtin
                  (YulSemantics.EVM.Op.add)
                  [YulSemantics.Expr.builtin
                     (YulSemantics.EVM.Op.mload)
                     [YulSemantics.Expr.lit (YulSemantics.Literal.number 1568)],
                   YulSemantics.Expr.lit (YulSemantics.Literal.number 96)]]])),
       YulSemantics.Stmt.letDecl ["\x00118", "\x00119"] none,
       YulSemantics.Stmt.letDecl ["fc2_1", "fc2_2"] none,
       YulSemantics.Stmt.letDecl ["fc2_3"] (some (YulSemantics.Expr.var "\x00117")),
       YulSemantics.Stmt.letDecl ["fc2_4"] (some (YulSemantics.Expr.var "\x00116")),
       YulSemantics.Stmt.exprStmt
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
       YulSemantics.Stmt.letDecl [] none,
       YulSemantics.Stmt.exprStmt
         (YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.mstore)
           [YulSemantics.Expr.lit (YulSemantics.Literal.number 1120),
            YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.shl)
              [YulSemantics.Expr.lit (YulSemantics.Literal.number 128), YulSemantics.Expr.var "fc2_4"]]),
       YulSemantics.Stmt.exprStmt
         (YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.mstore)
           [YulSemantics.Expr.lit (YulSemantics.Literal.number 1136), YulSemantics.Expr.var "fc2_3"]),
       YulSemantics.Stmt.letDecl [] none,
       YulSemantics.Stmt.exprStmt
         (YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.mstore)
           [YulSemantics.Expr.lit (YulSemantics.Literal.number 1168),
            YulSemantics.Expr.lit
              (YulSemantics.Literal.number
                11762024554600535993938308040068522739871412259351471353901582648940435603456)]),
       YulSemantics.Stmt.exprStmt
         (YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.mstore)
           [YulSemantics.Expr.lit (YulSemantics.Literal.number 1184),
            YulSemantics.Expr.lit
              (YulSemantics.Literal.number
                45442060874369865957053122457065728162598490762543039060009208264153100167849)]),
       YulSemantics.Stmt.letDecl [] none,
       YulSemantics.Stmt.letDecl [] none,
       YulSemantics.Stmt.exprStmt
         (YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.mstore)
           [YulSemantics.Expr.lit (YulSemantics.Literal.number 1216),
            YulSemantics.Expr.lit
              (YulSemantics.Literal.number
                11762024554600535993938308040068522739871412259351471353901582648940435603456)]),
       YulSemantics.Stmt.exprStmt
         (YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.mstore)
           [YulSemantics.Expr.lit (YulSemantics.Literal.number 1232),
            YulSemantics.Expr.lit
              (YulSemantics.Literal.number
                45442060874369865957053122457065728162598490762543039060009208264153100167851)]),
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
         ["fc2_1"]
         (YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.shr)
           [YulSemantics.Expr.lit (YulSemantics.Literal.number 128),
            YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.mload)
              [YulSemantics.Expr.lit (YulSemantics.Literal.number 1280)]]),
       YulSemantics.Stmt.assign
         ["fc2_2"]
         (YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.mload)
           [YulSemantics.Expr.lit (YulSemantics.Literal.number 1296)]),
       YulSemantics.Stmt.assign ["\x00118"] (YulSemantics.Expr.var "fc2_1"),
       YulSemantics.Stmt.assign ["\x00119"] (YulSemantics.Expr.var "fc2_2"),
       YulSemantics.Stmt.letDecl
         ["\x00120", "\x00121"]
         (some (YulSemantics.Expr.call
            "\x009"
            [YulSemantics.Expr.var "\x00114",
             YulSemantics.Expr.var "\x00115",
             YulSemantics.Expr.var "\x00118",
             YulSemantics.Expr.var "\x00119"])),
       YulSemantics.Stmt.letDecl
         ["\x00122", "\x00123"]
         (some (YulSemantics.Expr.call
            "\x009"
            [YulSemantics.Expr.var "\x00120",
             YulSemantics.Expr.var "\x00121",
             YulSemantics.Expr.var "\x00120",
             YulSemantics.Expr.var "\x00121"])),
       YulSemantics.Stmt.letDecl ["fc0_28", "fc0_29"] none,
       YulSemantics.Stmt.letDecl
         ["fc0_30"]
         (some (YulSemantics.Expr.builtin
            (YulSemantics.EVM.Op.mload)
            [YulSemantics.Expr.builtin
               (YulSemantics.EVM.Op.add)
               [YulSemantics.Expr.builtin
                  (YulSemantics.EVM.Op.mload)
                  [YulSemantics.Expr.lit (YulSemantics.Literal.number 1568)],
                YulSemantics.Expr.lit (YulSemantics.Literal.number 32)]])),
       YulSemantics.Stmt.letDecl
         ["fc0_31"]
         (some (YulSemantics.Expr.builtin
            (YulSemantics.EVM.Op.mload)
            [YulSemantics.Expr.builtin
               (YulSemantics.EVM.Op.mload)
               [YulSemantics.Expr.lit (YulSemantics.Literal.number 1568)]])),
       YulSemantics.Stmt.letDecl ["fc0_32"] (some (YulSemantics.Expr.var "\x00123")),
       YulSemantics.Stmt.letDecl ["fc0_33"] (some (YulSemantics.Expr.var "\x00122")),
       YulSemantics.Stmt.assign
         ["fc0_29"]
         (YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.sub)
           [YulSemantics.Expr.var "fc0_32", YulSemantics.Expr.var "fc0_30"]),
       YulSemantics.Stmt.assign
         ["fc0_28"]
         (YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.sub)
           [YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.sub)
              [YulSemantics.Expr.var "fc0_33", YulSemantics.Expr.var "fc0_31"],
            YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.gt)
              [YulSemantics.Expr.var "fc0_30", YulSemantics.Expr.var "fc0_32"]]),
       YulSemantics.Stmt.cond
         (YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.gt)
           [YulSemantics.Expr.var "fc0_28",
            YulSemantics.Expr.lit (YulSemantics.Literal.number 34565483545414906068789196026815425751)])
         [YulSemantics.Stmt.letDecl
            ["\x0051"]
            (some (YulSemantics.Expr.builtin
               (YulSemantics.EVM.Op.add)
               [YulSemantics.Expr.var "fc0_29",
                YulSemantics.Expr.lit
                  (YulSemantics.Literal.number
                    45442060874369865957053122457065728162598490762543039060009208264153100167851)])),
          YulSemantics.Stmt.assign
            ["fc0_28"]
            (YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.add)
              [YulSemantics.Expr.builtin
                 (YulSemantics.EVM.Op.add)
                 [YulSemantics.Expr.var "fc0_28",
                  YulSemantics.Expr.lit (YulSemantics.Literal.number 34565483545414906068789196026815425751)],
               YulSemantics.Expr.builtin
                 (YulSemantics.EVM.Op.lt)
                 [YulSemantics.Expr.var "\x0051", YulSemantics.Expr.var "fc0_29"]]),
          YulSemantics.Stmt.assign ["fc0_29"] (YulSemantics.Expr.var "\x0051")],
       YulSemantics.Stmt.assign ["\x00122"] (YulSemantics.Expr.var "fc0_28"),
       YulSemantics.Stmt.assign ["\x00123"] (YulSemantics.Expr.var "fc0_29"),
       YulSemantics.Stmt.letDecl ["fc0_35", "fc0_36"] none,
       YulSemantics.Stmt.letDecl
         ["fc0_37"]
         (some (YulSemantics.Expr.builtin
            (YulSemantics.EVM.Op.mload)
            [YulSemantics.Expr.builtin
               (YulSemantics.EVM.Op.add)
               [YulSemantics.Expr.builtin
                  (YulSemantics.EVM.Op.mload)
                  [YulSemantics.Expr.lit (YulSemantics.Literal.number 1600)],
                YulSemantics.Expr.lit (YulSemantics.Literal.number 32)]])),
       YulSemantics.Stmt.letDecl
         ["fc0_38"]
         (some (YulSemantics.Expr.builtin
            (YulSemantics.EVM.Op.mload)
            [YulSemantics.Expr.builtin
               (YulSemantics.EVM.Op.mload)
               [YulSemantics.Expr.lit (YulSemantics.Literal.number 1600)]])),
       YulSemantics.Stmt.letDecl ["fc0_39"] (some (YulSemantics.Expr.var "\x00123")),
       YulSemantics.Stmt.letDecl ["fc0_40"] (some (YulSemantics.Expr.var "\x00122")),
       YulSemantics.Stmt.assign
         ["fc0_36"]
         (YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.sub)
           [YulSemantics.Expr.var "fc0_39", YulSemantics.Expr.var "fc0_37"]),
       YulSemantics.Stmt.assign
         ["fc0_35"]
         (YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.sub)
           [YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.sub)
              [YulSemantics.Expr.var "fc0_40", YulSemantics.Expr.var "fc0_38"],
            YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.gt)
              [YulSemantics.Expr.var "fc0_37", YulSemantics.Expr.var "fc0_39"]]),
       YulSemantics.Stmt.cond
         (YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.gt)
           [YulSemantics.Expr.var "fc0_35",
            YulSemantics.Expr.lit (YulSemantics.Literal.number 34565483545414906068789196026815425751)])
         [YulSemantics.Stmt.letDecl
            ["\x0051"]
            (some (YulSemantics.Expr.builtin
               (YulSemantics.EVM.Op.add)
               [YulSemantics.Expr.var "fc0_36",
                YulSemantics.Expr.lit
                  (YulSemantics.Literal.number
                    45442060874369865957053122457065728162598490762543039060009208264153100167851)])),
          YulSemantics.Stmt.assign
            ["fc0_35"]
            (YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.add)
              [YulSemantics.Expr.builtin
                 (YulSemantics.EVM.Op.add)
                 [YulSemantics.Expr.var "fc0_35",
                  YulSemantics.Expr.lit (YulSemantics.Literal.number 34565483545414906068789196026815425751)],
               YulSemantics.Expr.builtin
                 (YulSemantics.EVM.Op.lt)
                 [YulSemantics.Expr.var "\x0051", YulSemantics.Expr.var "fc0_36"]]),
          YulSemantics.Stmt.assign ["fc0_36"] (YulSemantics.Expr.var "\x0051")],
       YulSemantics.Stmt.assign ["\x00122"] (YulSemantics.Expr.var "fc0_35"),
       YulSemantics.Stmt.assign ["\x00123"] (YulSemantics.Expr.var "fc0_36"),
       YulSemantics.Stmt.letDecl ["\x00124", "\x00125"] none,
       YulSemantics.Stmt.letDecl ["fc0_42", "fc0_43"] none,
       YulSemantics.Stmt.letDecl ["fc0_44"] (some (YulSemantics.Expr.var "\x00123")),
       YulSemantics.Stmt.letDecl ["fc0_45"] (some (YulSemantics.Expr.var "\x00122")),
       YulSemantics.Stmt.letDecl
         ["fc0_46"]
         (some (YulSemantics.Expr.builtin
            (YulSemantics.EVM.Op.mload)
            [YulSemantics.Expr.builtin
               (YulSemantics.EVM.Op.add)
               [YulSemantics.Expr.builtin
                  (YulSemantics.EVM.Op.mload)
                  [YulSemantics.Expr.lit (YulSemantics.Literal.number 1568)],
                YulSemantics.Expr.lit (YulSemantics.Literal.number 32)]])),
       YulSemantics.Stmt.letDecl
         ["fc0_47"]
         (some (YulSemantics.Expr.builtin
            (YulSemantics.EVM.Op.mload)
            [YulSemantics.Expr.builtin
               (YulSemantics.EVM.Op.mload)
               [YulSemantics.Expr.lit (YulSemantics.Literal.number 1568)]])),
       YulSemantics.Stmt.assign
         ["fc0_43"]
         (YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.sub)
           [YulSemantics.Expr.var "fc0_46", YulSemantics.Expr.var "fc0_44"]),
       YulSemantics.Stmt.assign
         ["fc0_42"]
         (YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.sub)
           [YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.sub)
              [YulSemantics.Expr.var "fc0_47", YulSemantics.Expr.var "fc0_45"],
            YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.gt)
              [YulSemantics.Expr.var "fc0_44", YulSemantics.Expr.var "fc0_46"]]),
       YulSemantics.Stmt.cond
         (YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.gt)
           [YulSemantics.Expr.var "fc0_42",
            YulSemantics.Expr.lit (YulSemantics.Literal.number 34565483545414906068789196026815425751)])
         [YulSemantics.Stmt.letDecl
            ["\x0051"]
            (some (YulSemantics.Expr.builtin
               (YulSemantics.EVM.Op.add)
               [YulSemantics.Expr.var "fc0_43",
                YulSemantics.Expr.lit
                  (YulSemantics.Literal.number
                    45442060874369865957053122457065728162598490762543039060009208264153100167851)])),
          YulSemantics.Stmt.assign
            ["fc0_42"]
            (YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.add)
              [YulSemantics.Expr.builtin
                 (YulSemantics.EVM.Op.add)
                 [YulSemantics.Expr.var "fc0_42",
                  YulSemantics.Expr.lit (YulSemantics.Literal.number 34565483545414906068789196026815425751)],
               YulSemantics.Expr.builtin
                 (YulSemantics.EVM.Op.lt)
                 [YulSemantics.Expr.var "\x0051", YulSemantics.Expr.var "fc0_43"]]),
          YulSemantics.Stmt.assign ["fc0_43"] (YulSemantics.Expr.var "\x0051")],
       YulSemantics.Stmt.assign ["\x00124"] (YulSemantics.Expr.var "fc0_42"),
       YulSemantics.Stmt.assign ["\x00125"] (YulSemantics.Expr.var "fc0_43"),
       YulSemantics.Stmt.letDecl
         ["\x00126", "\x00127"]
         (some (YulSemantics.Expr.call
            "\x009"
            [YulSemantics.Expr.var "\x00120",
             YulSemantics.Expr.var "\x00121",
             YulSemantics.Expr.var "\x00124",
             YulSemantics.Expr.var "\x00125"])),
       YulSemantics.Stmt.letDecl ["fc0_49", "fc0_50"] none,
       YulSemantics.Stmt.letDecl
         ["fc0_51"]
         (some (YulSemantics.Expr.builtin
            (YulSemantics.EVM.Op.mload)
            [YulSemantics.Expr.builtin
               (YulSemantics.EVM.Op.add)
               [YulSemantics.Expr.builtin
                  (YulSemantics.EVM.Op.mload)
                  [YulSemantics.Expr.lit (YulSemantics.Literal.number 1568)],
                YulSemantics.Expr.lit (YulSemantics.Literal.number 96)]])),
       YulSemantics.Stmt.letDecl
         ["fc0_52"]
         (some (YulSemantics.Expr.builtin
            (YulSemantics.EVM.Op.mload)
            [YulSemantics.Expr.builtin
               (YulSemantics.EVM.Op.add)
               [YulSemantics.Expr.builtin
                  (YulSemantics.EVM.Op.mload)
                  [YulSemantics.Expr.lit (YulSemantics.Literal.number 1568)],
                YulSemantics.Expr.lit (YulSemantics.Literal.number 64)]])),
       YulSemantics.Stmt.letDecl ["fc0_53"] (some (YulSemantics.Expr.var "\x00127")),
       YulSemantics.Stmt.letDecl ["fc0_54"] (some (YulSemantics.Expr.var "\x00126")),
       YulSemantics.Stmt.assign
         ["fc0_50"]
         (YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.sub)
           [YulSemantics.Expr.var "fc0_53", YulSemantics.Expr.var "fc0_51"]),
       YulSemantics.Stmt.assign
         ["fc0_49"]
         (YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.sub)
           [YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.sub)
              [YulSemantics.Expr.var "fc0_54", YulSemantics.Expr.var "fc0_52"],
            YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.gt)
              [YulSemantics.Expr.var "fc0_51", YulSemantics.Expr.var "fc0_53"]]),
       YulSemantics.Stmt.cond
         (YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.gt)
           [YulSemantics.Expr.var "fc0_49",
            YulSemantics.Expr.lit (YulSemantics.Literal.number 34565483545414906068789196026815425751)])
         [YulSemantics.Stmt.letDecl
            ["\x0051"]
            (some (YulSemantics.Expr.builtin
               (YulSemantics.EVM.Op.add)
               [YulSemantics.Expr.var "fc0_50",
                YulSemantics.Expr.lit
                  (YulSemantics.Literal.number
                    45442060874369865957053122457065728162598490762543039060009208264153100167851)])),
          YulSemantics.Stmt.assign
            ["fc0_49"]
            (YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.add)
              [YulSemantics.Expr.builtin
                 (YulSemantics.EVM.Op.add)
                 [YulSemantics.Expr.var "fc0_49",
                  YulSemantics.Expr.lit (YulSemantics.Literal.number 34565483545414906068789196026815425751)],
               YulSemantics.Expr.builtin
                 (YulSemantics.EVM.Op.lt)
                 [YulSemantics.Expr.var "\x0051", YulSemantics.Expr.var "fc0_50"]]),
          YulSemantics.Stmt.assign ["fc0_50"] (YulSemantics.Expr.var "\x0051")],
       YulSemantics.Stmt.assign ["\x00126"] (YulSemantics.Expr.var "fc0_49"),
       YulSemantics.Stmt.assign ["\x00127"] (YulSemantics.Expr.var "fc0_50"),
       YulSemantics.Stmt.letDecl [] none,
       YulSemantics.Stmt.letDecl ["fc0_56"] (some (YulSemantics.Expr.var "\x00127")),
       YulSemantics.Stmt.letDecl ["fc0_57"] (some (YulSemantics.Expr.var "\x00126")),
       YulSemantics.Stmt.letDecl ["fc0_58"] (some (YulSemantics.Expr.var "\x00123")),
       YulSemantics.Stmt.letDecl ["fc0_59"] (some (YulSemantics.Expr.var "\x00122")),
       YulSemantics.Stmt.letDecl
         ["fc0_60"]
         (some (YulSemantics.Expr.builtin
            (YulSemantics.EVM.Op.mload)
            [YulSemantics.Expr.lit (YulSemantics.Literal.number 1536)])),
       YulSemantics.Stmt.exprStmt
         (YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.mstore)
           [YulSemantics.Expr.var "fc0_60", YulSemantics.Expr.var "fc0_59"]),
       YulSemantics.Stmt.exprStmt
         (YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.mstore)
           [YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.add)
              [YulSemantics.Expr.var "fc0_60", YulSemantics.Expr.lit (YulSemantics.Literal.number 32)],
            YulSemantics.Expr.var "fc0_58"]),
       YulSemantics.Stmt.exprStmt
         (YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.mstore)
           [YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.add)
              [YulSemantics.Expr.var "fc0_60", YulSemantics.Expr.lit (YulSemantics.Literal.number 64)],
            YulSemantics.Expr.var "fc0_57"]),
       YulSemantics.Stmt.exprStmt
         (YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.mstore)
           [YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.add)
              [YulSemantics.Expr.var "fc0_60", YulSemantics.Expr.lit (YulSemantics.Literal.number 96)],
            YulSemantics.Expr.var "fc0_56"]),
       YulSemantics.Stmt.leave],
    YulSemantics.Stmt.letDecl ["\x00128", "\x00129"] none,
    YulSemantics.Stmt.letDecl ["fc0_67", "fc0_68"] none,
    YulSemantics.Stmt.letDecl
      ["fc0_69"]
      (some (YulSemantics.Expr.builtin
         (YulSemantics.EVM.Op.mload)
         [YulSemantics.Expr.builtin
            (YulSemantics.EVM.Op.add)
            [YulSemantics.Expr.builtin
               (YulSemantics.EVM.Op.mload)
               [YulSemantics.Expr.lit (YulSemantics.Literal.number 1568)],
             YulSemantics.Expr.lit (YulSemantics.Literal.number 96)]])),
    YulSemantics.Stmt.letDecl
      ["fc0_70"]
      (some (YulSemantics.Expr.builtin
         (YulSemantics.EVM.Op.mload)
         [YulSemantics.Expr.builtin
            (YulSemantics.EVM.Op.add)
            [YulSemantics.Expr.builtin
               (YulSemantics.EVM.Op.mload)
               [YulSemantics.Expr.lit (YulSemantics.Literal.number 1568)],
             YulSemantics.Expr.lit (YulSemantics.Literal.number 64)]])),
    YulSemantics.Stmt.letDecl
      ["fc0_71"]
      (some (YulSemantics.Expr.builtin
         (YulSemantics.EVM.Op.mload)
         [YulSemantics.Expr.builtin
            (YulSemantics.EVM.Op.add)
            [YulSemantics.Expr.builtin
               (YulSemantics.EVM.Op.mload)
               [YulSemantics.Expr.lit (YulSemantics.Literal.number 1600)],
             YulSemantics.Expr.lit (YulSemantics.Literal.number 96)]])),
    YulSemantics.Stmt.letDecl
      ["fc0_72"]
      (some (YulSemantics.Expr.builtin
         (YulSemantics.EVM.Op.mload)
         [YulSemantics.Expr.builtin
            (YulSemantics.EVM.Op.add)
            [YulSemantics.Expr.builtin
               (YulSemantics.EVM.Op.mload)
               [YulSemantics.Expr.lit (YulSemantics.Literal.number 1600)],
             YulSemantics.Expr.lit (YulSemantics.Literal.number 64)]])),
    YulSemantics.Stmt.assign
      ["fc0_68"]
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.sub)
        [YulSemantics.Expr.var "fc0_71", YulSemantics.Expr.var "fc0_69"]),
    YulSemantics.Stmt.assign
      ["fc0_67"]
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.sub)
        [YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.sub)
           [YulSemantics.Expr.var "fc0_72", YulSemantics.Expr.var "fc0_70"],
         YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.gt)
           [YulSemantics.Expr.var "fc0_69", YulSemantics.Expr.var "fc0_71"]]),
    YulSemantics.Stmt.cond
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.gt)
        [YulSemantics.Expr.var "fc0_67",
         YulSemantics.Expr.lit (YulSemantics.Literal.number 34565483545414906068789196026815425751)])
      [YulSemantics.Stmt.letDecl
         ["\x0051"]
         (some (YulSemantics.Expr.builtin
            (YulSemantics.EVM.Op.add)
            [YulSemantics.Expr.var "fc0_68",
             YulSemantics.Expr.lit
               (YulSemantics.Literal.number
                 45442060874369865957053122457065728162598490762543039060009208264153100167851)])),
       YulSemantics.Stmt.assign
         ["fc0_67"]
         (YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.add)
           [YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.add)
              [YulSemantics.Expr.var "fc0_67",
               YulSemantics.Expr.lit (YulSemantics.Literal.number 34565483545414906068789196026815425751)],
            YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.lt)
              [YulSemantics.Expr.var "\x0051", YulSemantics.Expr.var "fc0_68"]]),
       YulSemantics.Stmt.assign ["fc0_68"] (YulSemantics.Expr.var "\x0051")],
    YulSemantics.Stmt.assign ["\x00128"] (YulSemantics.Expr.var "fc0_67"),
    YulSemantics.Stmt.assign ["\x00129"] (YulSemantics.Expr.var "fc0_68"),
    YulSemantics.Stmt.letDecl ["\x00130", "\x00131"] none,
    YulSemantics.Stmt.letDecl ["fc0_74", "fc0_75"] none,
    YulSemantics.Stmt.letDecl
      ["fc0_76"]
      (some (YulSemantics.Expr.builtin
         (YulSemantics.EVM.Op.mload)
         [YulSemantics.Expr.builtin
            (YulSemantics.EVM.Op.add)
            [YulSemantics.Expr.builtin
               (YulSemantics.EVM.Op.mload)
               [YulSemantics.Expr.lit (YulSemantics.Literal.number 1568)],
             YulSemantics.Expr.lit (YulSemantics.Literal.number 32)]])),
    YulSemantics.Stmt.letDecl
      ["fc0_77"]
      (some (YulSemantics.Expr.builtin
         (YulSemantics.EVM.Op.mload)
         [YulSemantics.Expr.builtin
            (YulSemantics.EVM.Op.mload)
            [YulSemantics.Expr.lit (YulSemantics.Literal.number 1568)]])),
    YulSemantics.Stmt.letDecl
      ["fc0_78"]
      (some (YulSemantics.Expr.builtin
         (YulSemantics.EVM.Op.mload)
         [YulSemantics.Expr.builtin
            (YulSemantics.EVM.Op.add)
            [YulSemantics.Expr.builtin
               (YulSemantics.EVM.Op.mload)
               [YulSemantics.Expr.lit (YulSemantics.Literal.number 1600)],
             YulSemantics.Expr.lit (YulSemantics.Literal.number 32)]])),
    YulSemantics.Stmt.letDecl
      ["fc0_79"]
      (some (YulSemantics.Expr.builtin
         (YulSemantics.EVM.Op.mload)
         [YulSemantics.Expr.builtin
            (YulSemantics.EVM.Op.mload)
            [YulSemantics.Expr.lit (YulSemantics.Literal.number 1600)]])),
    YulSemantics.Stmt.assign
      ["fc0_75"]
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.sub)
        [YulSemantics.Expr.var "fc0_78", YulSemantics.Expr.var "fc0_76"]),
    YulSemantics.Stmt.assign
      ["fc0_74"]
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.sub)
        [YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.sub)
           [YulSemantics.Expr.var "fc0_79", YulSemantics.Expr.var "fc0_77"],
         YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.gt)
           [YulSemantics.Expr.var "fc0_76", YulSemantics.Expr.var "fc0_78"]]),
    YulSemantics.Stmt.cond
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.gt)
        [YulSemantics.Expr.var "fc0_74",
         YulSemantics.Expr.lit (YulSemantics.Literal.number 34565483545414906068789196026815425751)])
      [YulSemantics.Stmt.letDecl
         ["\x0051"]
         (some (YulSemantics.Expr.builtin
            (YulSemantics.EVM.Op.add)
            [YulSemantics.Expr.var "fc0_75",
             YulSemantics.Expr.lit
               (YulSemantics.Literal.number
                 45442060874369865957053122457065728162598490762543039060009208264153100167851)])),
       YulSemantics.Stmt.assign
         ["fc0_74"]
         (YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.add)
           [YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.add)
              [YulSemantics.Expr.var "fc0_74",
               YulSemantics.Expr.lit (YulSemantics.Literal.number 34565483545414906068789196026815425751)],
            YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.lt)
              [YulSemantics.Expr.var "\x0051", YulSemantics.Expr.var "fc0_75"]]),
       YulSemantics.Stmt.assign ["fc0_75"] (YulSemantics.Expr.var "\x0051")],
    YulSemantics.Stmt.assign ["\x00130"] (YulSemantics.Expr.var "fc0_74"),
    YulSemantics.Stmt.assign ["\x00131"] (YulSemantics.Expr.var "fc0_75"),
    YulSemantics.Stmt.letDecl ["\x00132", "\x00133"] none,
    YulSemantics.Stmt.letDecl ["fc2_7", "fc2_8"] none,
    YulSemantics.Stmt.letDecl ["fc2_9"] (some (YulSemantics.Expr.var "\x00131")),
    YulSemantics.Stmt.letDecl ["fc2_10"] (some (YulSemantics.Expr.var "\x00130")),
    YulSemantics.Stmt.exprStmt
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
    YulSemantics.Stmt.letDecl [] none,
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mstore)
        [YulSemantics.Expr.lit (YulSemantics.Literal.number 1120),
         YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.shl)
           [YulSemantics.Expr.lit (YulSemantics.Literal.number 128), YulSemantics.Expr.var "fc2_10"]]),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mstore)
        [YulSemantics.Expr.lit (YulSemantics.Literal.number 1136), YulSemantics.Expr.var "fc2_9"]),
    YulSemantics.Stmt.letDecl [] none,
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mstore)
        [YulSemantics.Expr.lit (YulSemantics.Literal.number 1168),
         YulSemantics.Expr.lit
           (YulSemantics.Literal.number
             11762024554600535993938308040068522739871412259351471353901582648940435603456)]),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mstore)
        [YulSemantics.Expr.lit (YulSemantics.Literal.number 1184),
         YulSemantics.Expr.lit
           (YulSemantics.Literal.number
             45442060874369865957053122457065728162598490762543039060009208264153100167849)]),
    YulSemantics.Stmt.letDecl [] none,
    YulSemantics.Stmt.letDecl [] none,
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mstore)
        [YulSemantics.Expr.lit (YulSemantics.Literal.number 1216),
         YulSemantics.Expr.lit
           (YulSemantics.Literal.number
             11762024554600535993938308040068522739871412259351471353901582648940435603456)]),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mstore)
        [YulSemantics.Expr.lit (YulSemantics.Literal.number 1232),
         YulSemantics.Expr.lit
           (YulSemantics.Literal.number
             45442060874369865957053122457065728162598490762543039060009208264153100167851)]),
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
      ["fc2_7"]
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.shr)
        [YulSemantics.Expr.lit (YulSemantics.Literal.number 128),
         YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.mload)
           [YulSemantics.Expr.lit (YulSemantics.Literal.number 1280)]]),
    YulSemantics.Stmt.assign
      ["fc2_8"]
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mload)
        [YulSemantics.Expr.lit (YulSemantics.Literal.number 1296)]),
    YulSemantics.Stmt.assign ["\x00132"] (YulSemantics.Expr.var "fc2_7"),
    YulSemantics.Stmt.assign ["\x00133"] (YulSemantics.Expr.var "fc2_8"),
    YulSemantics.Stmt.letDecl
      ["\x00134", "\x00135"]
      (some (YulSemantics.Expr.call
         "\x009"
         [YulSemantics.Expr.var "\x00128",
          YulSemantics.Expr.var "\x00129",
          YulSemantics.Expr.var "\x00132",
          YulSemantics.Expr.var "\x00133"])),
    YulSemantics.Stmt.letDecl
      ["\x00136", "\x00137"]
      (some (YulSemantics.Expr.call
         "\x009"
         [YulSemantics.Expr.var "\x00134",
          YulSemantics.Expr.var "\x00135",
          YulSemantics.Expr.var "\x00134",
          YulSemantics.Expr.var "\x00135"])),
    YulSemantics.Stmt.letDecl ["fc0_81", "fc0_82"] none,
    YulSemantics.Stmt.letDecl
      ["fc0_83"]
      (some (YulSemantics.Expr.builtin
         (YulSemantics.EVM.Op.mload)
         [YulSemantics.Expr.builtin
            (YulSemantics.EVM.Op.add)
            [YulSemantics.Expr.builtin
               (YulSemantics.EVM.Op.mload)
               [YulSemantics.Expr.lit (YulSemantics.Literal.number 1568)],
             YulSemantics.Expr.lit (YulSemantics.Literal.number 32)]])),
    YulSemantics.Stmt.letDecl
      ["fc0_84"]
      (some (YulSemantics.Expr.builtin
         (YulSemantics.EVM.Op.mload)
         [YulSemantics.Expr.builtin
            (YulSemantics.EVM.Op.mload)
            [YulSemantics.Expr.lit (YulSemantics.Literal.number 1568)]])),
    YulSemantics.Stmt.letDecl ["fc0_85"] (some (YulSemantics.Expr.var "\x00137")),
    YulSemantics.Stmt.letDecl ["fc0_86"] (some (YulSemantics.Expr.var "\x00136")),
    YulSemantics.Stmt.assign
      ["fc0_82"]
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.sub)
        [YulSemantics.Expr.var "fc0_85", YulSemantics.Expr.var "fc0_83"]),
    YulSemantics.Stmt.assign
      ["fc0_81"]
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.sub)
        [YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.sub)
           [YulSemantics.Expr.var "fc0_86", YulSemantics.Expr.var "fc0_84"],
         YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.gt)
           [YulSemantics.Expr.var "fc0_83", YulSemantics.Expr.var "fc0_85"]]),
    YulSemantics.Stmt.cond
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.gt)
        [YulSemantics.Expr.var "fc0_81",
         YulSemantics.Expr.lit (YulSemantics.Literal.number 34565483545414906068789196026815425751)])
      [YulSemantics.Stmt.letDecl
         ["\x0051"]
         (some (YulSemantics.Expr.builtin
            (YulSemantics.EVM.Op.add)
            [YulSemantics.Expr.var "fc0_82",
             YulSemantics.Expr.lit
               (YulSemantics.Literal.number
                 45442060874369865957053122457065728162598490762543039060009208264153100167851)])),
       YulSemantics.Stmt.assign
         ["fc0_81"]
         (YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.add)
           [YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.add)
              [YulSemantics.Expr.var "fc0_81",
               YulSemantics.Expr.lit (YulSemantics.Literal.number 34565483545414906068789196026815425751)],
            YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.lt)
              [YulSemantics.Expr.var "\x0051", YulSemantics.Expr.var "fc0_82"]]),
       YulSemantics.Stmt.assign ["fc0_82"] (YulSemantics.Expr.var "\x0051")],
    YulSemantics.Stmt.assign ["\x00136"] (YulSemantics.Expr.var "fc0_81"),
    YulSemantics.Stmt.assign ["\x00137"] (YulSemantics.Expr.var "fc0_82"),
    YulSemantics.Stmt.letDecl ["fc0_88", "fc0_89"] none,
    YulSemantics.Stmt.letDecl
      ["fc0_90"]
      (some (YulSemantics.Expr.builtin
         (YulSemantics.EVM.Op.mload)
         [YulSemantics.Expr.builtin
            (YulSemantics.EVM.Op.add)
            [YulSemantics.Expr.builtin
               (YulSemantics.EVM.Op.mload)
               [YulSemantics.Expr.lit (YulSemantics.Literal.number 1600)],
             YulSemantics.Expr.lit (YulSemantics.Literal.number 32)]])),
    YulSemantics.Stmt.letDecl
      ["fc0_91"]
      (some (YulSemantics.Expr.builtin
         (YulSemantics.EVM.Op.mload)
         [YulSemantics.Expr.builtin
            (YulSemantics.EVM.Op.mload)
            [YulSemantics.Expr.lit (YulSemantics.Literal.number 1600)]])),
    YulSemantics.Stmt.letDecl ["fc0_92"] (some (YulSemantics.Expr.var "\x00137")),
    YulSemantics.Stmt.letDecl ["fc0_93"] (some (YulSemantics.Expr.var "\x00136")),
    YulSemantics.Stmt.assign
      ["fc0_89"]
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.sub)
        [YulSemantics.Expr.var "fc0_92", YulSemantics.Expr.var "fc0_90"]),
    YulSemantics.Stmt.assign
      ["fc0_88"]
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.sub)
        [YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.sub)
           [YulSemantics.Expr.var "fc0_93", YulSemantics.Expr.var "fc0_91"],
         YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.gt)
           [YulSemantics.Expr.var "fc0_90", YulSemantics.Expr.var "fc0_92"]]),
    YulSemantics.Stmt.cond
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.gt)
        [YulSemantics.Expr.var "fc0_88",
         YulSemantics.Expr.lit (YulSemantics.Literal.number 34565483545414906068789196026815425751)])
      [YulSemantics.Stmt.letDecl
         ["\x0051"]
         (some (YulSemantics.Expr.builtin
            (YulSemantics.EVM.Op.add)
            [YulSemantics.Expr.var "fc0_89",
             YulSemantics.Expr.lit
               (YulSemantics.Literal.number
                 45442060874369865957053122457065728162598490762543039060009208264153100167851)])),
       YulSemantics.Stmt.assign
         ["fc0_88"]
         (YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.add)
           [YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.add)
              [YulSemantics.Expr.var "fc0_88",
               YulSemantics.Expr.lit (YulSemantics.Literal.number 34565483545414906068789196026815425751)],
            YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.lt)
              [YulSemantics.Expr.var "\x0051", YulSemantics.Expr.var "fc0_89"]]),
       YulSemantics.Stmt.assign ["fc0_89"] (YulSemantics.Expr.var "\x0051")],
    YulSemantics.Stmt.assign ["\x00136"] (YulSemantics.Expr.var "fc0_88"),
    YulSemantics.Stmt.assign ["\x00137"] (YulSemantics.Expr.var "fc0_89"),
    YulSemantics.Stmt.letDecl ["\x00138", "\x00139"] none,
    YulSemantics.Stmt.letDecl ["fc0_95", "fc0_96"] none,
    YulSemantics.Stmt.letDecl ["fc0_97"] (some (YulSemantics.Expr.var "\x00137")),
    YulSemantics.Stmt.letDecl ["fc0_98"] (some (YulSemantics.Expr.var "\x00136")),
    YulSemantics.Stmt.letDecl
      ["fc0_99"]
      (some (YulSemantics.Expr.builtin
         (YulSemantics.EVM.Op.mload)
         [YulSemantics.Expr.builtin
            (YulSemantics.EVM.Op.add)
            [YulSemantics.Expr.builtin
               (YulSemantics.EVM.Op.mload)
               [YulSemantics.Expr.lit (YulSemantics.Literal.number 1568)],
             YulSemantics.Expr.lit (YulSemantics.Literal.number 32)]])),
    YulSemantics.Stmt.letDecl
      ["fc0_100"]
      (some (YulSemantics.Expr.builtin
         (YulSemantics.EVM.Op.mload)
         [YulSemantics.Expr.builtin
            (YulSemantics.EVM.Op.mload)
            [YulSemantics.Expr.lit (YulSemantics.Literal.number 1568)]])),
    YulSemantics.Stmt.assign
      ["fc0_96"]
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.sub)
        [YulSemantics.Expr.var "fc0_99", YulSemantics.Expr.var "fc0_97"]),
    YulSemantics.Stmt.assign
      ["fc0_95"]
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.sub)
        [YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.sub)
           [YulSemantics.Expr.var "fc0_100", YulSemantics.Expr.var "fc0_98"],
         YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.gt)
           [YulSemantics.Expr.var "fc0_97", YulSemantics.Expr.var "fc0_99"]]),
    YulSemantics.Stmt.cond
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.gt)
        [YulSemantics.Expr.var "fc0_95",
         YulSemantics.Expr.lit (YulSemantics.Literal.number 34565483545414906068789196026815425751)])
      [YulSemantics.Stmt.letDecl
         ["\x0051"]
         (some (YulSemantics.Expr.builtin
            (YulSemantics.EVM.Op.add)
            [YulSemantics.Expr.var "fc0_96",
             YulSemantics.Expr.lit
               (YulSemantics.Literal.number
                 45442060874369865957053122457065728162598490762543039060009208264153100167851)])),
       YulSemantics.Stmt.assign
         ["fc0_95"]
         (YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.add)
           [YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.add)
              [YulSemantics.Expr.var "fc0_95",
               YulSemantics.Expr.lit (YulSemantics.Literal.number 34565483545414906068789196026815425751)],
            YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.lt)
              [YulSemantics.Expr.var "\x0051", YulSemantics.Expr.var "fc0_96"]]),
       YulSemantics.Stmt.assign ["fc0_96"] (YulSemantics.Expr.var "\x0051")],
    YulSemantics.Stmt.assign ["\x00138"] (YulSemantics.Expr.var "fc0_95"),
    YulSemantics.Stmt.assign ["\x00139"] (YulSemantics.Expr.var "fc0_96"),
    YulSemantics.Stmt.letDecl
      ["\x00140", "\x00141"]
      (some (YulSemantics.Expr.call
         "\x009"
         [YulSemantics.Expr.var "\x00134",
          YulSemantics.Expr.var "\x00135",
          YulSemantics.Expr.var "\x00138",
          YulSemantics.Expr.var "\x00139"])),
    YulSemantics.Stmt.letDecl ["fc0_102", "fc0_103"] none,
    YulSemantics.Stmt.letDecl
      ["fc0_104"]
      (some (YulSemantics.Expr.builtin
         (YulSemantics.EVM.Op.mload)
         [YulSemantics.Expr.builtin
            (YulSemantics.EVM.Op.add)
            [YulSemantics.Expr.builtin
               (YulSemantics.EVM.Op.mload)
               [YulSemantics.Expr.lit (YulSemantics.Literal.number 1568)],
             YulSemantics.Expr.lit (YulSemantics.Literal.number 96)]])),
    YulSemantics.Stmt.letDecl
      ["fc0_105"]
      (some (YulSemantics.Expr.builtin
         (YulSemantics.EVM.Op.mload)
         [YulSemantics.Expr.builtin
            (YulSemantics.EVM.Op.add)
            [YulSemantics.Expr.builtin
               (YulSemantics.EVM.Op.mload)
               [YulSemantics.Expr.lit (YulSemantics.Literal.number 1568)],
             YulSemantics.Expr.lit (YulSemantics.Literal.number 64)]])),
    YulSemantics.Stmt.letDecl ["fc0_106"] (some (YulSemantics.Expr.var "\x00141")),
    YulSemantics.Stmt.letDecl ["fc0_107"] (some (YulSemantics.Expr.var "\x00140")),
    YulSemantics.Stmt.assign
      ["fc0_103"]
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.sub)
        [YulSemantics.Expr.var "fc0_106", YulSemantics.Expr.var "fc0_104"]),
    YulSemantics.Stmt.assign
      ["fc0_102"]
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.sub)
        [YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.sub)
           [YulSemantics.Expr.var "fc0_107", YulSemantics.Expr.var "fc0_105"],
         YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.gt)
           [YulSemantics.Expr.var "fc0_104", YulSemantics.Expr.var "fc0_106"]]),
    YulSemantics.Stmt.cond
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.gt)
        [YulSemantics.Expr.var "fc0_102",
         YulSemantics.Expr.lit (YulSemantics.Literal.number 34565483545414906068789196026815425751)])
      [YulSemantics.Stmt.letDecl
         ["\x0051"]
         (some (YulSemantics.Expr.builtin
            (YulSemantics.EVM.Op.add)
            [YulSemantics.Expr.var "fc0_103",
             YulSemantics.Expr.lit
               (YulSemantics.Literal.number
                 45442060874369865957053122457065728162598490762543039060009208264153100167851)])),
       YulSemantics.Stmt.assign
         ["fc0_102"]
         (YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.add)
           [YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.add)
              [YulSemantics.Expr.var "fc0_102",
               YulSemantics.Expr.lit (YulSemantics.Literal.number 34565483545414906068789196026815425751)],
            YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.lt)
              [YulSemantics.Expr.var "\x0051", YulSemantics.Expr.var "fc0_103"]]),
       YulSemantics.Stmt.assign ["fc0_103"] (YulSemantics.Expr.var "\x0051")],
    YulSemantics.Stmt.assign ["\x00140"] (YulSemantics.Expr.var "fc0_102"),
    YulSemantics.Stmt.assign ["\x00141"] (YulSemantics.Expr.var "fc0_103"),
    YulSemantics.Stmt.letDecl [] none,
    YulSemantics.Stmt.letDecl ["fc0_109"] (some (YulSemantics.Expr.var "\x00141")),
    YulSemantics.Stmt.letDecl ["fc0_110"] (some (YulSemantics.Expr.var "\x00140")),
    YulSemantics.Stmt.letDecl ["fc0_111"] (some (YulSemantics.Expr.var "\x00137")),
    YulSemantics.Stmt.letDecl ["fc0_112"] (some (YulSemantics.Expr.var "\x00136")),
    YulSemantics.Stmt.letDecl
      ["fc0_113"]
      (some (YulSemantics.Expr.builtin
         (YulSemantics.EVM.Op.mload)
         [YulSemantics.Expr.lit (YulSemantics.Literal.number 1536)])),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mstore)
        [YulSemantics.Expr.var "fc0_113", YulSemantics.Expr.var "fc0_112"]),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mstore)
        [YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.add)
           [YulSemantics.Expr.var "fc0_113", YulSemantics.Expr.lit (YulSemantics.Literal.number 32)],
         YulSemantics.Expr.var "fc0_111"]),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mstore)
        [YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.add)
           [YulSemantics.Expr.var "fc0_113", YulSemantics.Expr.lit (YulSemantics.Literal.number 64)],
         YulSemantics.Expr.var "fc0_110"]),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mstore)
        [YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.add)
           [YulSemantics.Expr.var "fc0_113", YulSemantics.Expr.lit (YulSemantics.Literal.number 96)],
         YulSemantics.Expr.var "fc0_109"])],
 YulSemantics.Stmt.funDef
   "\x0017"
   ["\x00142", "\x00143", "\x00144"]
   []
   [YulSemantics.Stmt.letDecl [] none,
    YulSemantics.Stmt.letDecl [] none,
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mstore)
        [YulSemantics.Expr.var "\x00144", YulSemantics.Expr.lit (YulSemantics.Literal.number 0)]),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mstore)
        [YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.add)
           [YulSemantics.Expr.var "\x00144", YulSemantics.Expr.lit (YulSemantics.Literal.number 32)],
         YulSemantics.Expr.lit (YulSemantics.Literal.number 0)]),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mstore)
        [YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.add)
           [YulSemantics.Expr.var "\x00144", YulSemantics.Expr.lit (YulSemantics.Literal.number 64)],
         YulSemantics.Expr.lit (YulSemantics.Literal.number 0)]),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mstore)
        [YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.add)
           [YulSemantics.Expr.var "\x00144", YulSemantics.Expr.lit (YulSemantics.Literal.number 96)],
         YulSemantics.Expr.lit (YulSemantics.Literal.number 0)]),
    YulSemantics.Stmt.letDecl
      ["\x00145"]
      (some (YulSemantics.Expr.lit
         (YulSemantics.Literal.number 57896044618658097711785492504343953926634992332820282019728792003956564819968))),
    YulSemantics.Stmt.forLoop
      []
      (YulSemantics.Expr.var "\x00145")
      [YulSemantics.Stmt.assign
         ["\x00145"]
         (YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.shr)
           [YulSemantics.Expr.lit (YulSemantics.Literal.number 1), YulSemantics.Expr.var "\x00145"])]
      [YulSemantics.Stmt.exprStmt
         (YulSemantics.Expr.call
           "\x0016"
           [YulSemantics.Expr.var "\x00144", YulSemantics.Expr.var "\x00144", YulSemantics.Expr.var "\x00144"]),
       YulSemantics.Stmt.cond
         (YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.and)
           [YulSemantics.Expr.var "\x00142", YulSemantics.Expr.var "\x00145"])
         [YulSemantics.Stmt.exprStmt
            (YulSemantics.Expr.call
              "\x0016"
              [YulSemantics.Expr.var "\x00144", YulSemantics.Expr.var "\x00144", YulSemantics.Expr.var "\x00143"])]]],
 YulSemantics.Stmt.letDecl ["\x00146"] (some (YulSemantics.Expr.builtin (YulSemantics.EVM.Op.calldatasize) [])),
 YulSemantics.Stmt.cond
   (YulSemantics.Expr.builtin
     (YulSemantics.EVM.Op.or)
     [YulSemantics.Expr.builtin (YulSemantics.EVM.Op.iszero) [YulSemantics.Expr.var "\x00146"],
      YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mod)
        [YulSemantics.Expr.var "\x00146", YulSemantics.Expr.lit (YulSemantics.Literal.number 160)]])
   [YulSemantics.Stmt.exprStmt (YulSemantics.Expr.builtin (YulSemantics.EVM.Op.invalid) [])],
 YulSemantics.Stmt.letDecl [] none,
 YulSemantics.Stmt.letDecl [] none,
 YulSemantics.Stmt.exprStmt
   (YulSemantics.Expr.builtin
     (YulSemantics.EVM.Op.mstore)
     [YulSemantics.Expr.lit (YulSemantics.Literal.number 2432), YulSemantics.Expr.lit (YulSemantics.Literal.number 0)]),
 YulSemantics.Stmt.exprStmt
   (YulSemantics.Expr.builtin
     (YulSemantics.EVM.Op.mstore)
     [YulSemantics.Expr.lit (YulSemantics.Literal.number 2464), YulSemantics.Expr.lit (YulSemantics.Literal.number 0)]),
 YulSemantics.Stmt.exprStmt
   (YulSemantics.Expr.builtin
     (YulSemantics.EVM.Op.mstore)
     [YulSemantics.Expr.lit (YulSemantics.Literal.number 2496), YulSemantics.Expr.lit (YulSemantics.Literal.number 0)]),
 YulSemantics.Stmt.exprStmt
   (YulSemantics.Expr.builtin
     (YulSemantics.EVM.Op.mstore)
     [YulSemantics.Expr.lit (YulSemantics.Literal.number 2528), YulSemantics.Expr.lit (YulSemantics.Literal.number 0)]),
 YulSemantics.Stmt.forLoop
   [YulSemantics.Stmt.letDecl ["\x00151"] (some (YulSemantics.Expr.lit (YulSemantics.Literal.number 0)))]
   (YulSemantics.Expr.builtin
     (YulSemantics.EVM.Op.lt)
     [YulSemantics.Expr.var "\x00151", YulSemantics.Expr.var "\x00146"])
   [YulSemantics.Stmt.assign
      ["\x00151"]
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.add)
        [YulSemantics.Expr.var "\x00151", YulSemantics.Expr.lit (YulSemantics.Literal.number 160)])]
   [YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mstore)
        [YulSemantics.Expr.lit (YulSemantics.Literal.number 2048),
         YulSemantics.Expr.builtin (YulSemantics.EVM.Op.calldataload) [YulSemantics.Expr.var "\x00151"]]),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mstore)
        [YulSemantics.Expr.lit (YulSemantics.Literal.number 2080),
         YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.calldataload)
           [YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.add)
              [YulSemantics.Expr.var "\x00151", YulSemantics.Expr.lit (YulSemantics.Literal.number 32)]]]),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mstore)
        [YulSemantics.Expr.lit (YulSemantics.Literal.number 2112),
         YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.calldataload)
           [YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.add)
              [YulSemantics.Expr.var "\x00151", YulSemantics.Expr.lit (YulSemantics.Literal.number 64)]]]),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mstore)
        [YulSemantics.Expr.lit (YulSemantics.Literal.number 2144),
         YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.calldataload)
           [YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.add)
              [YulSemantics.Expr.var "\x00151", YulSemantics.Expr.lit (YulSemantics.Literal.number 96)]]]),
    YulSemantics.Stmt.cond
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.or)
        [YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.shr)
           [YulSemantics.Expr.lit (YulSemantics.Literal.number 128),
            YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.mload)
              [YulSemantics.Expr.lit (YulSemantics.Literal.number 2048)]],
         YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.shr)
           [YulSemantics.Expr.lit (YulSemantics.Literal.number 128),
            YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.mload)
              [YulSemantics.Expr.lit (YulSemantics.Literal.number 2112)]]])
      [YulSemantics.Stmt.exprStmt (YulSemantics.Expr.builtin (YulSemantics.EVM.Op.invalid) [])],
    YulSemantics.Stmt.cond
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.iszero)
        [YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.and)
           [YulSemantics.Expr.call
              "\x001"
              [YulSemantics.Expr.builtin
                 (YulSemantics.EVM.Op.mload)
                 [YulSemantics.Expr.lit (YulSemantics.Literal.number 2048)],
               YulSemantics.Expr.builtin
                 (YulSemantics.EVM.Op.mload)
                 [YulSemantics.Expr.lit (YulSemantics.Literal.number 2080)]],
            YulSemantics.Expr.call
              "\x001"
              [YulSemantics.Expr.builtin
                 (YulSemantics.EVM.Op.mload)
                 [YulSemantics.Expr.lit (YulSemantics.Literal.number 2112)],
               YulSemantics.Expr.builtin
                 (YulSemantics.EVM.Op.mload)
                 [YulSemantics.Expr.lit (YulSemantics.Literal.number 2144)]]]])
      [YulSemantics.Stmt.exprStmt (YulSemantics.Expr.builtin (YulSemantics.EVM.Op.invalid) [])],
    YulSemantics.Stmt.cond
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.and)
        [YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.iszero)
           [YulSemantics.Expr.call "\x0015" [YulSemantics.Expr.lit (YulSemantics.Literal.number 2048)]],
         YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.iszero)
           [YulSemantics.Expr.call
              "\x0011"
              [YulSemantics.Expr.builtin
                 (YulSemantics.EVM.Op.mload)
                 [YulSemantics.Expr.lit (YulSemantics.Literal.number 2048)],
               YulSemantics.Expr.builtin
                 (YulSemantics.EVM.Op.mload)
                 [YulSemantics.Expr.lit (YulSemantics.Literal.number 2080)],
               YulSemantics.Expr.builtin
                 (YulSemantics.EVM.Op.mload)
                 [YulSemantics.Expr.lit (YulSemantics.Literal.number 2112)],
               YulSemantics.Expr.builtin
                 (YulSemantics.EVM.Op.mload)
                 [YulSemantics.Expr.lit (YulSemantics.Literal.number 2144)]]]])
      [YulSemantics.Stmt.exprStmt (YulSemantics.Expr.builtin (YulSemantics.EVM.Op.invalid) [])],
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.call
        "\x0017"
        [YulSemantics.Expr.lit
           (YulSemantics.Literal.number 52435875175126190479447740508185965837690552500527637822603658699938581184513),
         YulSemantics.Expr.lit (YulSemantics.Literal.number 2048),
         YulSemantics.Expr.lit (YulSemantics.Literal.number 2176)]),
    YulSemantics.Stmt.cond
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.iszero)
        [YulSemantics.Expr.call "\x0015" [YulSemantics.Expr.lit (YulSemantics.Literal.number 2176)]])
      [YulSemantics.Stmt.exprStmt (YulSemantics.Expr.builtin (YulSemantics.EVM.Op.invalid) [])],
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.call
        "\x0017"
        [YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.calldataload)
           [YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.add)
              [YulSemantics.Expr.var "\x00151", YulSemantics.Expr.lit (YulSemantics.Literal.number 128)]],
         YulSemantics.Expr.lit (YulSemantics.Literal.number 2048),
         YulSemantics.Expr.lit (YulSemantics.Literal.number 2304)]),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.call
        "\x0016"
        [YulSemantics.Expr.lit (YulSemantics.Literal.number 2432),
         YulSemantics.Expr.lit (YulSemantics.Literal.number 2432),
         YulSemantics.Expr.lit (YulSemantics.Literal.number 2304)])],
 YulSemantics.Stmt.letDecl [] none,
 YulSemantics.Stmt.letDecl [] none,
 YulSemantics.Stmt.letDecl
   ["fc1_78"]
   (some (YulSemantics.Expr.builtin
      (YulSemantics.EVM.Op.mload)
      [YulSemantics.Expr.lit (YulSemantics.Literal.number 2528)])),
 YulSemantics.Stmt.letDecl
   ["fc1_79"]
   (some (YulSemantics.Expr.builtin
      (YulSemantics.EVM.Op.mload)
      [YulSemantics.Expr.lit (YulSemantics.Literal.number 2496)])),
 YulSemantics.Stmt.letDecl
   ["fc1_80"]
   (some (YulSemantics.Expr.builtin
      (YulSemantics.EVM.Op.mload)
      [YulSemantics.Expr.lit (YulSemantics.Literal.number 2464)])),
 YulSemantics.Stmt.letDecl
   ["fc1_81"]
   (some (YulSemantics.Expr.builtin
      (YulSemantics.EVM.Op.mload)
      [YulSemantics.Expr.lit (YulSemantics.Literal.number 2432)])),
 YulSemantics.Stmt.exprStmt
   (YulSemantics.Expr.builtin
     (YulSemantics.EVM.Op.mstore)
     [YulSemantics.Expr.lit (YulSemantics.Literal.number 0), YulSemantics.Expr.var "fc1_81"]),
 YulSemantics.Stmt.exprStmt
   (YulSemantics.Expr.builtin
     (YulSemantics.EVM.Op.mstore)
     [YulSemantics.Expr.lit (YulSemantics.Literal.number 32), YulSemantics.Expr.var "fc1_80"]),
 YulSemantics.Stmt.exprStmt
   (YulSemantics.Expr.builtin
     (YulSemantics.EVM.Op.mstore)
     [YulSemantics.Expr.lit (YulSemantics.Literal.number 64), YulSemantics.Expr.var "fc1_79"]),
 YulSemantics.Stmt.exprStmt
   (YulSemantics.Expr.builtin
     (YulSemantics.EVM.Op.mstore)
     [YulSemantics.Expr.lit (YulSemantics.Literal.number 96), YulSemantics.Expr.var "fc1_78"]),
 YulSemantics.Stmt.exprStmt
   (YulSemantics.Expr.builtin
     (YulSemantics.EVM.Op.ret)
     [YulSemantics.Expr.lit (YulSemantics.Literal.number 0), YulSemantics.Expr.lit (YulSemantics.Literal.number 128)])]

end Challenge.Bls12381G1Msm.Reference.Proofs.Compilation
