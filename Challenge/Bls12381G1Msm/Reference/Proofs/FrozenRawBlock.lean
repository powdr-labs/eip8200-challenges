import YulEvmCompiler.Optimizer.Implementation.Pipeline

set_option warningAsError true

namespace Challenge.Bls12381G1Msm.Reference.Proofs.Compilation

open YulSemantics (Block)
open YulSemantics.EVM (Op)

/-- Generated exact raw AST decoded from `reference.yul`. -/
def frozenReferenceRawBlock : Block Op :=
[YulSemantics.Stmt.funDef
   "fpGeModulus"
   ["hi", "lo"]
   ["yes"]
   [YulSemantics.Stmt.letDecl
      ["pHi"]
      (some (YulSemantics.Expr.lit (YulSemantics.Literal.number 34565483545414906068789196026815425751))),
    YulSemantics.Stmt.letDecl
      ["pLo"]
      (some (YulSemantics.Expr.lit
         (YulSemantics.Literal.number 45442060874369865957053122457065728162598490762543039060009208264153100167851))),
    YulSemantics.Stmt.assign
      ["yes"]
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.or)
        [YulSemantics.Expr.builtin (YulSemantics.EVM.Op.gt) [YulSemantics.Expr.var "hi", YulSemantics.Expr.var "pHi"],
         YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.and)
           [YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.eq)
              [YulSemantics.Expr.var "hi", YulSemantics.Expr.var "pHi"],
            YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.iszero)
              [YulSemantics.Expr.builtin
                 (YulSemantics.EVM.Op.lt)
                 [YulSemantics.Expr.var "lo", YulSemantics.Expr.var "pLo"]]]])],
 YulSemantics.Stmt.funDef
   "fpValid"
   ["hi", "lo"]
   ["yes"]
   [YulSemantics.Stmt.assign
      ["yes"]
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.iszero)
        [YulSemantics.Expr.call "fpGeModulus" [YulSemantics.Expr.var "hi", YulSemantics.Expr.var "lo"]])],
 YulSemantics.Stmt.funDef
   "fpZero"
   ["hi", "lo"]
   ["yes"]
   [YulSemantics.Stmt.assign
      ["yes"]
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.and)
        [YulSemantics.Expr.builtin (YulSemantics.EVM.Op.iszero) [YulSemantics.Expr.var "hi"],
         YulSemantics.Expr.builtin (YulSemantics.EVM.Op.iszero) [YulSemantics.Expr.var "lo"]])],
 YulSemantics.Stmt.funDef
   "fpEq"
   ["aHi", "aLo", "bHi", "bLo"]
   ["yes"]
   [YulSemantics.Stmt.assign
      ["yes"]
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.and)
        [YulSemantics.Expr.builtin (YulSemantics.EVM.Op.eq) [YulSemantics.Expr.var "aHi", YulSemantics.Expr.var "bHi"],
         YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.eq)
           [YulSemantics.Expr.var "aLo", YulSemantics.Expr.var "bLo"]])],
 YulSemantics.Stmt.funDef
   "fpAdd"
   ["aHi", "aLo", "bHi", "bLo"]
   ["zHi", "zLo"]
   [YulSemantics.Stmt.assign
      ["zLo"]
      (YulSemantics.Expr.builtin (YulSemantics.EVM.Op.add) [YulSemantics.Expr.var "aLo", YulSemantics.Expr.var "bLo"]),
    YulSemantics.Stmt.assign
      ["zHi"]
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.add)
        [YulSemantics.Expr.builtin (YulSemantics.EVM.Op.add) [YulSemantics.Expr.var "aHi", YulSemantics.Expr.var "bHi"],
         YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.lt)
           [YulSemantics.Expr.var "zLo", YulSemantics.Expr.var "aLo"]]),
    YulSemantics.Stmt.cond
      (YulSemantics.Expr.call "fpGeModulus" [YulSemantics.Expr.var "zHi", YulSemantics.Expr.var "zLo"])
      [YulSemantics.Stmt.letDecl
         ["pHi"]
         (some (YulSemantics.Expr.lit (YulSemantics.Literal.number 34565483545414906068789196026815425751))),
       YulSemantics.Stmt.letDecl
         ["pLo"]
         (some (YulSemantics.Expr.lit
            (YulSemantics.Literal.number
              45442060874369865957053122457065728162598490762543039060009208264153100167851))),
       YulSemantics.Stmt.letDecl
         ["nextLo"]
         (some (YulSemantics.Expr.builtin
            (YulSemantics.EVM.Op.sub)
            [YulSemantics.Expr.var "zLo", YulSemantics.Expr.var "pLo"])),
       YulSemantics.Stmt.assign
         ["zHi"]
         (YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.sub)
           [YulSemantics.Expr.var "zHi",
            YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.add)
              [YulSemantics.Expr.var "pHi",
               YulSemantics.Expr.builtin
                 (YulSemantics.EVM.Op.gt)
                 [YulSemantics.Expr.var "pLo", YulSemantics.Expr.var "zLo"]]]),
       YulSemantics.Stmt.assign ["zLo"] (YulSemantics.Expr.var "nextLo")]],
 YulSemantics.Stmt.funDef
   "fpSub"
   ["aHi", "aLo", "bHi", "bLo"]
   ["zHi", "zLo"]
   [YulSemantics.Stmt.assign
      ["zLo"]
      (YulSemantics.Expr.builtin (YulSemantics.EVM.Op.sub) [YulSemantics.Expr.var "aLo", YulSemantics.Expr.var "bLo"]),
    YulSemantics.Stmt.assign
      ["zHi"]
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.sub)
        [YulSemantics.Expr.builtin (YulSemantics.EVM.Op.sub) [YulSemantics.Expr.var "aHi", YulSemantics.Expr.var "bHi"],
         YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.gt)
           [YulSemantics.Expr.var "bLo", YulSemantics.Expr.var "aLo"]]),
    YulSemantics.Stmt.letDecl
      ["pHi"]
      (some (YulSemantics.Expr.lit (YulSemantics.Literal.number 34565483545414906068789196026815425751))),
    YulSemantics.Stmt.cond
      (YulSemantics.Expr.builtin (YulSemantics.EVM.Op.gt) [YulSemantics.Expr.var "zHi", YulSemantics.Expr.var "pHi"])
      [YulSemantics.Stmt.letDecl
         ["pLo"]
         (some (YulSemantics.Expr.lit
            (YulSemantics.Literal.number
              45442060874369865957053122457065728162598490762543039060009208264153100167851))),
       YulSemantics.Stmt.letDecl
         ["nextLo"]
         (some (YulSemantics.Expr.builtin
            (YulSemantics.EVM.Op.add)
            [YulSemantics.Expr.var "zLo", YulSemantics.Expr.var "pLo"])),
       YulSemantics.Stmt.assign
         ["zHi"]
         (YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.add)
           [YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.add)
              [YulSemantics.Expr.var "zHi", YulSemantics.Expr.var "pHi"],
            YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.lt)
              [YulSemantics.Expr.var "nextLo", YulSemantics.Expr.var "zLo"]]),
       YulSemantics.Stmt.assign ["zLo"] (YulSemantics.Expr.var "nextLo")]],
 YulSemantics.Stmt.funDef
   "fullMul"
   ["aHi", "aLo", "bHi", "bLo"]
   ["r2", "r1", "r0"]
   [YulSemantics.Stmt.assign
      ["r0"]
      (YulSemantics.Expr.builtin (YulSemantics.EVM.Op.mul) [YulSemantics.Expr.var "aLo", YulSemantics.Expr.var "bLo"]),
    YulSemantics.Stmt.letDecl
      ["mm0"]
      (some (YulSemantics.Expr.builtin
         (YulSemantics.EVM.Op.mulmod)
         [YulSemantics.Expr.var "aLo",
          YulSemantics.Expr.var "bLo",
          YulSemantics.Expr.builtin
            (YulSemantics.EVM.Op.not)
            [YulSemantics.Expr.lit (YulSemantics.Literal.number 0)]])),
    YulSemantics.Stmt.letDecl
      ["hi0"]
      (some (YulSemantics.Expr.builtin
         (YulSemantics.EVM.Op.sub)
         [YulSemantics.Expr.builtin (YulSemantics.EVM.Op.sub) [YulSemantics.Expr.var "mm0", YulSemantics.Expr.var "r0"],
          YulSemantics.Expr.builtin
            (YulSemantics.EVM.Op.lt)
            [YulSemantics.Expr.var "mm0", YulSemantics.Expr.var "r0"]])),
    YulSemantics.Stmt.letDecl
      ["lo1"]
      (some (YulSemantics.Expr.builtin
         (YulSemantics.EVM.Op.mul)
         [YulSemantics.Expr.var "aHi", YulSemantics.Expr.var "bLo"])),
    YulSemantics.Stmt.letDecl
      ["mm1"]
      (some (YulSemantics.Expr.builtin
         (YulSemantics.EVM.Op.mulmod)
         [YulSemantics.Expr.var "aHi",
          YulSemantics.Expr.var "bLo",
          YulSemantics.Expr.builtin
            (YulSemantics.EVM.Op.not)
            [YulSemantics.Expr.lit (YulSemantics.Literal.number 0)]])),
    YulSemantics.Stmt.letDecl
      ["hi1"]
      (some (YulSemantics.Expr.builtin
         (YulSemantics.EVM.Op.sub)
         [YulSemantics.Expr.builtin
            (YulSemantics.EVM.Op.sub)
            [YulSemantics.Expr.var "mm1", YulSemantics.Expr.var "lo1"],
          YulSemantics.Expr.builtin
            (YulSemantics.EVM.Op.lt)
            [YulSemantics.Expr.var "mm1", YulSemantics.Expr.var "lo1"]])),
    YulSemantics.Stmt.letDecl
      ["lo2"]
      (some (YulSemantics.Expr.builtin
         (YulSemantics.EVM.Op.mul)
         [YulSemantics.Expr.var "aLo", YulSemantics.Expr.var "bHi"])),
    YulSemantics.Stmt.letDecl
      ["mm2"]
      (some (YulSemantics.Expr.builtin
         (YulSemantics.EVM.Op.mulmod)
         [YulSemantics.Expr.var "aLo",
          YulSemantics.Expr.var "bHi",
          YulSemantics.Expr.builtin
            (YulSemantics.EVM.Op.not)
            [YulSemantics.Expr.lit (YulSemantics.Literal.number 0)]])),
    YulSemantics.Stmt.letDecl
      ["hi2"]
      (some (YulSemantics.Expr.builtin
         (YulSemantics.EVM.Op.sub)
         [YulSemantics.Expr.builtin
            (YulSemantics.EVM.Op.sub)
            [YulSemantics.Expr.var "mm2", YulSemantics.Expr.var "lo2"],
          YulSemantics.Expr.builtin
            (YulSemantics.EVM.Op.lt)
            [YulSemantics.Expr.var "mm2", YulSemantics.Expr.var "lo2"]])),
    YulSemantics.Stmt.assign
      ["r1"]
      (YulSemantics.Expr.builtin (YulSemantics.EVM.Op.add) [YulSemantics.Expr.var "hi0", YulSemantics.Expr.var "lo1"]),
    YulSemantics.Stmt.letDecl
      ["carry"]
      (some (YulSemantics.Expr.builtin
         (YulSemantics.EVM.Op.lt)
         [YulSemantics.Expr.var "r1", YulSemantics.Expr.var "hi0"])),
    YulSemantics.Stmt.letDecl
      ["nextR1"]
      (some (YulSemantics.Expr.builtin
         (YulSemantics.EVM.Op.add)
         [YulSemantics.Expr.var "r1", YulSemantics.Expr.var "lo2"])),
    YulSemantics.Stmt.assign
      ["carry"]
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.add)
        [YulSemantics.Expr.var "carry",
         YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.lt)
           [YulSemantics.Expr.var "nextR1", YulSemantics.Expr.var "r1"]]),
    YulSemantics.Stmt.assign ["r1"] (YulSemantics.Expr.var "nextR1"),
    YulSemantics.Stmt.assign
      ["r2"]
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.add)
        [YulSemantics.Expr.builtin (YulSemantics.EVM.Op.add) [YulSemantics.Expr.var "hi1", YulSemantics.Expr.var "hi2"],
         YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.add)
           [YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.mul)
              [YulSemantics.Expr.var "aHi", YulSemantics.Expr.var "bHi"],
            YulSemantics.Expr.var "carry"]])],
 YulSemantics.Stmt.funDef
   "storeFp"
   ["ptr", "hi", "lo"]
   []
   [YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mstore)
        [YulSemantics.Expr.var "ptr",
         YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.shl)
           [YulSemantics.Expr.lit (YulSemantics.Literal.number 128), YulSemantics.Expr.var "hi"]]),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mstore)
        [YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.add)
           [YulSemantics.Expr.var "ptr", YulSemantics.Expr.lit (YulSemantics.Literal.number 16)],
         YulSemantics.Expr.var "lo"])],
 YulSemantics.Stmt.funDef
   "storeModulus"
   ["ptr"]
   []
   [YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.call
        "storeFp"
        [YulSemantics.Expr.var "ptr",
         YulSemantics.Expr.lit (YulSemantics.Literal.number 34565483545414906068789196026815425751),
         YulSemantics.Expr.lit
           (YulSemantics.Literal.number
             45442060874369865957053122457065728162598490762543039060009208264153100167851)])],
 YulSemantics.Stmt.funDef
   "fpMul"
   ["aHi", "aLo", "bHi", "bLo"]
   ["zHi", "zLo"]
   [YulSemantics.Stmt.letDecl
      ["r2", "r1", "r0"]
      (some (YulSemantics.Expr.call
         "fullMul"
         [YulSemantics.Expr.var "aHi",
          YulSemantics.Expr.var "aLo",
          YulSemantics.Expr.var "bHi",
          YulSemantics.Expr.var "bLo"])),
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
        [YulSemantics.Expr.lit (YulSemantics.Literal.number 1120), YulSemantics.Expr.var "r2"]),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mstore)
        [YulSemantics.Expr.lit (YulSemantics.Literal.number 1152), YulSemantics.Expr.var "r1"]),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mstore)
        [YulSemantics.Expr.lit (YulSemantics.Literal.number 1184), YulSemantics.Expr.var "r0"]),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mstore8)
        [YulSemantics.Expr.lit (YulSemantics.Literal.number 1216),
         YulSemantics.Expr.lit (YulSemantics.Literal.number 1)]),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.call "storeModulus" [YulSemantics.Expr.lit (YulSemantics.Literal.number 1217)]),
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
      ["zHi"]
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.shr)
        [YulSemantics.Expr.lit (YulSemantics.Literal.number 128),
         YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.mload)
           [YulSemantics.Expr.lit (YulSemantics.Literal.number 1280)]]),
    YulSemantics.Stmt.assign
      ["zLo"]
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mload)
        [YulSemantics.Expr.lit (YulSemantics.Literal.number 1296)])],
 YulSemantics.Stmt.funDef
   "fpInv"
   ["aHi", "aLo"]
   ["zHi", "zLo"]
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
        "storeFp"
        [YulSemantics.Expr.lit (YulSemantics.Literal.number 1120),
         YulSemantics.Expr.var "aHi",
         YulSemantics.Expr.var "aLo"]),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.call
        "storeFp"
        [YulSemantics.Expr.lit (YulSemantics.Literal.number 1168),
         YulSemantics.Expr.lit (YulSemantics.Literal.number 34565483545414906068789196026815425751),
         YulSemantics.Expr.lit
           (YulSemantics.Literal.number
             45442060874369865957053122457065728162598490762543039060009208264153100167849)]),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.call "storeModulus" [YulSemantics.Expr.lit (YulSemantics.Literal.number 1216)]),
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
      ["zHi"]
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.shr)
        [YulSemantics.Expr.lit (YulSemantics.Literal.number 128),
         YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.mload)
           [YulSemantics.Expr.lit (YulSemantics.Literal.number 1280)]]),
    YulSemantics.Stmt.assign
      ["zLo"]
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mload)
        [YulSemantics.Expr.lit (YulSemantics.Literal.number 1296)])],
 YulSemantics.Stmt.funDef
   "onCurve"
   ["xHi", "xLo", "yHi", "yLo"]
   ["yes"]
   [YulSemantics.Stmt.letDecl
      ["lhsHi", "lhsLo"]
      (some (YulSemantics.Expr.call
         "fpMul"
         [YulSemantics.Expr.var "yHi",
          YulSemantics.Expr.var "yLo",
          YulSemantics.Expr.var "yHi",
          YulSemantics.Expr.var "yLo"])),
    YulSemantics.Stmt.letDecl
      ["x2Hi", "x2Lo"]
      (some (YulSemantics.Expr.call
         "fpMul"
         [YulSemantics.Expr.var "xHi",
          YulSemantics.Expr.var "xLo",
          YulSemantics.Expr.var "xHi",
          YulSemantics.Expr.var "xLo"])),
    YulSemantics.Stmt.letDecl
      ["rhsHi", "rhsLo"]
      (some (YulSemantics.Expr.call
         "fpMul"
         [YulSemantics.Expr.var "x2Hi",
          YulSemantics.Expr.var "x2Lo",
          YulSemantics.Expr.var "xHi",
          YulSemantics.Expr.var "xLo"])),
    YulSemantics.Stmt.assign
      ["rhsHi", "rhsLo"]
      (YulSemantics.Expr.call
        "fpAdd"
        [YulSemantics.Expr.var "rhsHi",
         YulSemantics.Expr.var "rhsLo",
         YulSemantics.Expr.lit (YulSemantics.Literal.number 0),
         YulSemantics.Expr.lit (YulSemantics.Literal.number 4)]),
    YulSemantics.Stmt.assign
      ["yes"]
      (YulSemantics.Expr.call
        "fpEq"
        [YulSemantics.Expr.var "lhsHi",
         YulSemantics.Expr.var "lhsLo",
         YulSemantics.Expr.var "rhsHi",
         YulSemantics.Expr.var "rhsLo"])],
 YulSemantics.Stmt.funDef
   "storePoint"
   ["ptr", "xHi", "xLo", "yHi", "yLo"]
   []
   [YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mstore)
        [YulSemantics.Expr.var "ptr", YulSemantics.Expr.var "xHi"]),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mstore)
        [YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.add)
           [YulSemantics.Expr.var "ptr", YulSemantics.Expr.lit (YulSemantics.Literal.number 32)],
         YulSemantics.Expr.var "xLo"]),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mstore)
        [YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.add)
           [YulSemantics.Expr.var "ptr", YulSemantics.Expr.lit (YulSemantics.Literal.number 64)],
         YulSemantics.Expr.var "yHi"]),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mstore)
        [YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.add)
           [YulSemantics.Expr.var "ptr", YulSemantics.Expr.lit (YulSemantics.Literal.number 96)],
         YulSemantics.Expr.var "yLo"])],
 YulSemantics.Stmt.funDef
   "storeInfinity"
   ["ptr"]
   []
   [YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.call
        "storePoint"
        [YulSemantics.Expr.var "ptr",
         YulSemantics.Expr.lit (YulSemantics.Literal.number 0),
         YulSemantics.Expr.lit (YulSemantics.Literal.number 0),
         YulSemantics.Expr.lit (YulSemantics.Literal.number 0),
         YulSemantics.Expr.lit (YulSemantics.Literal.number 0)])],
 YulSemantics.Stmt.funDef
   "copyPoint"
   ["dst", "src"]
   []
   [YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.call
        "storePoint"
        [YulSemantics.Expr.var "dst",
         YulSemantics.Expr.builtin (YulSemantics.EVM.Op.mload) [YulSemantics.Expr.var "src"],
         YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.mload)
           [YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.add)
              [YulSemantics.Expr.var "src", YulSemantics.Expr.lit (YulSemantics.Literal.number 32)]],
         YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.mload)
           [YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.add)
              [YulSemantics.Expr.var "src", YulSemantics.Expr.lit (YulSemantics.Literal.number 64)]],
         YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.mload)
           [YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.add)
              [YulSemantics.Expr.var "src", YulSemantics.Expr.lit (YulSemantics.Literal.number 96)]]])],
 YulSemantics.Stmt.funDef
   "pointInfinity"
   ["ptr"]
   ["yes"]
   [YulSemantics.Stmt.assign
      ["yes"]
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.and)
        [YulSemantics.Expr.call
           "fpZero"
           [YulSemantics.Expr.builtin (YulSemantics.EVM.Op.mload) [YulSemantics.Expr.var "ptr"],
            YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.mload)
              [YulSemantics.Expr.builtin
                 (YulSemantics.EVM.Op.add)
                 [YulSemantics.Expr.var "ptr", YulSemantics.Expr.lit (YulSemantics.Literal.number 32)]]],
         YulSemantics.Expr.call
           "fpZero"
           [YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.mload)
              [YulSemantics.Expr.builtin
                 (YulSemantics.EVM.Op.add)
                 [YulSemantics.Expr.var "ptr", YulSemantics.Expr.lit (YulSemantics.Literal.number 64)]],
            YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.mload)
              [YulSemantics.Expr.builtin
                 (YulSemantics.EVM.Op.add)
                 [YulSemantics.Expr.var "ptr", YulSemantics.Expr.lit (YulSemantics.Literal.number 96)]]]])],
 YulSemantics.Stmt.funDef
   "pointAdd"
   ["out", "left", "right"]
   []
   [YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mstore)
        [YulSemantics.Expr.lit (YulSemantics.Literal.number 1536), YulSemantics.Expr.var "out"]),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mstore)
        [YulSemantics.Expr.lit (YulSemantics.Literal.number 1568), YulSemantics.Expr.var "left"]),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mstore)
        [YulSemantics.Expr.lit (YulSemantics.Literal.number 1600), YulSemantics.Expr.var "right"]),
    YulSemantics.Stmt.cond
      (YulSemantics.Expr.call
        "pointInfinity"
        [YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.mload)
           [YulSemantics.Expr.lit (YulSemantics.Literal.number 1568)]])
      [YulSemantics.Stmt.exprStmt
         (YulSemantics.Expr.call
           "copyPoint"
           [YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.mload)
              [YulSemantics.Expr.lit (YulSemantics.Literal.number 1536)],
            YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.mload)
              [YulSemantics.Expr.lit (YulSemantics.Literal.number 1600)]]),
       YulSemantics.Stmt.leave],
    YulSemantics.Stmt.cond
      (YulSemantics.Expr.call
        "pointInfinity"
        [YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.mload)
           [YulSemantics.Expr.lit (YulSemantics.Literal.number 1600)]])
      [YulSemantics.Stmt.exprStmt
         (YulSemantics.Expr.call
           "copyPoint"
           [YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.mload)
              [YulSemantics.Expr.lit (YulSemantics.Literal.number 1536)],
            YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.mload)
              [YulSemantics.Expr.lit (YulSemantics.Literal.number 1568)]]),
       YulSemantics.Stmt.leave],
    YulSemantics.Stmt.cond
      (YulSemantics.Expr.call
        "fpEq"
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
         ["sumHi", "sumLo"]
         (some (YulSemantics.Expr.call
            "fpAdd"
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
         (YulSemantics.Expr.call "fpZero" [YulSemantics.Expr.var "sumHi", YulSemantics.Expr.var "sumLo"])
         [YulSemantics.Stmt.exprStmt
            (YulSemantics.Expr.call
              "storeInfinity"
              [YulSemantics.Expr.builtin
                 (YulSemantics.EVM.Op.mload)
                 [YulSemantics.Expr.lit (YulSemantics.Literal.number 1536)]]),
          YulSemantics.Stmt.leave],
       YulSemantics.Stmt.letDecl
         ["xSqHi", "xSqLo"]
         (some (YulSemantics.Expr.call
            "fpMul"
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
         ["numHi", "numLo"]
         (some (YulSemantics.Expr.call
            "fpAdd"
            [YulSemantics.Expr.var "xSqHi",
             YulSemantics.Expr.var "xSqLo",
             YulSemantics.Expr.var "xSqHi",
             YulSemantics.Expr.var "xSqLo"])),
       YulSemantics.Stmt.assign
         ["numHi", "numLo"]
         (YulSemantics.Expr.call
           "fpAdd"
           [YulSemantics.Expr.var "numHi",
            YulSemantics.Expr.var "numLo",
            YulSemantics.Expr.var "xSqHi",
            YulSemantics.Expr.var "xSqLo"]),
       YulSemantics.Stmt.letDecl
         ["denHi", "denLo"]
         (some (YulSemantics.Expr.call
            "fpAdd"
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
       YulSemantics.Stmt.letDecl
         ["denInvHi", "denInvLo"]
         (some (YulSemantics.Expr.call "fpInv" [YulSemantics.Expr.var "denHi", YulSemantics.Expr.var "denLo"])),
       YulSemantics.Stmt.letDecl
         ["lamHi", "lamLo"]
         (some (YulSemantics.Expr.call
            "fpMul"
            [YulSemantics.Expr.var "numHi",
             YulSemantics.Expr.var "numLo",
             YulSemantics.Expr.var "denInvHi",
             YulSemantics.Expr.var "denInvLo"])),
       YulSemantics.Stmt.letDecl
         ["x3Hi", "x3Lo"]
         (some (YulSemantics.Expr.call
            "fpMul"
            [YulSemantics.Expr.var "lamHi",
             YulSemantics.Expr.var "lamLo",
             YulSemantics.Expr.var "lamHi",
             YulSemantics.Expr.var "lamLo"])),
       YulSemantics.Stmt.assign
         ["x3Hi", "x3Lo"]
         (YulSemantics.Expr.call
           "fpSub"
           [YulSemantics.Expr.var "x3Hi",
            YulSemantics.Expr.var "x3Lo",
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
                  YulSemantics.Expr.lit (YulSemantics.Literal.number 32)]]]),
       YulSemantics.Stmt.assign
         ["x3Hi", "x3Lo"]
         (YulSemantics.Expr.call
           "fpSub"
           [YulSemantics.Expr.var "x3Hi",
            YulSemantics.Expr.var "x3Lo",
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
                  YulSemantics.Expr.lit (YulSemantics.Literal.number 32)]]]),
       YulSemantics.Stmt.letDecl
         ["deltaHi", "deltaLo"]
         (some (YulSemantics.Expr.call
            "fpSub"
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
             YulSemantics.Expr.var "x3Hi",
             YulSemantics.Expr.var "x3Lo"])),
       YulSemantics.Stmt.letDecl
         ["y3Hi", "y3Lo"]
         (some (YulSemantics.Expr.call
            "fpMul"
            [YulSemantics.Expr.var "lamHi",
             YulSemantics.Expr.var "lamLo",
             YulSemantics.Expr.var "deltaHi",
             YulSemantics.Expr.var "deltaLo"])),
       YulSemantics.Stmt.assign
         ["y3Hi", "y3Lo"]
         (YulSemantics.Expr.call
           "fpSub"
           [YulSemantics.Expr.var "y3Hi",
            YulSemantics.Expr.var "y3Lo",
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
                  YulSemantics.Expr.lit (YulSemantics.Literal.number 96)]]]),
       YulSemantics.Stmt.exprStmt
         (YulSemantics.Expr.call
           "storePoint"
           [YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.mload)
              [YulSemantics.Expr.lit (YulSemantics.Literal.number 1536)],
            YulSemantics.Expr.var "x3Hi",
            YulSemantics.Expr.var "x3Lo",
            YulSemantics.Expr.var "y3Hi",
            YulSemantics.Expr.var "y3Lo"]),
       YulSemantics.Stmt.leave],
    YulSemantics.Stmt.letDecl
      ["numHi", "numLo"]
      (some (YulSemantics.Expr.call
         "fpSub"
         [YulSemantics.Expr.builtin
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
    YulSemantics.Stmt.letDecl
      ["denHi", "denLo"]
      (some (YulSemantics.Expr.call
         "fpSub"
         [YulSemantics.Expr.builtin
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
      ["denInvHi", "denInvLo"]
      (some (YulSemantics.Expr.call "fpInv" [YulSemantics.Expr.var "denHi", YulSemantics.Expr.var "denLo"])),
    YulSemantics.Stmt.letDecl
      ["lamHi", "lamLo"]
      (some (YulSemantics.Expr.call
         "fpMul"
         [YulSemantics.Expr.var "numHi",
          YulSemantics.Expr.var "numLo",
          YulSemantics.Expr.var "denInvHi",
          YulSemantics.Expr.var "denInvLo"])),
    YulSemantics.Stmt.letDecl
      ["x3Hi", "x3Lo"]
      (some (YulSemantics.Expr.call
         "fpMul"
         [YulSemantics.Expr.var "lamHi",
          YulSemantics.Expr.var "lamLo",
          YulSemantics.Expr.var "lamHi",
          YulSemantics.Expr.var "lamLo"])),
    YulSemantics.Stmt.assign
      ["x3Hi", "x3Lo"]
      (YulSemantics.Expr.call
        "fpSub"
        [YulSemantics.Expr.var "x3Hi",
         YulSemantics.Expr.var "x3Lo",
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
               YulSemantics.Expr.lit (YulSemantics.Literal.number 32)]]]),
    YulSemantics.Stmt.assign
      ["x3Hi", "x3Lo"]
      (YulSemantics.Expr.call
        "fpSub"
        [YulSemantics.Expr.var "x3Hi",
         YulSemantics.Expr.var "x3Lo",
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
               YulSemantics.Expr.lit (YulSemantics.Literal.number 32)]]]),
    YulSemantics.Stmt.letDecl
      ["deltaHi", "deltaLo"]
      (some (YulSemantics.Expr.call
         "fpSub"
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
          YulSemantics.Expr.var "x3Hi",
          YulSemantics.Expr.var "x3Lo"])),
    YulSemantics.Stmt.letDecl
      ["y3Hi", "y3Lo"]
      (some (YulSemantics.Expr.call
         "fpMul"
         [YulSemantics.Expr.var "lamHi",
          YulSemantics.Expr.var "lamLo",
          YulSemantics.Expr.var "deltaHi",
          YulSemantics.Expr.var "deltaLo"])),
    YulSemantics.Stmt.assign
      ["y3Hi", "y3Lo"]
      (YulSemantics.Expr.call
        "fpSub"
        [YulSemantics.Expr.var "y3Hi",
         YulSemantics.Expr.var "y3Lo",
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
               YulSemantics.Expr.lit (YulSemantics.Literal.number 96)]]]),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.call
        "storePoint"
        [YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.mload)
           [YulSemantics.Expr.lit (YulSemantics.Literal.number 1536)],
         YulSemantics.Expr.var "x3Hi",
         YulSemantics.Expr.var "x3Lo",
         YulSemantics.Expr.var "y3Hi",
         YulSemantics.Expr.var "y3Lo"])],
 YulSemantics.Stmt.funDef
   "scalarMul"
   ["scalar", "point", "out"]
   []
   [YulSemantics.Stmt.exprStmt (YulSemantics.Expr.call "storeInfinity" [YulSemantics.Expr.var "out"]),
    YulSemantics.Stmt.letDecl
      ["bit"]
      (some (YulSemantics.Expr.builtin
         (YulSemantics.EVM.Op.shl)
         [YulSemantics.Expr.lit (YulSemantics.Literal.number 255),
          YulSemantics.Expr.lit (YulSemantics.Literal.number 1)])),
    YulSemantics.Stmt.forLoop
      []
      (YulSemantics.Expr.var "bit")
      [YulSemantics.Stmt.assign
         ["bit"]
         (YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.shr)
           [YulSemantics.Expr.lit (YulSemantics.Literal.number 1), YulSemantics.Expr.var "bit"])]
      [YulSemantics.Stmt.exprStmt
         (YulSemantics.Expr.call
           "pointAdd"
           [YulSemantics.Expr.var "out", YulSemantics.Expr.var "out", YulSemantics.Expr.var "out"]),
       YulSemantics.Stmt.cond
         (YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.and)
           [YulSemantics.Expr.var "scalar", YulSemantics.Expr.var "bit"])
         [YulSemantics.Stmt.exprStmt
            (YulSemantics.Expr.call
              "pointAdd"
              [YulSemantics.Expr.var "out", YulSemantics.Expr.var "out", YulSemantics.Expr.var "point"])]]],
 YulSemantics.Stmt.letDecl ["size"] (some (YulSemantics.Expr.builtin (YulSemantics.EVM.Op.calldatasize) [])),
 YulSemantics.Stmt.cond
   (YulSemantics.Expr.builtin
     (YulSemantics.EVM.Op.or)
     [YulSemantics.Expr.builtin (YulSemantics.EVM.Op.iszero) [YulSemantics.Expr.var "size"],
      YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mod)
        [YulSemantics.Expr.var "size", YulSemantics.Expr.lit (YulSemantics.Literal.number 160)]])
   [YulSemantics.Stmt.exprStmt (YulSemantics.Expr.builtin (YulSemantics.EVM.Op.invalid) [])],
 YulSemantics.Stmt.letDecl ["point"] (some (YulSemantics.Expr.lit (YulSemantics.Literal.number 2048))),
 YulSemantics.Stmt.letDecl ["subgroupOut"] (some (YulSemantics.Expr.lit (YulSemantics.Literal.number 2176))),
 YulSemantics.Stmt.letDecl ["termOut"] (some (YulSemantics.Expr.lit (YulSemantics.Literal.number 2304))),
 YulSemantics.Stmt.letDecl ["acc"] (some (YulSemantics.Expr.lit (YulSemantics.Literal.number 2432))),
 YulSemantics.Stmt.exprStmt (YulSemantics.Expr.call "storeInfinity" [YulSemantics.Expr.var "acc"]),
 YulSemantics.Stmt.forLoop
   [YulSemantics.Stmt.letDecl ["offset"] (some (YulSemantics.Expr.lit (YulSemantics.Literal.number 0)))]
   (YulSemantics.Expr.builtin (YulSemantics.EVM.Op.lt) [YulSemantics.Expr.var "offset", YulSemantics.Expr.var "size"])
   [YulSemantics.Stmt.assign
      ["offset"]
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.add)
        [YulSemantics.Expr.var "offset", YulSemantics.Expr.lit (YulSemantics.Literal.number 160)])]
   [YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mstore)
        [YulSemantics.Expr.var "point",
         YulSemantics.Expr.builtin (YulSemantics.EVM.Op.calldataload) [YulSemantics.Expr.var "offset"]]),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mstore)
        [YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.add)
           [YulSemantics.Expr.var "point", YulSemantics.Expr.lit (YulSemantics.Literal.number 32)],
         YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.calldataload)
           [YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.add)
              [YulSemantics.Expr.var "offset", YulSemantics.Expr.lit (YulSemantics.Literal.number 32)]]]),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mstore)
        [YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.add)
           [YulSemantics.Expr.var "point", YulSemantics.Expr.lit (YulSemantics.Literal.number 64)],
         YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.calldataload)
           [YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.add)
              [YulSemantics.Expr.var "offset", YulSemantics.Expr.lit (YulSemantics.Literal.number 64)]]]),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.mstore)
        [YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.add)
           [YulSemantics.Expr.var "point", YulSemantics.Expr.lit (YulSemantics.Literal.number 96)],
         YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.calldataload)
           [YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.add)
              [YulSemantics.Expr.var "offset", YulSemantics.Expr.lit (YulSemantics.Literal.number 96)]]]),
    YulSemantics.Stmt.cond
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.or)
        [YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.shr)
           [YulSemantics.Expr.lit (YulSemantics.Literal.number 128),
            YulSemantics.Expr.builtin (YulSemantics.EVM.Op.mload) [YulSemantics.Expr.var "point"]],
         YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.shr)
           [YulSemantics.Expr.lit (YulSemantics.Literal.number 128),
            YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.mload)
              [YulSemantics.Expr.builtin
                 (YulSemantics.EVM.Op.add)
                 [YulSemantics.Expr.var "point", YulSemantics.Expr.lit (YulSemantics.Literal.number 64)]]]])
      [YulSemantics.Stmt.exprStmt (YulSemantics.Expr.builtin (YulSemantics.EVM.Op.invalid) [])],
    YulSemantics.Stmt.cond
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.iszero)
        [YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.and)
           [YulSemantics.Expr.call
              "fpValid"
              [YulSemantics.Expr.builtin (YulSemantics.EVM.Op.mload) [YulSemantics.Expr.var "point"],
               YulSemantics.Expr.builtin
                 (YulSemantics.EVM.Op.mload)
                 [YulSemantics.Expr.builtin
                    (YulSemantics.EVM.Op.add)
                    [YulSemantics.Expr.var "point", YulSemantics.Expr.lit (YulSemantics.Literal.number 32)]]],
            YulSemantics.Expr.call
              "fpValid"
              [YulSemantics.Expr.builtin
                 (YulSemantics.EVM.Op.mload)
                 [YulSemantics.Expr.builtin
                    (YulSemantics.EVM.Op.add)
                    [YulSemantics.Expr.var "point", YulSemantics.Expr.lit (YulSemantics.Literal.number 64)]],
               YulSemantics.Expr.builtin
                 (YulSemantics.EVM.Op.mload)
                 [YulSemantics.Expr.builtin
                    (YulSemantics.EVM.Op.add)
                    [YulSemantics.Expr.var "point", YulSemantics.Expr.lit (YulSemantics.Literal.number 96)]]]]])
      [YulSemantics.Stmt.exprStmt (YulSemantics.Expr.builtin (YulSemantics.EVM.Op.invalid) [])],
    YulSemantics.Stmt.cond
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.and)
        [YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.iszero)
           [YulSemantics.Expr.call "pointInfinity" [YulSemantics.Expr.var "point"]],
         YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.iszero)
           [YulSemantics.Expr.call
              "onCurve"
              [YulSemantics.Expr.builtin (YulSemantics.EVM.Op.mload) [YulSemantics.Expr.var "point"],
               YulSemantics.Expr.builtin
                 (YulSemantics.EVM.Op.mload)
                 [YulSemantics.Expr.builtin
                    (YulSemantics.EVM.Op.add)
                    [YulSemantics.Expr.var "point", YulSemantics.Expr.lit (YulSemantics.Literal.number 32)]],
               YulSemantics.Expr.builtin
                 (YulSemantics.EVM.Op.mload)
                 [YulSemantics.Expr.builtin
                    (YulSemantics.EVM.Op.add)
                    [YulSemantics.Expr.var "point", YulSemantics.Expr.lit (YulSemantics.Literal.number 64)]],
               YulSemantics.Expr.builtin
                 (YulSemantics.EVM.Op.mload)
                 [YulSemantics.Expr.builtin
                    (YulSemantics.EVM.Op.add)
                    [YulSemantics.Expr.var "point", YulSemantics.Expr.lit (YulSemantics.Literal.number 96)]]]]])
      [YulSemantics.Stmt.exprStmt (YulSemantics.Expr.builtin (YulSemantics.EVM.Op.invalid) [])],
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.call
        "scalarMul"
        [YulSemantics.Expr.lit
           (YulSemantics.Literal.number 52435875175126190479447740508185965837690552500527637822603658699938581184513),
         YulSemantics.Expr.var "point",
         YulSemantics.Expr.var "subgroupOut"]),
    YulSemantics.Stmt.cond
      (YulSemantics.Expr.builtin
        (YulSemantics.EVM.Op.iszero)
        [YulSemantics.Expr.call "pointInfinity" [YulSemantics.Expr.var "subgroupOut"]])
      [YulSemantics.Stmt.exprStmt (YulSemantics.Expr.builtin (YulSemantics.EVM.Op.invalid) [])],
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.call
        "scalarMul"
        [YulSemantics.Expr.builtin
           (YulSemantics.EVM.Op.calldataload)
           [YulSemantics.Expr.builtin
              (YulSemantics.EVM.Op.add)
              [YulSemantics.Expr.var "offset", YulSemantics.Expr.lit (YulSemantics.Literal.number 128)]],
         YulSemantics.Expr.var "point",
         YulSemantics.Expr.var "termOut"]),
    YulSemantics.Stmt.exprStmt
      (YulSemantics.Expr.call
        "pointAdd"
        [YulSemantics.Expr.var "acc", YulSemantics.Expr.var "acc", YulSemantics.Expr.var "termOut"])],
 YulSemantics.Stmt.exprStmt
   (YulSemantics.Expr.call
     "copyPoint"
     [YulSemantics.Expr.lit (YulSemantics.Literal.number 0), YulSemantics.Expr.var "acc"]),
 YulSemantics.Stmt.exprStmt
   (YulSemantics.Expr.builtin
     (YulSemantics.EVM.Op.ret)
     [YulSemantics.Expr.lit (YulSemantics.Literal.number 0), YulSemantics.Expr.lit (YulSemantics.Literal.number 128)])]

end Challenge.Bls12381G1Msm.Reference.Proofs.Compilation
