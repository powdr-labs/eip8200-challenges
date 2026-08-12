import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointInfinityRefinement

set_option warningAsError true

/-! Frozen declaration and prefix boundary for the G1MSM `pointAdd` helper. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM
open Challenge.Bls12381G1Msm.Reference.Proofs.Compilation

def pointAddBody : Block Op :=
  match referenceBackendBlock[9]? with
  | some (Stmt.funDef _ _ _ body) => body
  | _ => []

def pointAddStmt0 : Stmt Op := pointAddBody[0]!
def pointAddStmt1 : Stmt Op := pointAddBody[1]!
def pointAddStmt2 : Stmt Op := pointAddBody[2]!
def pointAddStmt3 : Stmt Op := pointAddBody[3]!
def pointAddStmt4 : Stmt Op := pointAddBody[4]!
def pointAddStmt5 : Stmt Op := pointAddBody[5]!
def pointAddAfterPrefix : Block Op := pointAddBody.drop 3

def pointAddLeftInfinityCondition : Expr Op :=
  match pointAddStmt3 with
  | .cond condition _ => condition
  | _ => .lit (.number 0)

def pointAddLeftInfinityBody : Block Op :=
  match pointAddStmt3 with
  | .cond _ body => body
  | _ => []

def pointAddLeftCopyStmt : Stmt Op := pointAddLeftInfinityBody[0]!

def pointAddLeftCopyBody : Block Op :=
  match pointAddLeftCopyStmt with
  | .block body => body
  | _ => []

def pointAddLeftCopyStmt0 : Stmt Op := pointAddLeftCopyBody[0]!
def pointAddLeftCopyStmt1 : Stmt Op := pointAddLeftCopyBody[1]!
def pointAddLeftCopyStmt2 : Stmt Op := pointAddLeftCopyBody[2]!
def pointAddLeftCopyStmt3 : Stmt Op := pointAddLeftCopyBody[3]!
def pointAddLeftCopyStmt4 : Stmt Op := pointAddLeftCopyBody[4]!
def pointAddLeftCopyStmt5 : Stmt Op := pointAddLeftCopyBody[5]!
def pointAddLeftCopyStmt6 : Stmt Op := pointAddLeftCopyBody[6]!

theorem pointAddLeftInfinityCondition_eq : pointAddLeftInfinityCondition =
    .call "\x0015" [.builtin .mload [.lit (.number 1568)]] := by
  rfl

theorem pointAddStmt3_eq : pointAddStmt3 =
    .cond pointAddLeftInfinityCondition pointAddLeftInfinityBody := by
  rfl

def pointAddRightInfinityCondition : Expr Op :=
  match pointAddStmt4 with
  | .cond condition _ => condition
  | _ => .lit (.number 0)

def pointAddRightInfinityBody : Block Op :=
  match pointAddStmt4 with
  | .cond _ body => body
  | _ => []

def pointAddRightCopyStmt : Stmt Op := pointAddRightInfinityBody[0]!

def pointAddRightCopyBody : Block Op :=
  match pointAddRightCopyStmt with
  | .block body => body
  | _ => []

def pointAddRightCopyStmt0 : Stmt Op := pointAddRightCopyBody[0]!
def pointAddRightCopyStmt1 : Stmt Op := pointAddRightCopyBody[1]!
def pointAddRightCopyStmt2 : Stmt Op := pointAddRightCopyBody[2]!
def pointAddRightCopyStmt3 : Stmt Op := pointAddRightCopyBody[3]!
def pointAddRightCopyStmt4 : Stmt Op := pointAddRightCopyBody[4]!
def pointAddRightCopyStmt5 : Stmt Op := pointAddRightCopyBody[5]!
def pointAddRightCopyStmt6 : Stmt Op := pointAddRightCopyBody[6]!

theorem pointAddRightInfinityCondition_eq : pointAddRightInfinityCondition =
    .call "\x0015" [.builtin .mload [.lit (.number 1600)]] := by
  rfl

theorem pointAddStmt4_eq : pointAddStmt4 =
    .cond pointAddRightInfinityCondition pointAddRightInfinityBody := by
  rfl

theorem pointAddRightInfinityBody_eq : pointAddRightInfinityBody =
    [pointAddRightCopyStmt, .leave] := by
  rfl

theorem pointAddRightCopyStmt_eq : pointAddRightCopyStmt =
    .block pointAddRightCopyBody := by
  rfl

theorem pointAddRightCopyBody_eq : pointAddRightCopyBody =
    [pointAddRightCopyStmt0, pointAddRightCopyStmt1, pointAddRightCopyStmt2,
      pointAddRightCopyStmt3, pointAddRightCopyStmt4, pointAddRightCopyStmt5,
      pointAddRightCopyStmt6] := by
  rfl

def pointAddXEqCondition : Expr Op :=
  match pointAddStmt5 with
  | .cond condition _ => condition
  | _ => .lit (.number 0)

def pointAddXEqBody : Block Op :=
  match pointAddStmt5 with
  | .cond _ body => body
  | _ => []

theorem pointAddStmt5_eq : pointAddStmt5 =
    .cond pointAddXEqCondition pointAddXEqBody := by
  rfl

theorem pointAddXEqCondition_eq : pointAddXEqCondition =
    .call "\x003"
      [.builtin .mload [.builtin .mload [.lit (.number 1568)]],
       .builtin .mload
        [.builtin .add
          [.builtin .mload [.lit (.number 1568)], .lit (.number 32)]],
       .builtin .mload [.builtin .mload [.lit (.number 1600)]],
       .builtin .mload
        [.builtin .add
          [.builtin .mload [.lit (.number 1600)], .lit (.number 32)]]] := by
  rfl

def pointAddXEqMainStmt : Stmt Op := pointAddXEqBody[0]!

def pointAddXEqMainBody : Block Op :=
  match pointAddXEqMainStmt with
  | .block body => body
  | _ => []

def pointAddXEqExceptionalStmt : Stmt Op := pointAddXEqMainBody[0]!

def pointAddXEqExceptionalBody : Block Op :=
  match pointAddXEqExceptionalStmt with
  | .block body => body
  | _ => []

def pointAddYSumStmt : Stmt Op := pointAddXEqExceptionalBody[0]!
def pointAddYZeroStmt : Stmt Op := pointAddXEqExceptionalBody[1]!
def pointAddDoubleXSqStmt : Stmt Op := pointAddXEqMainBody[1]!
def pointAddDoubleNum2Stmt : Stmt Op := pointAddXEqMainBody[2]!
def pointAddDoubleNum3Stmt : Stmt Op := pointAddXEqMainBody[3]!
def pointAddDoubleDenStmt : Stmt Op := pointAddXEqMainBody[4]!
def pointAddDoubleInvInitStmt : Stmt Op := pointAddXEqMainBody[5]!
def pointAddDoubleInvStmt : Stmt Op := pointAddXEqMainBody[6]!
def pointAddDoubleLambdaStmt : Stmt Op := pointAddXEqMainBody[7]!
def pointAddDoubleX3Stmt : Stmt Op := pointAddXEqMainBody[8]!
def pointAddDoubleXSubStmt : Stmt Op := pointAddXEqMainBody[9]!
def pointAddDoubleDeltaInitStmt : Stmt Op := pointAddXEqMainBody[10]!
def pointAddDoubleDeltaStmt : Stmt Op := pointAddXEqMainBody[11]!
def pointAddDoubleYMulStmt : Stmt Op := pointAddXEqMainBody[12]!
def pointAddDoubleYSubStmt : Stmt Op := pointAddXEqMainBody[13]!

def pointAddDoubleXSubBody : Block Op :=
  match pointAddDoubleXSubStmt with
  | .block body => body
  | _ => []

def pointAddDoubleXSubLeftStmt : Stmt Op := pointAddDoubleXSubBody[0]!

def pointAddDoubleXSubLeftBody : Block Op :=
  match pointAddDoubleXSubLeftStmt with
  | .block body => body
  | _ => []

def pointAddDoubleXSubRightTail : Block Op := pointAddDoubleXSubBody.drop 1

def pointAddDoubleXSubLeftRepairStmt : Stmt Op := pointAddDoubleXSubLeftBody[2]!
def pointAddDoubleXSubLeftOutHiStmt : Stmt Op := pointAddDoubleXSubLeftBody[3]!
def pointAddDoubleXSubLeftOutLoStmt : Stmt Op := pointAddDoubleXSubLeftBody[4]!

def pointAddDoubleInvBody : Block Op :=
  match pointAddDoubleInvStmt with
  | .block body => body
  | _ => []

def pointAddDoubleInvStmt0 : Stmt Op := pointAddDoubleInvBody[0]!
def pointAddDoubleInvStmt1 : Stmt Op := pointAddDoubleInvBody[1]!
def pointAddDoubleInvStmt2 : Stmt Op := pointAddDoubleInvBody[2]!
def pointAddDoubleInvStmt3 : Stmt Op := pointAddDoubleInvBody[3]!
def pointAddDoubleInvStmt4 : Stmt Op := pointAddDoubleInvBody[4]!
def pointAddDoubleInvStmt5 : Stmt Op := pointAddDoubleInvBody[5]!
def pointAddDoubleInvStmt6 : Stmt Op := pointAddDoubleInvBody[6]!
def pointAddDoubleInvStmt7 : Stmt Op := pointAddDoubleInvBody[7]!
def pointAddDoubleInvStmt8 : Stmt Op := pointAddDoubleInvBody[8]!
def pointAddDoubleInvStmt9 : Stmt Op := pointAddDoubleInvBody[9]!
def pointAddDoubleInvStmt10 : Stmt Op := pointAddDoubleInvBody[10]!
def pointAddDoubleInvStmt11 : Stmt Op := pointAddDoubleInvBody[11]!
def pointAddDoubleInvStmt12 : Stmt Op := pointAddDoubleInvBody[12]!
def pointAddDoubleInvStmt13 : Stmt Op := pointAddDoubleInvBody[13]!

theorem pointAddDoubleInvInitStmt_eq : pointAddDoubleInvInitStmt =
    .letDecl ["\x00118", "\x00119"] none := by rfl

theorem pointAddDoubleInvStmt_eq : pointAddDoubleInvStmt =
    .block pointAddDoubleInvBody := by rfl

theorem pointAddDoubleInvBody_eq : pointAddDoubleInvBody =
    [pointAddDoubleInvStmt0, pointAddDoubleInvStmt1,
      pointAddDoubleInvStmt2, pointAddDoubleInvStmt3,
      pointAddDoubleInvStmt4, pointAddDoubleInvStmt5,
      pointAddDoubleInvStmt6, pointAddDoubleInvStmt7,
      pointAddDoubleInvStmt8, pointAddDoubleInvStmt9,
      pointAddDoubleInvStmt10, pointAddDoubleInvStmt11,
      pointAddDoubleInvStmt12, pointAddDoubleInvStmt13] := by rfl

theorem hoist_pointAddDoubleInvBody :
    hoist Challenge.EvmProof.modexpExec.toDialect pointAddDoubleInvBody = [] := by
  rfl

theorem pointAddDoubleInvStmt9_eq : pointAddDoubleInvStmt9 =
    .cond
      (.builtin .iszero
        [.builtin .staticcall
          [.lit (.number 36576), .lit (.number 5), .lit (.number 1024),
            .lit (.number 240), .lit (.number 1280), .lit (.number 48)]])
      [.exprStmt (.builtin .invalid [])] := by rfl

def pointAddDoubleLambdaExpr : Expr Op :=
  match pointAddDoubleLambdaStmt with
  | .letDecl _ (some expr) => expr
  | _ => .lit (.number 0)

def pointAddDoubleLambdaArgs : List (Expr Op) :=
  match pointAddDoubleLambdaExpr with
  | .call _ args => args
  | _ => []

theorem pointAddDoubleLambdaStmt_eq : pointAddDoubleLambdaStmt =
    .letDecl ["\x00120", "\x00121"] (some pointAddDoubleLambdaExpr) := by
  rfl

theorem pointAddDoubleLambdaExpr_eq : pointAddDoubleLambdaExpr =
    .call "\x009" pointAddDoubleLambdaArgs := by
  rfl

theorem pointAddDoubleLambdaArgs_eq : pointAddDoubleLambdaArgs =
    [.var "\x00114", .var "\x00115", .var "\x00118", .var "\x00119"] := by
  rfl

def pointAddDoubleX3Expr : Expr Op :=
  match pointAddDoubleX3Stmt with
  | .letDecl _ (some expr) => expr
  | _ => .lit (.number 0)

def pointAddDoubleX3Args : List (Expr Op) :=
  match pointAddDoubleX3Expr with
  | .call _ args => args
  | _ => []

theorem pointAddDoubleX3Stmt_eq : pointAddDoubleX3Stmt =
    .letDecl ["\x00122", "\x00123"] (some pointAddDoubleX3Expr) := by
  rfl

theorem pointAddDoubleX3Expr_eq : pointAddDoubleX3Expr =
    .call "\x009" pointAddDoubleX3Args := by
  rfl

theorem pointAddDoubleX3Args_eq : pointAddDoubleX3Args =
    [.var "\x00120", .var "\x00121", .var "\x00120", .var "\x00121"] := by
  rfl

theorem pointAddDoubleXSubStmt_eq : pointAddDoubleXSubStmt =
    .block pointAddDoubleXSubBody := by
  rfl

theorem pointAddDoubleDeltaInitStmt_eq : pointAddDoubleDeltaInitStmt =
    .letDecl ["\x00124", "\x00125"] none := by rfl

def pointAddDoubleDeltaBody : Block Op :=
  match pointAddDoubleDeltaStmt with
  | .block body => body
  | _ => []

theorem pointAddDoubleDeltaStmt_eq : pointAddDoubleDeltaStmt =
    .block pointAddDoubleDeltaBody := by rfl

theorem pointAddDoubleXSubBody_eq : pointAddDoubleXSubBody =
    pointAddDoubleXSubLeftStmt :: pointAddDoubleXSubRightTail := by
  rfl

theorem pointAddDoubleXSubLeftStmt_eq : pointAddDoubleXSubLeftStmt =
    .block pointAddDoubleXSubLeftBody := by
  rfl

theorem pointAddDoubleXSubLeftBody_length :
    pointAddDoubleXSubLeftBody.length = 5 := by
  rfl

theorem pointAddDoubleXSubLeftRawPrefix_shape :
    pointAddDoubleXSubLeftBody.take 2 =
    [.letDecl ["fc0_28", "fc0_29"] none,
     .block
      [.letDecl ["fc0_30"]
        (some (.builtin .mload
          [.builtin .add
            [.builtin .mload [.lit (.number 1568)], .lit (.number 32)]])),
       .letDecl ["fc0_31"]
        (some (.builtin .mload
          [.builtin .mload [.lit (.number 1568)]])),
       .letDecl ["fc0_32"] (some (.var "\x00123")),
       .letDecl ["fc0_33"] (some (.var "\x00122")),
       .assign ["fc0_29"] (.builtin .sub [.var "fc0_32", .var "fc0_30"]),
       .assign ["fc0_28"]
        (.builtin .sub
          [.builtin .sub [.var "fc0_33", .var "fc0_31"],
           .builtin .gt [.var "fc0_30", .var "fc0_32"]])]] := by
  rfl

theorem pointAddDoubleXSubLeftTail_shape :
    pointAddDoubleXSubLeftBody.drop 2 =
    [.cond
      (.builtin .gt
        [.var "fc0_28",
         .lit (.number 34565483545414906068789196026815425751)])
      [.letDecl ["\x0051"]
        (some (.builtin .add
          [.var "fc0_29",
           .lit (.number
            45442060874369865957053122457065728162598490762543039060009208264153100167851)])),
       .assign ["fc0_28"]
        (.builtin .add
          [.var "fc0_28",
           .builtin .add
            [.lit (.number 34565483545414906068789196026815425751),
             .builtin .lt [.var "\x0051", .var "fc0_29"]]]),
       .assign ["fc0_29"] (.var "\x0051")],
     .assign ["\x00122"] (.var "fc0_28"),
     .assign ["\x00123"] (.var "fc0_29")] := by
  rfl

theorem pointAddDoubleXSubLeftRepairStmt_eq :
    pointAddDoubleXSubLeftRepairStmt =
    .cond
      (.builtin .gt
        [.var "fc0_28",
         .lit (.number 34565483545414906068789196026815425751)])
      [.letDecl ["\x0051"]
        (some (.builtin .add
          [.var "fc0_29",
           .lit (.number
            45442060874369865957053122457065728162598490762543039060009208264153100167851)])),
       .assign ["fc0_28"]
        (.builtin .add
          [.var "fc0_28",
           .builtin .add
            [.lit (.number 34565483545414906068789196026815425751),
             .builtin .lt [.var "\x0051", .var "fc0_29"]]]),
       .assign ["fc0_29"] (.var "\x0051")] := by
  rfl

theorem pointAddDoubleXSubLeftOutHiStmt_eq :
    pointAddDoubleXSubLeftOutHiStmt =
      .assign ["\x00122"] (.var "fc0_28") := by
  rfl

theorem pointAddDoubleXSubLeftOutLoStmt_eq :
    pointAddDoubleXSubLeftOutLoStmt =
      .assign ["\x00123"] (.var "fc0_29") := by
  rfl

theorem pointAddDoubleXSubRightTail_length :
    pointAddDoubleXSubRightTail.length = 5 := by
  rfl

theorem hoist_pointAddDoubleXSubLeftBody :
    hoist Challenge.EvmProof.modexpExec.toDialect pointAddDoubleXSubLeftBody = [] := by
  rfl

theorem hoist_pointAddDoubleXSubBody :
    hoist Challenge.EvmProof.modexpExec.toDialect pointAddDoubleXSubBody = [] := by
  rfl

def pointAddDoubleXSqExpr : Expr Op :=
  match pointAddDoubleXSqStmt with
  | .letDecl _ (some expr) => expr
  | _ => .lit (.number 0)

def pointAddDoubleXSqArgs : List (Expr Op) :=
  match pointAddDoubleXSqExpr with
  | .call _ args => args
  | _ => []

theorem pointAddDoubleXSqStmt_eq : pointAddDoubleXSqStmt =
    .letDecl ["\x00112", "\x00113"] (some pointAddDoubleXSqExpr) := by
  rfl

theorem pointAddDoubleXSqExpr_eq : pointAddDoubleXSqExpr =
    .call "\x009" pointAddDoubleXSqArgs := by
  rfl

theorem pointAddDoubleXSqArgs_eq : pointAddDoubleXSqArgs =
    [.builtin .mload [.builtin .mload [.lit (.number 1568)]],
     .builtin .mload
      [.builtin .add
        [.builtin .mload [.lit (.number 1568)], .lit (.number 32)]],
     .builtin .mload [.builtin .mload [.lit (.number 1568)]],
     .builtin .mload
      [.builtin .add
        [.builtin .mload [.lit (.number 1568)], .lit (.number 32)]]] := by
  rfl

def pointAddDoubleNum2Expr : Expr Op :=
  match pointAddDoubleNum2Stmt with
  | .letDecl _ (some expr) => expr
  | _ => .lit (.number 0)

theorem pointAddDoubleNum2Stmt_eq : pointAddDoubleNum2Stmt =
    .letDecl ["\x00114", "\x00115"] (some pointAddDoubleNum2Expr) := by
  rfl

theorem pointAddDoubleNum2Expr_eq : pointAddDoubleNum2Expr =
    .call "\x004"
      [.var "\x00112", .var "\x00113", .var "\x00112", .var "\x00113"] := by
  rfl

def pointAddDoubleNum3Expr : Expr Op :=
  match pointAddDoubleNum3Stmt with
  | .assign _ expr => expr
  | _ => .lit (.number 0)

theorem pointAddDoubleNum3Stmt_eq : pointAddDoubleNum3Stmt =
    .assign ["\x00114", "\x00115"] pointAddDoubleNum3Expr := by
  rfl

theorem pointAddDoubleNum3Expr_eq : pointAddDoubleNum3Expr =
    .call "\x004"
      [.var "\x00114", .var "\x00115", .var "\x00112", .var "\x00113"] := by
  rfl

def pointAddDoubleDenExpr : Expr Op :=
  match pointAddDoubleDenStmt with
  | .letDecl _ (some expr) => expr
  | _ => .lit (.number 0)

def pointAddDoubleDenArgs : List (Expr Op) :=
  match pointAddDoubleDenExpr with
  | .call _ args => args
  | _ => []

theorem pointAddDoubleDenStmt_eq : pointAddDoubleDenStmt =
    .letDecl ["\x00116", "\x00117"] (some pointAddDoubleDenExpr) := by
  rfl

theorem pointAddDoubleDenExpr_eq : pointAddDoubleDenExpr =
    .call "\x004" pointAddDoubleDenArgs := by
  rfl

theorem pointAddDoubleDenArgs_eq : pointAddDoubleDenArgs =
    [.builtin .mload
      [.builtin .add
        [.builtin .mload [.lit (.number 1568)], .lit (.number 64)]],
     .builtin .mload
      [.builtin .add
        [.builtin .mload [.lit (.number 1568)], .lit (.number 96)]],
     .builtin .mload
      [.builtin .add
        [.builtin .mload [.lit (.number 1568)], .lit (.number 64)]],
     .builtin .mload
      [.builtin .add
        [.builtin .mload [.lit (.number 1568)], .lit (.number 96)]]] := by
  rfl

def pointAddYSumExpr : Expr Op :=
  match pointAddYSumStmt with
  | .letDecl _ (some expr) => expr
  | _ => .lit (.number 0)

def pointAddYSumArgs : List (Expr Op) :=
  match pointAddYSumExpr with
  | .call _ args => args
  | _ => []

theorem pointAddXEqBody_eq : pointAddXEqBody =
    [pointAddXEqMainStmt, .leave] := by
  rfl

theorem pointAddXEqMainStmt_eq : pointAddXEqMainStmt =
    .block pointAddXEqMainBody := by
  rfl

theorem pointAddXEqExceptionalStmt_eq : pointAddXEqExceptionalStmt =
    .block pointAddXEqExceptionalBody := by
  rfl

theorem pointAddXEqExceptionalBody_eq : pointAddXEqExceptionalBody =
    [pointAddYSumStmt, pointAddYZeroStmt] := by
  rfl

theorem pointAddYSumStmt_eq : pointAddYSumStmt =
    .letDecl ["\x00110", "\x00111"]
      (some pointAddYSumExpr) := by
  rfl

theorem pointAddYSumExpr_eq : pointAddYSumExpr =
    .call "\x004" pointAddYSumArgs := by
  rfl

theorem pointAddYSumArgs_eq : pointAddYSumArgs =
    [.builtin .mload
          [.builtin .add
            [.builtin .mload [.lit (.number 1568)], .lit (.number 64)]],
         .builtin .mload
          [.builtin .add
            [.builtin .mload [.lit (.number 1568)], .lit (.number 96)]],
         .builtin .mload
          [.builtin .add
            [.builtin .mload [.lit (.number 1600)], .lit (.number 64)]],
         .builtin .mload
          [.builtin .add
            [.builtin .mload [.lit (.number 1600)], .lit (.number 96)]]] := by
  rfl

def pointAddYZeroCondition : Expr Op :=
  match pointAddYZeroStmt with
  | .cond condition _ => condition
  | _ => .lit (.number 0)

def pointAddYZeroBody : Block Op :=
  match pointAddYZeroStmt with
  | .cond _ body => body
  | _ => []

theorem pointAddYZeroStmt_eq : pointAddYZeroStmt =
    .cond pointAddYZeroCondition pointAddYZeroBody := by
  rfl

theorem pointAddYZeroCondition_eq : pointAddYZeroCondition =
    .call "\x002" [.var "\x00110", .var "\x00111"] := by
  rfl

theorem pointAddLeftInfinityBody_eq : pointAddLeftInfinityBody =
    [pointAddLeftCopyStmt, .leave] := by
  rfl

theorem pointAddLeftCopyStmt_eq : pointAddLeftCopyStmt =
    .block pointAddLeftCopyBody := by
  rfl

theorem pointAddLeftCopyBody_eq : pointAddLeftCopyBody =
    [pointAddLeftCopyStmt0, pointAddLeftCopyStmt1, pointAddLeftCopyStmt2,
      pointAddLeftCopyStmt3, pointAddLeftCopyStmt4, pointAddLeftCopyStmt5,
      pointAddLeftCopyStmt6] := by
  rfl

theorem pointAddBody_length : pointAddBody.length = 27 := by
  rfl

theorem pointAddBody_eq : pointAddBody =
    [pointAddStmt0, pointAddStmt1, pointAddStmt2] ++ pointAddAfterPrefix := by
  rfl

theorem hoist_pointAddBody :
    hoist Challenge.EvmProof.modexpExec.toDialect pointAddBody = [] := by
  rfl

def pointAddBodyFuns : FunEnv Challenge.EvmProof.modexpExec.toDialect :=
  [] :: sourceFuns

def pointAddDecl : FDecl Challenge.EvmProof.modexpExec.toDialect :=
  { params := ["\x00107", "\x00108", "\x00109"]
    rets := []
    body := pointAddBody }

theorem lookup_pointAdd : lookupFun sourceFuns "\x0016" =
    some (pointAddDecl, sourceFuns) := by
  rfl

def pointAddInitialEnv (out left right : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  [("\x00107", out), ("\x00108", left), ("\x00109", right)]

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
