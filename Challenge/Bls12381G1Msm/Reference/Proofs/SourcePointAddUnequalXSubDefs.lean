import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalX3

set_option warningAsError true

/-! Frozen subtraction boundaries for the unequal-point x-coordinate. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def pointAddUnequalXSubBody : Block Op :=
  match pointAddUnequalXSubStmt with
  | .block body => body
  | _ => []

def pointAddUnequalXSubLeftStmt : Stmt Op := pointAddUnequalXSubBody[0]!

def pointAddUnequalXSubLeftBody : Block Op :=
  match pointAddUnequalXSubLeftStmt with
  | .block body => body
  | _ => []

def pointAddUnequalXSubRightTail : Block Op :=
  pointAddUnequalXSubBody.drop 1

def pointAddUnequalXSubLeftRepairStmt : Stmt Op :=
  pointAddUnequalXSubLeftBody[2]!

def pointAddUnequalXSubLeftOutHiStmt : Stmt Op :=
  pointAddUnequalXSubLeftBody[3]!

def pointAddUnequalXSubLeftOutLoStmt : Stmt Op :=
  pointAddUnequalXSubLeftBody[4]!

theorem pointAddUnequalXSubStmt_eq : pointAddUnequalXSubStmt =
    .block pointAddUnequalXSubBody := by
  rfl

theorem pointAddUnequalXSubBody_eq : pointAddUnequalXSubBody =
    pointAddUnequalXSubLeftStmt :: pointAddUnequalXSubRightTail := by
  rfl

theorem pointAddUnequalXSubLeftStmt_eq : pointAddUnequalXSubLeftStmt =
    .block pointAddUnequalXSubLeftBody := by
  rfl

theorem pointAddUnequalXSubLeftBody_length :
    pointAddUnequalXSubLeftBody.length = 5 := by
  rfl

theorem pointAddUnequalXSubLeftRawPrefix_shape :
    pointAddUnequalXSubLeftBody.take 2 =
    [.letDecl ["fc0_81", "fc0_82"] none,
     .block
      [.letDecl ["fc0_83"]
        (some (.builtin .mload
          [.builtin .add
            [.builtin .mload [.lit (.number 1568)], .lit (.number 32)]])),
       .letDecl ["fc0_84"]
        (some (.builtin .mload
          [.builtin .mload [.lit (.number 1568)]])),
       .letDecl ["fc0_85"] (some (.var "\x00137")),
       .letDecl ["fc0_86"] (some (.var "\x00136")),
       .assign ["fc0_82"] (.builtin .sub [.var "fc0_85", .var "fc0_83"]),
       .assign ["fc0_81"]
        (.builtin .sub
          [.builtin .sub [.var "fc0_86", .var "fc0_84"],
           .builtin .gt [.var "fc0_83", .var "fc0_85"]])]] := by
  rfl

theorem pointAddUnequalXSubLeftTail_shape :
    pointAddUnequalXSubLeftBody.drop 2 =
    [.cond
      (.builtin .gt
        [.var "fc0_81",
         .lit (.number 34565483545414906068789196026815425751)])
      [.letDecl ["\x0051"]
        (some (.builtin .add
          [.var "fc0_82",
           .lit (.number
            45442060874369865957053122457065728162598490762543039060009208264153100167851)])),
       .assign ["fc0_81"]
        (.builtin .add
          [.var "fc0_81",
           .builtin .add
            [.lit (.number 34565483545414906068789196026815425751),
             .builtin .lt [.var "\x0051", .var "fc0_82"]]]),
       .assign ["fc0_82"] (.var "\x0051")],
     .assign ["\x00136"] (.var "fc0_81"),
     .assign ["\x00137"] (.var "fc0_82")] := by
  rfl

theorem pointAddUnequalXSubLeftRepairStmt_eq :
    pointAddUnequalXSubLeftRepairStmt =
    .cond
      (.builtin .gt
        [.var "fc0_81",
         .lit (.number 34565483545414906068789196026815425751)])
      [.letDecl ["\x0051"]
        (some (.builtin .add
          [.var "fc0_82",
           .lit (.number
            45442060874369865957053122457065728162598490762543039060009208264153100167851)])),
       .assign ["fc0_81"]
        (.builtin .add
          [.var "fc0_81",
           .builtin .add
            [.lit (.number 34565483545414906068789196026815425751),
             .builtin .lt [.var "\x0051", .var "fc0_82"]]]),
       .assign ["fc0_82"] (.var "\x0051")] := by
  rfl

theorem pointAddUnequalXSubLeftOutHiStmt_eq :
    pointAddUnequalXSubLeftOutHiStmt =
      .assign ["\x00136"] (.var "fc0_81") := by
  rfl

theorem pointAddUnequalXSubLeftOutLoStmt_eq :
    pointAddUnequalXSubLeftOutLoStmt =
      .assign ["\x00137"] (.var "fc0_82") := by
  rfl

theorem pointAddUnequalXSubRightTail_length :
    pointAddUnequalXSubRightTail.length = 5 := by
  rfl

theorem hoist_pointAddUnequalXSubLeftBody :
    hoist Challenge.EvmProof.modexpExec.toDialect
      pointAddUnequalXSubLeftBody = [] := by
  rfl

theorem hoist_pointAddUnequalXSubBody :
    hoist Challenge.EvmProof.modexpExec.toDialect
      pointAddUnequalXSubBody = [] := by
  rfl

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
