import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddXEq

set_option warningAsError true

/-! Frozen AST and value-only context for the second point-double x subtraction.

This module deliberately has no dependency on the proof of the first subtraction.
The generic proof chain consumes only the normalized environment/state/value fields
of `PointAddDoubleXSubRightContext`; the concrete bridge is deferred until both
subtractions have been proved. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

structure PointAddDoubleXSubRightContext where
  env : VEnv Challenge.EvmProof.modexpExec.toDialect
  state : EvmState
  x3Hi : U256
  x3Lo : U256
  env_hi : VEnv.get env "\x00122" = some x3Hi
  env_lo : VEnv.get env "\x00123" = some x3Lo

def pointAddDoubleXSubRightRawDeclStmt : Stmt Op :=
  pointAddDoubleXSubRightTail[0]!

def pointAddDoubleXSubRightRawBlockStmt : Stmt Op :=
  pointAddDoubleXSubRightTail[1]!

def pointAddDoubleXSubRightRepairStmt : Stmt Op :=
  pointAddDoubleXSubRightTail[2]!

def pointAddDoubleXSubRightOutHiStmt : Stmt Op :=
  pointAddDoubleXSubRightTail[3]!

def pointAddDoubleXSubRightOutLoStmt : Stmt Op :=
  pointAddDoubleXSubRightTail[4]!

def pointAddDoubleXSubRightRawBody : Block Op :=
  match pointAddDoubleXSubRightRawBlockStmt with
  | .block body => body
  | _ => []

def pointAddDoubleXSubRightRawStmt0 : Stmt Op := pointAddDoubleXSubRightRawBody[0]!
def pointAddDoubleXSubRightRawStmt1 : Stmt Op := pointAddDoubleXSubRightRawBody[1]!
def pointAddDoubleXSubRightRawStmt2 : Stmt Op := pointAddDoubleXSubRightRawBody[2]!
def pointAddDoubleXSubRightRawStmt3 : Stmt Op := pointAddDoubleXSubRightRawBody[3]!
def pointAddDoubleXSubRightRawStmt4 : Stmt Op := pointAddDoubleXSubRightRawBody[4]!
def pointAddDoubleXSubRightRawStmt5 : Stmt Op := pointAddDoubleXSubRightRawBody[5]!

theorem pointAddDoubleXSubRightRawPrefix_shape :
    pointAddDoubleXSubRightTail.take 2 =
      [pointAddDoubleXSubRightRawDeclStmt,
       pointAddDoubleXSubRightRawBlockStmt] := by
  rfl

theorem pointAddDoubleXSubRightRawDeclStmt_eq :
    pointAddDoubleXSubRightRawDeclStmt =
      .letDecl ["fc0_35", "fc0_36"] none := by rfl

theorem pointAddDoubleXSubRightRawBlockStmt_eq :
    pointAddDoubleXSubRightRawBlockStmt =
      .block pointAddDoubleXSubRightRawBody := by rfl

theorem pointAddDoubleXSubRightRawBody_eq :
    pointAddDoubleXSubRightRawBody =
      [pointAddDoubleXSubRightRawStmt0, pointAddDoubleXSubRightRawStmt1,
       pointAddDoubleXSubRightRawStmt2, pointAddDoubleXSubRightRawStmt3,
       pointAddDoubleXSubRightRawStmt4, pointAddDoubleXSubRightRawStmt5] := by rfl

theorem pointAddDoubleXSubRightRawStmt0_eq :
    pointAddDoubleXSubRightRawStmt0 =
      .letDecl ["fc0_37"]
        (some (.builtin .mload
          [.builtin .add
            [.builtin .mload [.lit (.number 1600)], .lit (.number 32)]])) := by rfl

theorem pointAddDoubleXSubRightRawStmt1_eq :
    pointAddDoubleXSubRightRawStmt1 =
      .letDecl ["fc0_38"]
        (some (.builtin .mload
          [.builtin .mload [.lit (.number 1600)]])) := by rfl

theorem pointAddDoubleXSubRightRawStmt2_eq :
    pointAddDoubleXSubRightRawStmt2 =
      .letDecl ["fc0_39"] (some (.var "\x00123")) := by rfl

theorem pointAddDoubleXSubRightRawStmt3_eq :
    pointAddDoubleXSubRightRawStmt3 =
      .letDecl ["fc0_40"] (some (.var "\x00122")) := by rfl

theorem pointAddDoubleXSubRightRawStmt4_eq :
    pointAddDoubleXSubRightRawStmt4 =
      .assign ["fc0_36"]
        (.builtin .sub [.var "fc0_39", .var "fc0_37"]) := by rfl

theorem pointAddDoubleXSubRightRawStmt5_eq :
    pointAddDoubleXSubRightRawStmt5 =
      .assign ["fc0_35"]
        (.builtin .sub
          [.builtin .sub [.var "fc0_40", .var "fc0_38"],
           .builtin .gt [.var "fc0_37", .var "fc0_39"]]) := by rfl

theorem pointAddDoubleXSubRightRepairStmt_eq :
    pointAddDoubleXSubRightRepairStmt =
      .cond
        (.builtin .gt
          [.var "fc0_35",
           .lit (.number 34565483545414906068789196026815425751)])
        [.letDecl ["\x0051"]
          (some (.builtin .add
            [.var "fc0_36",
             .lit (.number
              45442060874369865957053122457065728162598490762543039060009208264153100167851)])),
         .assign ["fc0_35"]
          (.builtin .add
            [.var "fc0_35",
             .builtin .add
              [.lit (.number 34565483545414906068789196026815425751),
               .builtin .lt [.var "\x0051", .var "fc0_36"]]]),
         .assign ["fc0_36"] (.var "\x0051")] := by rfl

theorem pointAddDoubleXSubRightOutHiStmt_eq :
    pointAddDoubleXSubRightOutHiStmt =
      .assign ["\x00122"] (.var "fc0_35") := by rfl

theorem pointAddDoubleXSubRightOutLoStmt_eq :
    pointAddDoubleXSubRightOutLoStmt =
      .assign ["\x00123"] (.var "fc0_36") := by rfl

theorem hoist_pointAddDoubleXSubRightRawBody :
    hoist Challenge.EvmProof.modexpExec.toDialect
      pointAddDoubleXSubRightRawBody = [] := by rfl

def pointAddDoubleXSubRightPtr (ctx : PointAddDoubleXSubRightContext) : U256 :=
  loadWord ctx.state.memory 1600

def pointAddDoubleXSubRightHi (ctx : PointAddDoubleXSubRightContext) : U256 :=
  loadWord ctx.state.memory (pointAddDoubleXSubRightPtr ctx).toNat

def pointAddDoubleXSubRightLo (ctx : PointAddDoubleXSubRightContext) : U256 :=
  loadWord ctx.state.memory (pointAddDoubleXSubRightPtr ctx + 32).toNat

def pointAddDoubleXSubRightRawLo (ctx : PointAddDoubleXSubRightContext) : U256 :=
  ctx.x3Lo - pointAddDoubleXSubRightLo ctx

def pointAddDoubleXSubRightRawHi (ctx : PointAddDoubleXSubRightContext) : U256 :=
  ctx.x3Hi - pointAddDoubleXSubRightHi ctx -
    b2w (BitVec.ult ctx.x3Lo (pointAddDoubleXSubRightLo ctx))

def pointAddDoubleXSubRightRaw (ctx : PointAddDoubleXSubRightContext) :
    U256 × U256 :=
  (pointAddDoubleXSubRightRawHi ctx, pointAddDoubleXSubRightRawLo ctx)

def pointAddDoubleXSubRightState1 (ctx : PointAddDoubleXSubRightContext) :=
  touchMemory ctx.state 1600 32

def pointAddDoubleXSubRightState2 (ctx : PointAddDoubleXSubRightContext) :=
  touchMemory (pointAddDoubleXSubRightState1 ctx)
    (pointAddDoubleXSubRightPtr ctx + 32).toNat 32

def pointAddDoubleXSubRightState3 (ctx : PointAddDoubleXSubRightContext) :=
  touchMemory (pointAddDoubleXSubRightState2 ctx) 1600 32

def pointAddDoubleXSubRightRawState (ctx : PointAddDoubleXSubRightContext) :=
  touchMemory (pointAddDoubleXSubRightState3 ctx)
    (pointAddDoubleXSubRightPtr ctx).toNat 32

def pointAddDoubleXSubRightRawEnv (ctx : PointAddDoubleXSubRightContext) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  [("fc0_35", (pointAddDoubleXSubRightRaw ctx).1),
   ("fc0_36", (pointAddDoubleXSubRightRaw ctx).2)] ++ ctx.env

theorem pointAddDoubleXSubRightRawEnv_hi (ctx : PointAddDoubleXSubRightContext) :
    VEnv.get (pointAddDoubleXSubRightRawEnv ctx) "fc0_35" =
      some (pointAddDoubleXSubRightRaw ctx).1 := by rfl

theorem pointAddDoubleXSubRightRawEnv_lo (ctx : PointAddDoubleXSubRightContext) :
    VEnv.get (pointAddDoubleXSubRightRawEnv ctx) "fc0_36" =
      some (pointAddDoubleXSubRightRaw ctx).2 := by rfl

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
