import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalXSubDefs

set_option warningAsError true

/-! Frozen AST and value-only context for the second unequal-point x subtraction.

This module deliberately has no dependency on the proof of the first subtraction.
The generic proof chain consumes only the normalized environment/state/value fields
of `PointAddUnequalXSubRightContext`; the concrete bridge is deferred until both
subtractions have been proved. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

structure PointAddUnequalXSubRightContext where
  env : VEnv Challenge.EvmProof.modexpExec.toDialect
  state : EvmState
  x3Hi : U256
  x3Lo : U256
  env_hi : VEnv.get env "\x00136" = some x3Hi
  env_lo : VEnv.get env "\x00137" = some x3Lo

def makePointAddUnequalXSubRightContext
    (env : VEnv Challenge.EvmProof.modexpExec.toDialect) (state : EvmState)
    (x3Hi x3Lo : U256) (env_hi : VEnv.get env "\x00136" = some x3Hi)
    (env_lo : VEnv.get env "\x00137" = some x3Lo) :
    PointAddUnequalXSubRightContext where
  env := env
  state := state
  x3Hi := x3Hi
  x3Lo := x3Lo
  env_hi := env_hi
  env_lo := env_lo

@[simp] theorem makePointAddUnequalXSubRightContext_x3Hi
    (env : VEnv Challenge.EvmProof.modexpExec.toDialect) (state : EvmState)
    (x3Hi x3Lo : U256) (env_hi : VEnv.get env "\x00136" = some x3Hi)
    (env_lo : VEnv.get env "\x00137" = some x3Lo) :
    (makePointAddUnequalXSubRightContext env state x3Hi x3Lo env_hi env_lo).x3Hi =
      x3Hi := by
  rfl

@[simp] theorem makePointAddUnequalXSubRightContext_x3Lo
    (env : VEnv Challenge.EvmProof.modexpExec.toDialect) (state : EvmState)
    (x3Hi x3Lo : U256) (env_hi : VEnv.get env "\x00136" = some x3Hi)
    (env_lo : VEnv.get env "\x00137" = some x3Lo) :
    (makePointAddUnequalXSubRightContext env state x3Hi x3Lo env_hi env_lo).x3Lo =
      x3Lo := by
  rfl

def pointAddUnequalXSubRightRawDeclStmt : Stmt Op :=
  pointAddUnequalXSubRightTail[0]!

def pointAddUnequalXSubRightRawBlockStmt : Stmt Op :=
  pointAddUnequalXSubRightTail[1]!

def pointAddUnequalXSubRightRepairStmt : Stmt Op :=
  pointAddUnequalXSubRightTail[2]!

def pointAddUnequalXSubRightOutHiStmt : Stmt Op :=
  pointAddUnequalXSubRightTail[3]!

def pointAddUnequalXSubRightOutLoStmt : Stmt Op :=
  pointAddUnequalXSubRightTail[4]!

def pointAddUnequalXSubRightRawBody : Block Op :=
  match pointAddUnequalXSubRightRawBlockStmt with
  | .block body => body
  | _ => []

def pointAddUnequalXSubRightRawStmt0 : Stmt Op := pointAddUnequalXSubRightRawBody[0]!
def pointAddUnequalXSubRightRawStmt1 : Stmt Op := pointAddUnequalXSubRightRawBody[1]!
def pointAddUnequalXSubRightRawStmt2 : Stmt Op := pointAddUnequalXSubRightRawBody[2]!
def pointAddUnequalXSubRightRawStmt3 : Stmt Op := pointAddUnequalXSubRightRawBody[3]!
def pointAddUnequalXSubRightRawStmt4 : Stmt Op := pointAddUnequalXSubRightRawBody[4]!
def pointAddUnequalXSubRightRawStmt5 : Stmt Op := pointAddUnequalXSubRightRawBody[5]!

theorem pointAddUnequalXSubRightRawPrefix_shape :
    pointAddUnequalXSubRightTail.take 2 =
      [pointAddUnequalXSubRightRawDeclStmt,
       pointAddUnequalXSubRightRawBlockStmt] := by
  rfl

theorem pointAddUnequalXSubRightRawDeclStmt_eq :
    pointAddUnequalXSubRightRawDeclStmt =
      .letDecl ["fc0_88", "fc0_89"] none := by rfl

theorem pointAddUnequalXSubRightRawBlockStmt_eq :
    pointAddUnequalXSubRightRawBlockStmt =
      .block pointAddUnequalXSubRightRawBody := by rfl

theorem pointAddUnequalXSubRightRawBody_eq :
    pointAddUnequalXSubRightRawBody =
      [pointAddUnequalXSubRightRawStmt0, pointAddUnequalXSubRightRawStmt1,
       pointAddUnequalXSubRightRawStmt2, pointAddUnequalXSubRightRawStmt3,
       pointAddUnequalXSubRightRawStmt4, pointAddUnequalXSubRightRawStmt5] := by rfl

theorem pointAddUnequalXSubRightRawStmt0_eq :
    pointAddUnequalXSubRightRawStmt0 =
      .letDecl ["fc0_90"]
        (some (.builtin .mload
          [.builtin .add
            [.builtin .mload [.lit (.number 1600)], .lit (.number 32)]])) := by rfl

theorem pointAddUnequalXSubRightRawStmt1_eq :
    pointAddUnequalXSubRightRawStmt1 =
      .letDecl ["fc0_91"]
        (some (.builtin .mload
          [.builtin .mload [.lit (.number 1600)]])) := by rfl

theorem pointAddUnequalXSubRightRawStmt2_eq :
    pointAddUnequalXSubRightRawStmt2 =
      .letDecl ["fc0_92"] (some (.var "\x00137")) := by rfl

theorem pointAddUnequalXSubRightRawStmt3_eq :
    pointAddUnequalXSubRightRawStmt3 =
      .letDecl ["fc0_93"] (some (.var "\x00136")) := by rfl

theorem pointAddUnequalXSubRightRawStmt4_eq :
    pointAddUnequalXSubRightRawStmt4 =
      .assign ["fc0_89"]
        (.builtin .sub [.var "fc0_92", .var "fc0_90"]) := by rfl

theorem pointAddUnequalXSubRightRawStmt5_eq :
    pointAddUnequalXSubRightRawStmt5 =
      .assign ["fc0_88"]
        (.builtin .sub
          [.builtin .sub [.var "fc0_93", .var "fc0_91"],
           .builtin .gt [.var "fc0_90", .var "fc0_92"]]) := by rfl

theorem pointAddUnequalXSubRightRepairStmt_eq :
    pointAddUnequalXSubRightRepairStmt =
      .cond
        (.builtin .gt
          [.var "fc0_88",
           .lit (.number 34565483545414906068789196026815425751)])
        [.letDecl ["\x0051"]
          (some (.builtin .add
            [.var "fc0_89",
             .lit (.number
              45442060874369865957053122457065728162598490762543039060009208264153100167851)])),
         .assign ["fc0_88"]
          (.builtin .add
            [.var "fc0_88",
             .builtin .add
              [.lit (.number 34565483545414906068789196026815425751),
               .builtin .lt [.var "\x0051", .var "fc0_89"]]]),
         .assign ["fc0_89"] (.var "\x0051")] := by rfl

theorem pointAddUnequalXSubRightOutHiStmt_eq :
    pointAddUnequalXSubRightOutHiStmt =
      .assign ["\x00136"] (.var "fc0_88") := by rfl

theorem pointAddUnequalXSubRightOutLoStmt_eq :
    pointAddUnequalXSubRightOutLoStmt =
      .assign ["\x00137"] (.var "fc0_89") := by rfl

theorem hoist_pointAddUnequalXSubRightRawBody :
    hoist Challenge.EvmProof.modexpExec.toDialect
      pointAddUnequalXSubRightRawBody = [] := by rfl

def pointAddUnequalXSubRightPtr (ctx : PointAddUnequalXSubRightContext) : U256 :=
  loadWord ctx.state.memory 1600

def pointAddUnequalXSubRightHi (ctx : PointAddUnequalXSubRightContext) : U256 :=
  loadWord ctx.state.memory (pointAddUnequalXSubRightPtr ctx).toNat

def pointAddUnequalXSubRightLo (ctx : PointAddUnequalXSubRightContext) : U256 :=
  loadWord ctx.state.memory (pointAddUnequalXSubRightPtr ctx + 32).toNat

def pointAddUnequalXSubRightRawLo (ctx : PointAddUnequalXSubRightContext) : U256 :=
  ctx.x3Lo - pointAddUnequalXSubRightLo ctx

def pointAddUnequalXSubRightRawHi (ctx : PointAddUnequalXSubRightContext) : U256 :=
  ctx.x3Hi - pointAddUnequalXSubRightHi ctx -
    b2w (BitVec.ult ctx.x3Lo (pointAddUnequalXSubRightLo ctx))

def pointAddUnequalXSubRightRaw (ctx : PointAddUnequalXSubRightContext) :
    U256 × U256 :=
  (pointAddUnequalXSubRightRawHi ctx, pointAddUnequalXSubRightRawLo ctx)

def pointAddUnequalXSubRightState1 (ctx : PointAddUnequalXSubRightContext) :=
  touchMemory ctx.state 1600 32

def pointAddUnequalXSubRightState2 (ctx : PointAddUnequalXSubRightContext) :=
  touchMemory (pointAddUnequalXSubRightState1 ctx)
    (pointAddUnequalXSubRightPtr ctx + 32).toNat 32

def pointAddUnequalXSubRightState3 (ctx : PointAddUnequalXSubRightContext) :=
  touchMemory (pointAddUnequalXSubRightState2 ctx) 1600 32

def pointAddUnequalXSubRightRawState (ctx : PointAddUnequalXSubRightContext) :=
  touchMemory (pointAddUnequalXSubRightState3 ctx)
    (pointAddUnequalXSubRightPtr ctx).toNat 32

def pointAddUnequalXSubRightRawEnv (ctx : PointAddUnequalXSubRightContext) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  [("fc0_88", (pointAddUnequalXSubRightRaw ctx).1),
   ("fc0_89", (pointAddUnequalXSubRightRaw ctx).2)] ++ ctx.env

theorem pointAddUnequalXSubRightRawEnv_hi (ctx : PointAddUnequalXSubRightContext) :
    VEnv.get (pointAddUnequalXSubRightRawEnv ctx) "fc0_88" =
      some (pointAddUnequalXSubRightRaw ctx).1 := by rfl

theorem pointAddUnequalXSubRightRawEnv_lo (ctx : PointAddUnequalXSubRightContext) :
    VEnv.get (pointAddUnequalXSubRightRawEnv ctx) "fc0_89" =
      some (pointAddUnequalXSubRightRaw ctx).2 := by rfl

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
