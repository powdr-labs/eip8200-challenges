import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddXEq

set_option warningAsError true

/-! Frozen AST and value-only context for `left.x - x3` in point doubling.

The proof stages below this boundary know only the two `x3` words and the
current memory.  In particular, they do not import the concrete proof DAG
that computed `x3`; that DAG is connected once, after this generic proof is
complete. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

structure PointAddDoubleDeltaContext where
  env : VEnv Challenge.EvmProof.modexpExec.toDialect
  state : EvmState
  x3Hi : U256
  x3Lo : U256
  env_hi : VEnv.get env "\x00122" = some x3Hi
  env_lo : VEnv.get env "\x00123" = some x3Lo

def pointAddDoubleDeltaRawDeclStmt : Stmt Op := pointAddDoubleDeltaBody[0]!
def pointAddDoubleDeltaRawBlockStmt : Stmt Op := pointAddDoubleDeltaBody[1]!
def pointAddDoubleDeltaRepairStmt : Stmt Op := pointAddDoubleDeltaBody[2]!
def pointAddDoubleDeltaOutHiStmt : Stmt Op := pointAddDoubleDeltaBody[3]!
def pointAddDoubleDeltaOutLoStmt : Stmt Op := pointAddDoubleDeltaBody[4]!

def pointAddDoubleDeltaRawBody : Block Op :=
  match pointAddDoubleDeltaRawBlockStmt with
  | .block body => body
  | _ => []

def pointAddDoubleDeltaRawStmt0 : Stmt Op := pointAddDoubleDeltaRawBody[0]!
def pointAddDoubleDeltaRawStmt1 : Stmt Op := pointAddDoubleDeltaRawBody[1]!
def pointAddDoubleDeltaRawStmt2 : Stmt Op := pointAddDoubleDeltaRawBody[2]!
def pointAddDoubleDeltaRawStmt3 : Stmt Op := pointAddDoubleDeltaRawBody[3]!
def pointAddDoubleDeltaRawStmt4 : Stmt Op := pointAddDoubleDeltaRawBody[4]!
def pointAddDoubleDeltaRawStmt5 : Stmt Op := pointAddDoubleDeltaRawBody[5]!

theorem pointAddDoubleDeltaBody_eq : pointAddDoubleDeltaBody =
    [pointAddDoubleDeltaRawDeclStmt, pointAddDoubleDeltaRawBlockStmt,
     pointAddDoubleDeltaRepairStmt, pointAddDoubleDeltaOutHiStmt,
     pointAddDoubleDeltaOutLoStmt] := by rfl

theorem pointAddDoubleDeltaRawDeclStmt_eq : pointAddDoubleDeltaRawDeclStmt =
    .letDecl ["fc0_42", "fc0_43"] none := by rfl

theorem pointAddDoubleDeltaRawBlockStmt_eq : pointAddDoubleDeltaRawBlockStmt =
    .block pointAddDoubleDeltaRawBody := by rfl

theorem pointAddDoubleDeltaRawBody_eq : pointAddDoubleDeltaRawBody =
    [pointAddDoubleDeltaRawStmt0, pointAddDoubleDeltaRawStmt1,
     pointAddDoubleDeltaRawStmt2, pointAddDoubleDeltaRawStmt3,
     pointAddDoubleDeltaRawStmt4, pointAddDoubleDeltaRawStmt5] := by rfl

theorem pointAddDoubleDeltaRawStmt0_eq : pointAddDoubleDeltaRawStmt0 =
    .letDecl ["fc0_44"] (some (.var "\x00123")) := by rfl

theorem pointAddDoubleDeltaRawStmt1_eq : pointAddDoubleDeltaRawStmt1 =
    .letDecl ["fc0_45"] (some (.var "\x00122")) := by rfl

theorem pointAddDoubleDeltaRawStmt2_eq : pointAddDoubleDeltaRawStmt2 =
    .letDecl ["fc0_46"]
      (some (.builtin .mload
        [.builtin .add
          [.builtin .mload [.lit (.number 1568)], .lit (.number 32)]])) := by rfl

theorem pointAddDoubleDeltaRawStmt3_eq : pointAddDoubleDeltaRawStmt3 =
    .letDecl ["fc0_47"]
      (some (.builtin .mload
        [.builtin .mload [.lit (.number 1568)]])) := by rfl

theorem pointAddDoubleDeltaRawStmt4_eq : pointAddDoubleDeltaRawStmt4 =
    .assign ["fc0_43"]
      (.builtin .sub [.var "fc0_46", .var "fc0_44"]) := by rfl

theorem pointAddDoubleDeltaRawStmt5_eq : pointAddDoubleDeltaRawStmt5 =
    .assign ["fc0_42"]
      (.builtin .sub
        [.builtin .sub [.var "fc0_47", .var "fc0_45"],
         .builtin .gt [.var "fc0_44", .var "fc0_46"]]) := by rfl

theorem pointAddDoubleDeltaRepairStmt_eq : pointAddDoubleDeltaRepairStmt =
    .cond
      (.builtin .gt
        [.var "fc0_42",
         .lit (.number 34565483545414906068789196026815425751)])
      [.letDecl ["\x0051"]
        (some (.builtin .add
          [.var "fc0_43",
           .lit (.number
            45442060874369865957053122457065728162598490762543039060009208264153100167851)])),
       .assign ["fc0_42"]
        (.builtin .add
          [.var "fc0_42",
           .builtin .add
            [.lit (.number 34565483545414906068789196026815425751),
             .builtin .lt [.var "\x0051", .var "fc0_43"]]]),
       .assign ["fc0_43"] (.var "\x0051")] := by rfl

theorem pointAddDoubleDeltaOutHiStmt_eq : pointAddDoubleDeltaOutHiStmt =
    .assign ["\x00124"] (.var "fc0_42") := by rfl

theorem pointAddDoubleDeltaOutLoStmt_eq : pointAddDoubleDeltaOutLoStmt =
    .assign ["\x00125"] (.var "fc0_43") := by rfl

theorem hoist_pointAddDoubleDeltaRawBody :
    hoist Challenge.EvmProof.modexpExec.toDialect
      pointAddDoubleDeltaRawBody = [] := by rfl

theorem hoist_pointAddDoubleDeltaBody :
    hoist Challenge.EvmProof.modexpExec.toDialect
      pointAddDoubleDeltaBody = [] := by rfl

def pointAddDoubleDeltaPtr (ctx : PointAddDoubleDeltaContext) : U256 :=
  loadWord ctx.state.memory 1568

def pointAddDoubleDeltaLeftHi (ctx : PointAddDoubleDeltaContext) : U256 :=
  loadWord ctx.state.memory (pointAddDoubleDeltaPtr ctx).toNat

def pointAddDoubleDeltaLeftLo (ctx : PointAddDoubleDeltaContext) : U256 :=
  loadWord ctx.state.memory (pointAddDoubleDeltaPtr ctx + 32).toNat

def pointAddDoubleDeltaRawLo (ctx : PointAddDoubleDeltaContext) : U256 :=
  pointAddDoubleDeltaLeftLo ctx - ctx.x3Lo

def pointAddDoubleDeltaRawHi (ctx : PointAddDoubleDeltaContext) : U256 :=
  pointAddDoubleDeltaLeftHi ctx - ctx.x3Hi -
    b2w (BitVec.ult (pointAddDoubleDeltaLeftLo ctx) ctx.x3Lo)

def pointAddDoubleDeltaRaw (ctx : PointAddDoubleDeltaContext) : U256 × U256 :=
  (pointAddDoubleDeltaRawHi ctx, pointAddDoubleDeltaRawLo ctx)

def pointAddDoubleDeltaState1 (ctx : PointAddDoubleDeltaContext) :=
  touchMemory ctx.state 1568 32

def pointAddDoubleDeltaState2 (ctx : PointAddDoubleDeltaContext) :=
  touchMemory (pointAddDoubleDeltaState1 ctx)
    (pointAddDoubleDeltaPtr ctx + 32).toNat 32

def pointAddDoubleDeltaState3 (ctx : PointAddDoubleDeltaContext) :=
  touchMemory (pointAddDoubleDeltaState2 ctx) 1568 32

def pointAddDoubleDeltaRawState (ctx : PointAddDoubleDeltaContext) :=
  touchMemory (pointAddDoubleDeltaState3 ctx)
    (pointAddDoubleDeltaPtr ctx).toNat 32

def pointAddDoubleDeltaRawEnv (ctx : PointAddDoubleDeltaContext) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  [("fc0_42", (pointAddDoubleDeltaRaw ctx).1),
   ("fc0_43", (pointAddDoubleDeltaRaw ctx).2)] ++ ctx.env

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
