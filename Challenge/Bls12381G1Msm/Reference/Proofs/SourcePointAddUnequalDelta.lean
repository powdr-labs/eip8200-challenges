import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalXSubBridge

set_option warningAsError true

/-! Frozen AST and value-only context for `left.x - x3` in unequal addition.

The proof stages below this boundary know only the two `x3` words and the
current memory.  In particular, they do not import the concrete proof DAG
that computed `x3`; that DAG is connected once, after this generic proof is
complete. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def pointAddUnequalDeltaBody : Block Op :=
  match pointAddUnequalDeltaStmt with
  | .block body => body
  | _ => []

theorem pointAddUnequalDeltaInitStmt_eq : pointAddUnequalDeltaInitStmt =
    .letDecl ["\x00138", "\x00139"] none := by
  rfl

theorem pointAddUnequalDeltaStmt_eq : pointAddUnequalDeltaStmt =
    .block pointAddUnequalDeltaBody := by
  rfl

structure PointAddUnequalDeltaContext where
  env : VEnv Challenge.EvmProof.modexpExec.toDialect
  state : EvmState
  x3Hi : U256
  x3Lo : U256
  env_hi : VEnv.get env "\x00136" = some x3Hi
  env_lo : VEnv.get env "\x00137" = some x3Lo

def pointAddUnequalDeltaRawDeclStmt : Stmt Op := pointAddUnequalDeltaBody[0]!
def pointAddUnequalDeltaRawBlockStmt : Stmt Op := pointAddUnequalDeltaBody[1]!
def pointAddUnequalDeltaRepairStmt : Stmt Op := pointAddUnequalDeltaBody[2]!
def pointAddUnequalDeltaOutHiStmt : Stmt Op := pointAddUnequalDeltaBody[3]!
def pointAddUnequalDeltaOutLoStmt : Stmt Op := pointAddUnequalDeltaBody[4]!

def pointAddUnequalDeltaRawBody : Block Op :=
  match pointAddUnequalDeltaRawBlockStmt with
  | .block body => body
  | _ => []

def pointAddUnequalDeltaRawStmt0 : Stmt Op := pointAddUnequalDeltaRawBody[0]!
def pointAddUnequalDeltaRawStmt1 : Stmt Op := pointAddUnequalDeltaRawBody[1]!
def pointAddUnequalDeltaRawStmt2 : Stmt Op := pointAddUnequalDeltaRawBody[2]!
def pointAddUnequalDeltaRawStmt3 : Stmt Op := pointAddUnequalDeltaRawBody[3]!
def pointAddUnequalDeltaRawStmt4 : Stmt Op := pointAddUnequalDeltaRawBody[4]!
def pointAddUnequalDeltaRawStmt5 : Stmt Op := pointAddUnequalDeltaRawBody[5]!

theorem pointAddUnequalDeltaBody_eq : pointAddUnequalDeltaBody =
    [pointAddUnequalDeltaRawDeclStmt, pointAddUnequalDeltaRawBlockStmt,
     pointAddUnequalDeltaRepairStmt, pointAddUnequalDeltaOutHiStmt,
     pointAddUnequalDeltaOutLoStmt] := by rfl

theorem pointAddUnequalDeltaRawDeclStmt_eq : pointAddUnequalDeltaRawDeclStmt =
    .letDecl ["fc0_95", "fc0_96"] none := by rfl

theorem pointAddUnequalDeltaRawBlockStmt_eq : pointAddUnequalDeltaRawBlockStmt =
    .block pointAddUnequalDeltaRawBody := by rfl

theorem pointAddUnequalDeltaRawBody_eq : pointAddUnequalDeltaRawBody =
    [pointAddUnequalDeltaRawStmt0, pointAddUnequalDeltaRawStmt1,
     pointAddUnequalDeltaRawStmt2, pointAddUnequalDeltaRawStmt3,
     pointAddUnequalDeltaRawStmt4, pointAddUnequalDeltaRawStmt5] := by rfl

theorem pointAddUnequalDeltaRawStmt0_eq : pointAddUnequalDeltaRawStmt0 =
    .letDecl ["fc0_97"] (some (.var "\x00137")) := by rfl

theorem pointAddUnequalDeltaRawStmt1_eq : pointAddUnequalDeltaRawStmt1 =
    .letDecl ["fc0_98"] (some (.var "\x00136")) := by rfl

theorem pointAddUnequalDeltaRawStmt2_eq : pointAddUnequalDeltaRawStmt2 =
    .letDecl ["fc0_99"]
      (some (.builtin .mload
        [.builtin .add
          [.builtin .mload [.lit (.number 1568)], .lit (.number 32)]])) := by rfl

theorem pointAddUnequalDeltaRawStmt3_eq : pointAddUnequalDeltaRawStmt3 =
    .letDecl ["fc0_100"]
      (some (.builtin .mload
        [.builtin .mload [.lit (.number 1568)]])) := by rfl

theorem pointAddUnequalDeltaRawStmt4_eq : pointAddUnequalDeltaRawStmt4 =
    .assign ["fc0_96"]
      (.builtin .sub [.var "fc0_99", .var "fc0_97"]) := by rfl

theorem pointAddUnequalDeltaRawStmt5_eq : pointAddUnequalDeltaRawStmt5 =
    .assign ["fc0_95"]
      (.builtin .sub
        [.builtin .sub [.var "fc0_100", .var "fc0_98"],
         .builtin .gt [.var "fc0_97", .var "fc0_99"]]) := by rfl

theorem pointAddUnequalDeltaRepairStmt_eq : pointAddUnequalDeltaRepairStmt =
    .cond
      (.builtin .gt
        [.var "fc0_95",
         .lit (.number 34565483545414906068789196026815425751)])
      [.letDecl ["\x0051"]
        (some (.builtin .add
          [.var "fc0_96",
           .lit (.number
            45442060874369865957053122457065728162598490762543039060009208264153100167851)])),
       .assign ["fc0_95"]
        (.builtin .add
          [.var "fc0_95",
           .builtin .add
            [.lit (.number 34565483545414906068789196026815425751),
             .builtin .lt [.var "\x0051", .var "fc0_96"]]]),
       .assign ["fc0_96"] (.var "\x0051")] := by rfl

theorem pointAddUnequalDeltaOutHiStmt_eq : pointAddUnequalDeltaOutHiStmt =
    .assign ["\x00138"] (.var "fc0_95") := by rfl

theorem pointAddUnequalDeltaOutLoStmt_eq : pointAddUnequalDeltaOutLoStmt =
    .assign ["\x00139"] (.var "fc0_96") := by rfl

theorem hoist_pointAddUnequalDeltaRawBody :
    hoist Challenge.EvmProof.modexpExec.toDialect
      pointAddUnequalDeltaRawBody = [] := by rfl

theorem hoist_pointAddUnequalDeltaBody :
    hoist Challenge.EvmProof.modexpExec.toDialect
      pointAddUnequalDeltaBody = [] := by rfl

def pointAddUnequalDeltaPtr (ctx : PointAddUnequalDeltaContext) : U256 :=
  loadWord ctx.state.memory 1568

def pointAddUnequalDeltaLeftHi (ctx : PointAddUnequalDeltaContext) : U256 :=
  loadWord ctx.state.memory (pointAddUnequalDeltaPtr ctx).toNat

def pointAddUnequalDeltaLeftLo (ctx : PointAddUnequalDeltaContext) : U256 :=
  loadWord ctx.state.memory (pointAddUnequalDeltaPtr ctx + 32).toNat

def pointAddUnequalDeltaRawLo (ctx : PointAddUnequalDeltaContext) : U256 :=
  pointAddUnequalDeltaLeftLo ctx - ctx.x3Lo

def pointAddUnequalDeltaRawHi (ctx : PointAddUnequalDeltaContext) : U256 :=
  pointAddUnequalDeltaLeftHi ctx - ctx.x3Hi -
    b2w (BitVec.ult (pointAddUnequalDeltaLeftLo ctx) ctx.x3Lo)

def pointAddUnequalDeltaRaw (ctx : PointAddUnequalDeltaContext) : U256 × U256 :=
  (pointAddUnequalDeltaRawHi ctx, pointAddUnequalDeltaRawLo ctx)

def pointAddUnequalDeltaState1 (ctx : PointAddUnequalDeltaContext) :=
  touchMemory ctx.state 1568 32

def pointAddUnequalDeltaState2 (ctx : PointAddUnequalDeltaContext) :=
  touchMemory (pointAddUnequalDeltaState1 ctx)
    (pointAddUnequalDeltaPtr ctx + 32).toNat 32

def pointAddUnequalDeltaState3 (ctx : PointAddUnequalDeltaContext) :=
  touchMemory (pointAddUnequalDeltaState2 ctx) 1568 32

def pointAddUnequalDeltaRawState (ctx : PointAddUnequalDeltaContext) :=
  touchMemory (pointAddUnequalDeltaState3 ctx)
    (pointAddUnequalDeltaPtr ctx).toNat 32

def pointAddUnequalDeltaRawEnv (ctx : PointAddUnequalDeltaContext) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  [("fc0_95", (pointAddUnequalDeltaRaw ctx).1),
   ("fc0_96", (pointAddUnequalDeltaRaw ctx).2)] ++ ctx.env

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
