import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddXEq

set_option warningAsError true

/-! Frozen AST and value-only context for `lambda * delta - left.y`.

The context severs the final inlined subtraction from the concrete proof DAG
that produced its two input words. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

structure PointAddDoubleYSubContext where
  env : VEnv Challenge.EvmProof.modexpExec.toDialect
  state : EvmState
  inputHi : U256
  inputLo : U256
  env_hi : VEnv.get env "\x00126" = some inputHi
  env_lo : VEnv.get env "\x00127" = some inputLo

def pointAddDoubleYSubBody : Block Op :=
  match pointAddDoubleYSubStmt with | .block body => body | _ => []
def pointAddDoubleYSubRawDeclStmt : Stmt Op := pointAddDoubleYSubBody[0]!
def pointAddDoubleYSubRawBlockStmt : Stmt Op := pointAddDoubleYSubBody[1]!
def pointAddDoubleYSubRepairStmt : Stmt Op := pointAddDoubleYSubBody[2]!
def pointAddDoubleYSubOutHiStmt : Stmt Op := pointAddDoubleYSubBody[3]!
def pointAddDoubleYSubOutLoStmt : Stmt Op := pointAddDoubleYSubBody[4]!

def pointAddDoubleYSubRawBody : Block Op :=
  match pointAddDoubleYSubRawBlockStmt with | .block body => body | _ => []
def pointAddDoubleYSubRawStmt0 : Stmt Op := pointAddDoubleYSubRawBody[0]!
def pointAddDoubleYSubRawStmt1 : Stmt Op := pointAddDoubleYSubRawBody[1]!
def pointAddDoubleYSubRawStmt2 : Stmt Op := pointAddDoubleYSubRawBody[2]!
def pointAddDoubleYSubRawStmt3 : Stmt Op := pointAddDoubleYSubRawBody[3]!
def pointAddDoubleYSubRawStmt4 : Stmt Op := pointAddDoubleYSubRawBody[4]!
def pointAddDoubleYSubRawStmt5 : Stmt Op := pointAddDoubleYSubRawBody[5]!

theorem pointAddDoubleYSubStmt_eq : pointAddDoubleYSubStmt =
    .block pointAddDoubleYSubBody := by rfl

theorem pointAddDoubleYSubBody_eq : pointAddDoubleYSubBody =
    [pointAddDoubleYSubRawDeclStmt, pointAddDoubleYSubRawBlockStmt,
     pointAddDoubleYSubRepairStmt, pointAddDoubleYSubOutHiStmt,
     pointAddDoubleYSubOutLoStmt] := by rfl

theorem pointAddDoubleYSubRawDeclStmt_eq : pointAddDoubleYSubRawDeclStmt =
    .letDecl ["fc0_49", "fc0_50"] none := by rfl

theorem pointAddDoubleYSubRawBlockStmt_eq : pointAddDoubleYSubRawBlockStmt =
    .block pointAddDoubleYSubRawBody := by rfl

theorem pointAddDoubleYSubRawBody_eq : pointAddDoubleYSubRawBody =
    [pointAddDoubleYSubRawStmt0, pointAddDoubleYSubRawStmt1,
     pointAddDoubleYSubRawStmt2, pointAddDoubleYSubRawStmt3,
     pointAddDoubleYSubRawStmt4, pointAddDoubleYSubRawStmt5] := by rfl

theorem pointAddDoubleYSubRawStmt0_eq : pointAddDoubleYSubRawStmt0 =
    .letDecl ["fc0_51"]
      (some (.builtin .mload
        [.builtin .add
          [.builtin .mload [.lit (.number 1568)], .lit (.number 96)]])) := by rfl

theorem pointAddDoubleYSubRawStmt1_eq : pointAddDoubleYSubRawStmt1 =
    .letDecl ["fc0_52"]
      (some (.builtin .mload
        [.builtin .add
          [.builtin .mload [.lit (.number 1568)], .lit (.number 64)]])) := by rfl

theorem pointAddDoubleYSubRawStmt2_eq : pointAddDoubleYSubRawStmt2 =
    .letDecl ["fc0_53"] (some (.var "\x00127")) := by rfl

theorem pointAddDoubleYSubRawStmt3_eq : pointAddDoubleYSubRawStmt3 =
    .letDecl ["fc0_54"] (some (.var "\x00126")) := by rfl

theorem pointAddDoubleYSubRawStmt4_eq : pointAddDoubleYSubRawStmt4 =
    .assign ["fc0_50"]
      (.builtin .sub [.var "fc0_53", .var "fc0_51"]) := by rfl

theorem pointAddDoubleYSubRawStmt5_eq : pointAddDoubleYSubRawStmt5 =
    .assign ["fc0_49"]
      (.builtin .sub
        [.builtin .sub [.var "fc0_54", .var "fc0_52"],
         .builtin .gt [.var "fc0_51", .var "fc0_53"]]) := by rfl

theorem pointAddDoubleYSubRepairStmt_eq : pointAddDoubleYSubRepairStmt =
    .cond
      (.builtin .gt
        [.var "fc0_49",
         .lit (.number 34565483545414906068789196026815425751)])
      [.letDecl ["\x0051"]
        (some (.builtin .add
          [.var "fc0_50",
           .lit (.number
            45442060874369865957053122457065728162598490762543039060009208264153100167851)])),
       .assign ["fc0_49"]
        (.builtin .add
          [.var "fc0_49",
           .builtin .add
            [.lit (.number 34565483545414906068789196026815425751),
             .builtin .lt [.var "\x0051", .var "fc0_50"]]]),
       .assign ["fc0_50"] (.var "\x0051")] := by rfl

theorem pointAddDoubleYSubOutHiStmt_eq : pointAddDoubleYSubOutHiStmt =
    .assign ["\x00126"] (.var "fc0_49") := by rfl

theorem pointAddDoubleYSubOutLoStmt_eq : pointAddDoubleYSubOutLoStmt =
    .assign ["\x00127"] (.var "fc0_50") := by rfl

theorem hoist_pointAddDoubleYSubRawBody :
    hoist Challenge.EvmProof.modexpExec.toDialect pointAddDoubleYSubRawBody = [] := by rfl

theorem hoist_pointAddDoubleYSubBody :
    hoist Challenge.EvmProof.modexpExec.toDialect pointAddDoubleYSubBody = [] := by rfl

def pointAddDoubleYSubPtr (ctx : PointAddDoubleYSubContext) : U256 :=
  loadWord ctx.state.memory 1568
def pointAddDoubleYSubLeftLo (ctx : PointAddDoubleYSubContext) : U256 :=
  loadWord ctx.state.memory (pointAddDoubleYSubPtr ctx + 96).toNat
def pointAddDoubleYSubLeftHi (ctx : PointAddDoubleYSubContext) : U256 :=
  loadWord ctx.state.memory (pointAddDoubleYSubPtr ctx + 64).toNat

def pointAddDoubleYSubRawLo (ctx : PointAddDoubleYSubContext) : U256 :=
  ctx.inputLo - pointAddDoubleYSubLeftLo ctx
def pointAddDoubleYSubRawHi (ctx : PointAddDoubleYSubContext) : U256 :=
  ctx.inputHi - pointAddDoubleYSubLeftHi ctx -
    b2w (BitVec.ult ctx.inputLo (pointAddDoubleYSubLeftLo ctx))
def pointAddDoubleYSubRaw (ctx : PointAddDoubleYSubContext) : U256 × U256 :=
  (pointAddDoubleYSubRawHi ctx, pointAddDoubleYSubRawLo ctx)

def pointAddDoubleYSubState1 (ctx : PointAddDoubleYSubContext) :=
  touchMemory ctx.state 1568 32
def pointAddDoubleYSubState2 (ctx : PointAddDoubleYSubContext) :=
  touchMemory (pointAddDoubleYSubState1 ctx)
    (pointAddDoubleYSubPtr ctx + 96).toNat 32
def pointAddDoubleYSubState3 (ctx : PointAddDoubleYSubContext) :=
  touchMemory (pointAddDoubleYSubState2 ctx) 1568 32
def pointAddDoubleYSubRawState (ctx : PointAddDoubleYSubContext) :=
  touchMemory (pointAddDoubleYSubState3 ctx)
    (pointAddDoubleYSubPtr ctx + 64).toNat 32

def pointAddDoubleYSubRawEnv (ctx : PointAddDoubleYSubContext) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  [("fc0_49", (pointAddDoubleYSubRaw ctx).1),
   ("fc0_50", (pointAddDoubleYSubRaw ctx).2)] ++ ctx.env

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
