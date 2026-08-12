import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalYMul

set_option warningAsError true

/-! Frozen AST and value-only context for `lambda * delta - left.y`.

The context severs the final inlined subtraction from the concrete proof DAG
that produced its two input words. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

structure PointAddUnequalYSubContext where
  env : VEnv Challenge.EvmProof.modexpExec.toDialect
  state : EvmState
  inputHi : U256
  inputLo : U256
  env_hi : VEnv.get env "\x00140" = some inputHi
  env_lo : VEnv.get env "\x00141" = some inputLo

def pointAddUnequalYSubBody : Block Op :=
  match pointAddUnequalYSubStmt with | .block body => body | _ => []
def pointAddUnequalYSubRawDeclStmt : Stmt Op := pointAddUnequalYSubBody[0]!
def pointAddUnequalYSubRawBlockStmt : Stmt Op := pointAddUnequalYSubBody[1]!
def pointAddUnequalYSubRepairStmt : Stmt Op := pointAddUnequalYSubBody[2]!
def pointAddUnequalYSubOutHiStmt : Stmt Op := pointAddUnequalYSubBody[3]!
def pointAddUnequalYSubOutLoStmt : Stmt Op := pointAddUnequalYSubBody[4]!

def pointAddUnequalYSubRawBody : Block Op :=
  match pointAddUnequalYSubRawBlockStmt with | .block body => body | _ => []
def pointAddUnequalYSubRawStmt0 : Stmt Op := pointAddUnequalYSubRawBody[0]!
def pointAddUnequalYSubRawStmt1 : Stmt Op := pointAddUnequalYSubRawBody[1]!
def pointAddUnequalYSubRawStmt2 : Stmt Op := pointAddUnequalYSubRawBody[2]!
def pointAddUnequalYSubRawStmt3 : Stmt Op := pointAddUnequalYSubRawBody[3]!
def pointAddUnequalYSubRawStmt4 : Stmt Op := pointAddUnequalYSubRawBody[4]!
def pointAddUnequalYSubRawStmt5 : Stmt Op := pointAddUnequalYSubRawBody[5]!

theorem pointAddUnequalYSubStmt_eq : pointAddUnequalYSubStmt =
    .block pointAddUnequalYSubBody := by rfl

theorem pointAddUnequalYSubBody_eq : pointAddUnequalYSubBody =
    [pointAddUnequalYSubRawDeclStmt, pointAddUnequalYSubRawBlockStmt,
     pointAddUnequalYSubRepairStmt, pointAddUnequalYSubOutHiStmt,
     pointAddUnequalYSubOutLoStmt] := by rfl

theorem pointAddUnequalYSubRawDeclStmt_eq : pointAddUnequalYSubRawDeclStmt =
    .letDecl ["fc0_102", "fc0_103"] none := by rfl

theorem pointAddUnequalYSubRawBlockStmt_eq : pointAddUnequalYSubRawBlockStmt =
    .block pointAddUnequalYSubRawBody := by rfl

theorem pointAddUnequalYSubRawBody_eq : pointAddUnequalYSubRawBody =
    [pointAddUnequalYSubRawStmt0, pointAddUnequalYSubRawStmt1,
     pointAddUnequalYSubRawStmt2, pointAddUnequalYSubRawStmt3,
     pointAddUnequalYSubRawStmt4, pointAddUnequalYSubRawStmt5] := by rfl

theorem pointAddUnequalYSubRawStmt0_eq : pointAddUnequalYSubRawStmt0 =
    .letDecl ["fc0_104"]
      (some (.builtin .mload
        [.builtin .add
          [.builtin .mload [.lit (.number 1568)], .lit (.number 96)]])) := by rfl

theorem pointAddUnequalYSubRawStmt1_eq : pointAddUnequalYSubRawStmt1 =
    .letDecl ["fc0_105"]
      (some (.builtin .mload
        [.builtin .add
          [.builtin .mload [.lit (.number 1568)], .lit (.number 64)]])) := by rfl

theorem pointAddUnequalYSubRawStmt2_eq : pointAddUnequalYSubRawStmt2 =
    .letDecl ["fc0_106"] (some (.var "\x00141")) := by rfl

theorem pointAddUnequalYSubRawStmt3_eq : pointAddUnequalYSubRawStmt3 =
    .letDecl ["fc0_107"] (some (.var "\x00140")) := by rfl

theorem pointAddUnequalYSubRawStmt4_eq : pointAddUnequalYSubRawStmt4 =
    .assign ["fc0_103"]
      (.builtin .sub [.var "fc0_106", .var "fc0_104"]) := by rfl

theorem pointAddUnequalYSubRawStmt5_eq : pointAddUnequalYSubRawStmt5 =
    .assign ["fc0_102"]
      (.builtin .sub
        [.builtin .sub [.var "fc0_107", .var "fc0_105"],
         .builtin .gt [.var "fc0_104", .var "fc0_106"]]) := by rfl

theorem pointAddUnequalYSubRepairStmt_eq : pointAddUnequalYSubRepairStmt =
    .cond
      (.builtin .gt
        [.var "fc0_102",
         .lit (.number 34565483545414906068789196026815425751)])
      [.letDecl ["\x0051"]
        (some (.builtin .add
          [.var "fc0_103",
           .lit (.number
            45442060874369865957053122457065728162598490762543039060009208264153100167851)])),
       .assign ["fc0_102"]
        (.builtin .add
          [.var "fc0_102",
           .builtin .add
            [.lit (.number 34565483545414906068789196026815425751),
             .builtin .lt [.var "\x0051", .var "fc0_103"]]]),
       .assign ["fc0_103"] (.var "\x0051")] := by rfl

theorem pointAddUnequalYSubOutHiStmt_eq : pointAddUnequalYSubOutHiStmt =
    .assign ["\x00140"] (.var "fc0_102") := by rfl

theorem pointAddUnequalYSubOutLoStmt_eq : pointAddUnequalYSubOutLoStmt =
    .assign ["\x00141"] (.var "fc0_103") := by rfl

theorem hoist_pointAddUnequalYSubRawBody :
    hoist Challenge.EvmProof.modexpExec.toDialect pointAddUnequalYSubRawBody = [] := by rfl

theorem hoist_pointAddUnequalYSubBody :
    hoist Challenge.EvmProof.modexpExec.toDialect pointAddUnequalYSubBody = [] := by rfl

def pointAddUnequalYSubPtr (ctx : PointAddUnequalYSubContext) : U256 :=
  loadWord ctx.state.memory 1568
def pointAddUnequalYSubLeftLo (ctx : PointAddUnequalYSubContext) : U256 :=
  loadWord ctx.state.memory (pointAddUnequalYSubPtr ctx + 96).toNat
def pointAddUnequalYSubLeftHi (ctx : PointAddUnequalYSubContext) : U256 :=
  loadWord ctx.state.memory (pointAddUnequalYSubPtr ctx + 64).toNat

def pointAddUnequalYSubRawLo (ctx : PointAddUnequalYSubContext) : U256 :=
  ctx.inputLo - pointAddUnequalYSubLeftLo ctx
def pointAddUnequalYSubRawHi (ctx : PointAddUnequalYSubContext) : U256 :=
  ctx.inputHi - pointAddUnequalYSubLeftHi ctx -
    b2w (BitVec.ult ctx.inputLo (pointAddUnequalYSubLeftLo ctx))
def pointAddUnequalYSubRaw (ctx : PointAddUnequalYSubContext) : U256 × U256 :=
  (pointAddUnequalYSubRawHi ctx, pointAddUnequalYSubRawLo ctx)

def pointAddUnequalYSubState1 (ctx : PointAddUnequalYSubContext) :=
  touchMemory ctx.state 1568 32
def pointAddUnequalYSubState2 (ctx : PointAddUnequalYSubContext) :=
  touchMemory (pointAddUnequalYSubState1 ctx)
    (pointAddUnequalYSubPtr ctx + 96).toNat 32
def pointAddUnequalYSubState3 (ctx : PointAddUnequalYSubContext) :=
  touchMemory (pointAddUnequalYSubState2 ctx) 1568 32
def pointAddUnequalYSubRawState (ctx : PointAddUnequalYSubContext) :=
  touchMemory (pointAddUnequalYSubState3 ctx)
    (pointAddUnequalYSubPtr ctx + 64).toNat 32

def pointAddUnequalYSubRawEnv (ctx : PointAddUnequalYSubContext) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  [("fc0_102", (pointAddUnequalYSubRaw ctx).1),
   ("fc0_103", (pointAddUnequalYSubRaw ctx).2)] ++ ctx.env

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
