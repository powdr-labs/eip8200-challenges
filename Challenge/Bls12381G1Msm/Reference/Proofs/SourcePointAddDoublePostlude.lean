import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddXEq

set_option warningAsError true

/-! Value-only execution of the point-doubling output-store postlude. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

structure PointAddDoublePostContext where
  env : VEnv Challenge.EvmProof.modexpExec.toDialect
  state : EvmState
  xHi : U256
  xLo : U256
  yHi : U256
  yLo : U256
  tempHi : U256
  tempLo : U256
  env_xHi : VEnv.get env "\x00122" = some xHi
  env_xLo : VEnv.get env "\x00123" = some xLo
  env_yHi : VEnv.get env "\x00126" = some yHi
  env_yLo : VEnv.get env "\x00127" = some yLo
  env_tempHi : VEnv.get env "\x00124" = some tempHi
  env_tempLo : VEnv.get env "\x00125" = some tempLo

def pointAddDoublePostlude : Block Op := pointAddXEqMainBody.drop 14
def pointAddDoublePostStmt0 : Stmt Op := pointAddDoublePostlude[0]!
def pointAddDoublePostStmt1 : Stmt Op := pointAddDoublePostlude[1]!
def pointAddDoublePostStmt2 : Stmt Op := pointAddDoublePostlude[2]!
def pointAddDoublePostStmt3 : Stmt Op := pointAddDoublePostlude[3]!
def pointAddDoublePostStmt4 : Stmt Op := pointAddDoublePostlude[4]!
def pointAddDoublePostStmt5 : Stmt Op := pointAddDoublePostlude[5]!
def pointAddDoublePostStmt6 : Stmt Op := pointAddDoublePostlude[6]!
def pointAddDoublePostStmt7 : Stmt Op := pointAddDoublePostlude[7]!

theorem pointAddDoublePostlude_eq : pointAddDoublePostlude =
    [pointAddDoublePostStmt0, pointAddDoublePostStmt1,
     pointAddDoublePostStmt2, pointAddDoublePostStmt3,
     pointAddDoublePostStmt4, pointAddDoublePostStmt5,
     pointAddDoublePostStmt6, pointAddDoublePostStmt7] := by rfl
theorem pointAddDoublePostStmt0_eq : pointAddDoublePostStmt0 =
    .letDecl [] none := by rfl
theorem pointAddDoublePostStmt1_eq : pointAddDoublePostStmt1 =
    .assign ["\x00124"] (.var "\x00123") := by rfl
theorem pointAddDoublePostStmt2_eq : pointAddDoublePostStmt2 =
    .assign ["\x00125"] (.var "\x00122") := by rfl
theorem pointAddDoublePostStmt3_eq : pointAddDoublePostStmt3 =
    .assign ["\x00122"]
      (.builtin .mload [.lit (.number 1536)]) := by rfl
theorem pointAddDoublePostStmt4_eq : pointAddDoublePostStmt4 =
    .exprStmt (.builtin .mstore
      [.var "\x00122", .var "\x00125"]) := by rfl
theorem pointAddDoublePostStmt5_eq : pointAddDoublePostStmt5 =
    .exprStmt (.builtin .mstore
      [.builtin .add [.var "\x00122", .lit (.number 32)],
       .var "\x00124"]) := by rfl
theorem pointAddDoublePostStmt6_eq : pointAddDoublePostStmt6 =
    .exprStmt (.builtin .mstore
      [.builtin .add [.var "\x00122", .lit (.number 64)],
       .var "\x00126"]) := by rfl
theorem pointAddDoublePostStmt7_eq : pointAddDoublePostStmt7 =
    .exprStmt (.builtin .mstore
      [.builtin .add [.var "\x00122", .lit (.number 96)],
       .var "\x00127"]) := by rfl

def pointAddDoublePostEnv1 (ctx : PointAddDoublePostContext) :=
  VEnv.set ctx.env "\x00124" ctx.xLo
def pointAddDoublePostEnv2 (ctx : PointAddDoublePostContext) :=
  VEnv.set (pointAddDoublePostEnv1 ctx) "\x00125" ctx.xHi
def pointAddDoublePostOut (ctx : PointAddDoublePostContext) : U256 :=
  loadWord ctx.state.memory 1536
def pointAddDoublePostEnv (ctx : PointAddDoublePostContext) :=
  VEnv.set (pointAddDoublePostEnv2 ctx) "\x00122"
    (pointAddDoublePostOut ctx)

def pointAddDoublePostStoreState (yst : EvmState) (offset value : U256) : EvmState :=
  { touchMemory yst offset.toNat 32 with
    memory := storeWord yst.memory offset.toNat value }

def pointAddDoublePostLoadState (ctx : PointAddDoublePostContext) : EvmState :=
  touchMemory ctx.state 1536 32
def pointAddDoublePostState1 (ctx : PointAddDoublePostContext) : EvmState :=
  pointAddDoublePostStoreState (pointAddDoublePostLoadState ctx)
    (pointAddDoublePostOut ctx) ctx.xHi
def pointAddDoublePostState2 (ctx : PointAddDoublePostContext) : EvmState :=
  pointAddDoublePostStoreState (pointAddDoublePostState1 ctx)
    (pointAddDoublePostOut ctx + 32) ctx.xLo
def pointAddDoublePostState3 (ctx : PointAddDoublePostContext) : EvmState :=
  pointAddDoublePostStoreState (pointAddDoublePostState2 ctx)
    (pointAddDoublePostOut ctx + 64) ctx.yHi
def pointAddDoublePostState (ctx : PointAddDoublePostContext) : EvmState :=
  pointAddDoublePostStoreState (pointAddDoublePostState3 ctx)
    (pointAddDoublePostOut ctx + 96) ctx.yLo

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
