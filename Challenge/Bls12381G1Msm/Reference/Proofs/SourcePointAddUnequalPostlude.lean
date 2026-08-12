import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalYSubEnvLookup

set_option warningAsError true

/-! Value-only execution of the unequal-point output-store postlude. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

structure PointAddUnequalPostContext where
  xHi : U256
  xLo : U256
  yHi : U256
  yLo : U256
  tempHi : U256
  tempLo : U256
  env : VEnv Challenge.EvmProof.modexpExec.toDialect
  state : EvmState
  env_xHi : VEnv.get env "\x00136" = some xHi
  env_xLo : VEnv.get env "\x00137" = some xLo
  env_yHi : VEnv.get env "\x00140" = some yHi
  env_yLo : VEnv.get env "\x00141" = some yLo
  env_tempHi : VEnv.get env "\x00138" = some tempHi
  env_tempLo : VEnv.get env "\x00139" = some tempLo

def makePointAddUnequalPostContext
    (xHi xLo yHi yLo tempHi tempLo : U256)
    (env : VEnv Challenge.EvmProof.modexpExec.toDialect) (state : EvmState)
    (env_xHi : VEnv.get env "\x00136" = some xHi)
    (env_xLo : VEnv.get env "\x00137" = some xLo)
    (env_yHi : VEnv.get env "\x00140" = some yHi)
    (env_yLo : VEnv.get env "\x00141" = some yLo)
    (env_tempHi : VEnv.get env "\x00138" = some tempHi)
    (env_tempLo : VEnv.get env "\x00139" = some tempLo) :
    PointAddUnequalPostContext where
  xHi := xHi
  xLo := xLo
  yHi := yHi
  yLo := yLo
  tempHi := tempHi
  tempLo := tempLo
  env := env
  state := state
  env_xHi := env_xHi
  env_xLo := env_xLo
  env_yHi := env_yHi
  env_yLo := env_yLo
  env_tempHi := env_tempHi
  env_tempLo := env_tempLo

@[simp] theorem makePointAddUnequalPostContext_xHi
    (xHi xLo yHi yLo tempHi tempLo : U256)
    (env : VEnv Challenge.EvmProof.modexpExec.toDialect) (state : EvmState)
    (env_xHi : VEnv.get env "\x00136" = some xHi)
    (env_xLo : VEnv.get env "\x00137" = some xLo)
    (env_yHi : VEnv.get env "\x00140" = some yHi)
    (env_yLo : VEnv.get env "\x00141" = some yLo)
    (env_tempHi : VEnv.get env "\x00138" = some tempHi)
    (env_tempLo : VEnv.get env "\x00139" = some tempLo) :
    (makePointAddUnequalPostContext xHi xLo yHi yLo tempHi tempLo env state
      env_xHi env_xLo env_yHi env_yLo env_tempHi env_tempLo).xHi = xHi := by
  rfl

@[simp] theorem makePointAddUnequalPostContext_xLo
    (xHi xLo yHi yLo tempHi tempLo : U256)
    (env : VEnv Challenge.EvmProof.modexpExec.toDialect) (state : EvmState)
    (env_xHi : VEnv.get env "\x00136" = some xHi)
    (env_xLo : VEnv.get env "\x00137" = some xLo)
    (env_yHi : VEnv.get env "\x00140" = some yHi)
    (env_yLo : VEnv.get env "\x00141" = some yLo)
    (env_tempHi : VEnv.get env "\x00138" = some tempHi)
    (env_tempLo : VEnv.get env "\x00139" = some tempLo) :
    (makePointAddUnequalPostContext xHi xLo yHi yLo tempHi tempLo env state
      env_xHi env_xLo env_yHi env_yLo env_tempHi env_tempLo).xLo = xLo := by
  rfl

@[simp] theorem makePointAddUnequalPostContext_yHi
    (xHi xLo yHi yLo tempHi tempLo : U256)
    (env : VEnv Challenge.EvmProof.modexpExec.toDialect) (state : EvmState)
    (env_xHi : VEnv.get env "\x00136" = some xHi)
    (env_xLo : VEnv.get env "\x00137" = some xLo)
    (env_yHi : VEnv.get env "\x00140" = some yHi)
    (env_yLo : VEnv.get env "\x00141" = some yLo)
    (env_tempHi : VEnv.get env "\x00138" = some tempHi)
    (env_tempLo : VEnv.get env "\x00139" = some tempLo) :
    (makePointAddUnequalPostContext xHi xLo yHi yLo tempHi tempLo env state
      env_xHi env_xLo env_yHi env_yLo env_tempHi env_tempLo).yHi = yHi := by
  rfl

@[simp] theorem makePointAddUnequalPostContext_yLo
    (xHi xLo yHi yLo tempHi tempLo : U256)
    (env : VEnv Challenge.EvmProof.modexpExec.toDialect) (state : EvmState)
    (env_xHi : VEnv.get env "\x00136" = some xHi)
    (env_xLo : VEnv.get env "\x00137" = some xLo)
    (env_yHi : VEnv.get env "\x00140" = some yHi)
    (env_yLo : VEnv.get env "\x00141" = some yLo)
    (env_tempHi : VEnv.get env "\x00138" = some tempHi)
    (env_tempLo : VEnv.get env "\x00139" = some tempLo) :
    (makePointAddUnequalPostContext xHi xLo yHi yLo tempHi tempLo env state
      env_xHi env_xLo env_yHi env_yLo env_tempHi env_tempLo).yLo = yLo := by
  rfl

@[simp] theorem makePointAddUnequalPostContext_env
    (xHi xLo yHi yLo tempHi tempLo : U256)
    (env : VEnv Challenge.EvmProof.modexpExec.toDialect) (state : EvmState)
    (env_xHi : VEnv.get env "\x00136" = some xHi)
    (env_xLo : VEnv.get env "\x00137" = some xLo)
    (env_yHi : VEnv.get env "\x00140" = some yHi)
    (env_yLo : VEnv.get env "\x00141" = some yLo)
    (env_tempHi : VEnv.get env "\x00138" = some tempHi)
    (env_tempLo : VEnv.get env "\x00139" = some tempLo) :
    (makePointAddUnequalPostContext xHi xLo yHi yLo tempHi tempLo env state
      env_xHi env_xLo env_yHi env_yLo env_tempHi env_tempLo).env = env := by
  rfl

@[simp] theorem makePointAddUnequalPostContext_state
    (xHi xLo yHi yLo tempHi tempLo : U256)
    (env : VEnv Challenge.EvmProof.modexpExec.toDialect) (state : EvmState)
    (env_xHi : VEnv.get env "\x00136" = some xHi)
    (env_xLo : VEnv.get env "\x00137" = some xLo)
    (env_yHi : VEnv.get env "\x00140" = some yHi)
    (env_yLo : VEnv.get env "\x00141" = some yLo)
    (env_tempHi : VEnv.get env "\x00138" = some tempHi)
    (env_tempLo : VEnv.get env "\x00139" = some tempLo) :
    (makePointAddUnequalPostContext xHi xLo yHi yLo tempHi tempLo env state
      env_xHi env_xLo env_yHi env_yLo env_tempHi env_tempLo).state = state := by
  rfl

def pointAddUnequalPostlude : Block Op := pointAddUnequalCode.drop 13
def pointAddUnequalPostStmt0 : Stmt Op := pointAddUnequalPostlude[0]!
def pointAddUnequalPostStmt1 : Stmt Op := pointAddUnequalPostlude[1]!
def pointAddUnequalPostStmt2 : Stmt Op := pointAddUnequalPostlude[2]!
def pointAddUnequalPostStmt3 : Stmt Op := pointAddUnequalPostlude[3]!
def pointAddUnequalPostStmt4 : Stmt Op := pointAddUnequalPostlude[4]!
def pointAddUnequalPostStmt5 : Stmt Op := pointAddUnequalPostlude[5]!
def pointAddUnequalPostStmt6 : Stmt Op := pointAddUnequalPostlude[6]!
def pointAddUnequalPostStmt7 : Stmt Op := pointAddUnequalPostlude[7]!

theorem pointAddUnequalPostlude_eq : pointAddUnequalPostlude =
    [pointAddUnequalPostStmt0, pointAddUnequalPostStmt1,
     pointAddUnequalPostStmt2, pointAddUnequalPostStmt3,
     pointAddUnequalPostStmt4, pointAddUnequalPostStmt5,
     pointAddUnequalPostStmt6, pointAddUnequalPostStmt7] := by rfl
theorem pointAddUnequalPostStmt0_eq : pointAddUnequalPostStmt0 =
    .letDecl [] none := by rfl
theorem pointAddUnequalPostStmt1_eq : pointAddUnequalPostStmt1 =
    .assign ["\x00138"] (.var "\x00137") := by rfl
theorem pointAddUnequalPostStmt2_eq : pointAddUnequalPostStmt2 =
    .assign ["\x00139"] (.var "\x00136") := by rfl
theorem pointAddUnequalPostStmt3_eq : pointAddUnequalPostStmt3 =
    .assign ["\x00136"]
      (.builtin .mload [.lit (.number 1536)]) := by rfl
theorem pointAddUnequalPostStmt4_eq : pointAddUnequalPostStmt4 =
    .exprStmt (.builtin .mstore
      [.var "\x00136", .var "\x00139"]) := by rfl
theorem pointAddUnequalPostStmt5_eq : pointAddUnequalPostStmt5 =
    .exprStmt (.builtin .mstore
      [.builtin .add [.var "\x00136", .lit (.number 32)],
       .var "\x00138"]) := by rfl
theorem pointAddUnequalPostStmt6_eq : pointAddUnequalPostStmt6 =
    .exprStmt (.builtin .mstore
      [.builtin .add [.var "\x00136", .lit (.number 64)],
       .var "\x00140"]) := by rfl
theorem pointAddUnequalPostStmt7_eq : pointAddUnequalPostStmt7 =
    .exprStmt (.builtin .mstore
      [.builtin .add [.var "\x00136", .lit (.number 96)],
       .var "\x00141"]) := by rfl

def pointAddUnequalPostEnv1 (ctx : PointAddUnequalPostContext) :=
  VEnv.set ctx.env "\x00138" ctx.xLo
def pointAddUnequalPostEnv2 (ctx : PointAddUnequalPostContext) :=
  VEnv.set (pointAddUnequalPostEnv1 ctx) "\x00139" ctx.xHi
def pointAddUnequalPostOut (ctx : PointAddUnequalPostContext) : U256 :=
  loadWord ctx.state.memory 1536
def pointAddUnequalPostEnv (ctx : PointAddUnequalPostContext) :=
  VEnv.set (pointAddUnequalPostEnv2 ctx) "\x00136"
    (pointAddUnequalPostOut ctx)

def pointAddUnequalPostStoreState (yst : EvmState) (offset value : U256) : EvmState :=
  { touchMemory yst offset.toNat 32 with
    memory := storeWord yst.memory offset.toNat value }

def pointAddUnequalPostLoadState (ctx : PointAddUnequalPostContext) : EvmState :=
  touchMemory ctx.state 1536 32
def pointAddUnequalPostState1 (ctx : PointAddUnequalPostContext) : EvmState :=
  pointAddUnequalPostStoreState (pointAddUnequalPostLoadState ctx)
    (pointAddUnequalPostOut ctx) ctx.xHi
def pointAddUnequalPostState2 (ctx : PointAddUnequalPostContext) : EvmState :=
  pointAddUnequalPostStoreState (pointAddUnequalPostState1 ctx)
    (pointAddUnequalPostOut ctx + 32) ctx.xLo
def pointAddUnequalPostState3 (ctx : PointAddUnequalPostContext) : EvmState :=
  pointAddUnequalPostStoreState (pointAddUnequalPostState2 ctx)
    (pointAddUnequalPostOut ctx + 64) ctx.yHi
def pointAddUnequalPostState (ctx : PointAddUnequalPostContext) : EvmState :=
  pointAddUnequalPostStoreState (pointAddUnequalPostState3 ctx)
    (pointAddUnequalPostOut ctx + 96) ctx.yLo

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
