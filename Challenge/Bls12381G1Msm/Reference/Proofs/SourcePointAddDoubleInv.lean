import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddDoubleDenCall
import Challenge.Bls12381G1Add.Reference.Proofs.SourceFpInvCall

set_option warningAsError true

/-! Frozen prefix of the optimizer-inlined inversion in point doubling. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def pointAddDoubleInvInitialEnv (yst : EvmState) (out left right : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  bindZeros Challenge.EvmProof.modexpExec.toDialect ["\x00118", "\x00119"] ++
    pointAddDoubleDenEnv yst out left right

def pointAddDoubleInvWorkEnv (yst : EvmState) (out left right : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  bindZeros Challenge.EvmProof.modexpExec.toDialect ["fc2_1", "fc2_2"] ++
    pointAddDoubleInvInitialEnv yst out left right

def pointAddDoubleInvInputState (yst : EvmState) (out left right : U256) : EvmState :=
  Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpInvInputState
    (pointAddDoubleDenArgsState yst out left right)
    (pointAddDoubleDenResult yst out left right).1
    (pointAddDoubleDenResult yst out left right).2

theorem exec_pointAddDoubleInvInit (yst : EvmState) (out left right : U256) :
    Interp.execStmt Challenge.EvmProof.modexpExec 70 pointAddBodyFuns
      (pointAddDoubleDenEnv yst out left right)
      (pointAddDoubleDenArgsState yst out left right)
      pointAddDoubleInvInitStmt =
    .ok (pointAddDoubleInvInitialEnv yst out left right,
      pointAddDoubleDenArgsState yst out left right, .normal) := by
  rfl

theorem exec_pointAddDoubleInvPrefix (yst : EvmState) (out left right : U256) :
    Interp.execStmts Challenge.EvmProof.modexpExec 70
      ([] :: pointAddBodyFuns)
      (pointAddDoubleInvInitialEnv yst out left right)
      (pointAddDoubleDenArgsState yst out left right)
      [pointAddDoubleInvStmt0, pointAddDoubleInvStmt1,
        pointAddDoubleInvStmt2, pointAddDoubleInvStmt3,
        pointAddDoubleInvStmt4, pointAddDoubleInvStmt5,
        pointAddDoubleInvStmt6, pointAddDoubleInvStmt7,
        pointAddDoubleInvStmt8] =
    .ok (pointAddDoubleInvWorkEnv yst out left right,
      pointAddDoubleInvInputState yst out left right, .normal) := by
  rfl

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
