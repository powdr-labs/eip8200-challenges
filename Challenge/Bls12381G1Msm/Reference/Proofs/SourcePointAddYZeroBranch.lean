import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddYZero
import Challenge.EvmProof.ExecSound

set_option warningAsError true

/-! Exact store-infinity branch for equal x-coordinates with opposite y-coordinates. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def pointAddYZeroOutPtr (yst : EvmState) (out left right : U256) : U256 :=
  loadWord (pointAddYSumState yst out left right).memory 1536

def pointAddYZeroState1 (yst : EvmState) (out left right : U256) : EvmState :=
  touchMemory (pointAddYSumState yst out left right) 1536 32

def pointAddYZeroState2 (yst : EvmState) (out left right : U256) : EvmState :=
  pointAddStore (pointAddYZeroState1 yst out left right)
    (pointAddYZeroOutPtr yst out left right).toNat 0

def pointAddYZeroState3 (yst : EvmState) (out left right : U256) : EvmState :=
  pointAddStore (pointAddYZeroState2 yst out left right)
    (pointAddYZeroOutPtr yst out left right + 32).toNat 0

def pointAddYZeroState4 (yst : EvmState) (out left right : U256) : EvmState :=
  pointAddStore (pointAddYZeroState3 yst out left right)
    (pointAddYZeroOutPtr yst out left right + 64).toNat 0

def pointAddYZeroState (yst : EvmState) (out left right : U256) : EvmState :=
  pointAddStore (pointAddYZeroState4 yst out left right)
    (pointAddYZeroOutPtr yst out left right + 96).toNat 0

private theorem exec_pointAddYZeroBranch (yst : EvmState) (out left right : U256) :
    Interp.execStmt Challenge.EvmProof.modexpExec 70 pointAddBodyFuns
      (pointAddYSumEnv yst out left right) (pointAddYSumState yst out left right)
      (.block pointAddYZeroBody) =
    .ok (pointAddYSumEnv yst out left right,
      pointAddYZeroState yst out left right, .leave) := by
  rfl

theorem soundPointAddYZeroStmt {n funs V st stmt V' st' outcome}
    (h : Interp.execStmt Challenge.EvmProof.modexpExec n funs V st stmt =
      .ok (V', st', outcome)) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect funs V st stmt
      V' st' outcome :=
  (Interp.sound_all_of (E := Challenge.EvmProof.modexpExec)
    (fun _ _ _ _ hb => Challenge.EvmProof.modexpBuiltinFn_sound hb) n).2.2.1
    _ _ _ _ _ _ _ h

theorem step_pointAddYZeroBranch (yst : EvmState) (out left right : U256)
    (hzero : pointAddYZeroValue yst out left right ≠ 0) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddYSumEnv yst out left right) (pointAddYSumState yst out left right)
      pointAddYZeroStmt (pointAddYSumEnv yst out left right)
      (pointAddYZeroState yst out left right) .leave := by
  rw [pointAddYZeroStmt_eq]
  exact Step.ifTrue (step_pointAddYZero yst out left right) hzero
    (soundPointAddYZeroStmt (exec_pointAddYZeroBranch yst out left right))

theorem step_pointAddYZeroBody (yst : EvmState) (out left right : U256) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddYSumEnv yst out left right) (pointAddYSumState yst out left right)
      (.block pointAddYZeroBody) (pointAddYSumEnv yst out left right)
      (pointAddYZeroState yst out left right) .leave :=
  soundPointAddYZeroStmt (exec_pointAddYZeroBranch yst out left right)

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
