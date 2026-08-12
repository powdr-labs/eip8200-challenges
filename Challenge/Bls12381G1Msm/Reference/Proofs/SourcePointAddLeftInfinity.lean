import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddLeftInfinityCond
import Challenge.EvmProof.ExecSound

set_option warningAsError true

/-! Exact left-infinity identity branch of G1MSM `pointAdd`. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def pointAddLeftCopyState0 (yst : EvmState) (out left right : U256) : EvmState :=
  pointAddLeftInfinityState yst out left right

def pointAddLeftCopyRightPtr (yst : EvmState) (out left right : U256) : U256 :=
  loadWord (pointAddLeftCopyState0 yst out left right).memory 1600

def pointAddLeftCopyState1 (yst : EvmState) (out left right : U256) : EvmState :=
  touchMemory (pointAddLeftCopyState0 yst out left right) 1600 32

def pointAddLeftCopyOutPtr (yst : EvmState) (out left right : U256) : U256 :=
  loadWord (pointAddLeftCopyState1 yst out left right).memory 1536

def pointAddLeftCopyState2 (yst : EvmState) (out left right : U256) : EvmState :=
  touchMemory (pointAddLeftCopyState1 yst out left right) 1536 32

def pointAddLeftCopyYLo (yst : EvmState) (out left right : U256) : U256 :=
  loadWord (pointAddLeftCopyState2 yst out left right).memory
    (pointAddLeftCopyRightPtr yst out left right + 96).toNat

def pointAddLeftCopyState3 (yst : EvmState) (out left right : U256) : EvmState :=
  touchMemory (pointAddLeftCopyState2 yst out left right)
    (pointAddLeftCopyRightPtr yst out left right + 96).toNat 32

def pointAddLeftCopyYHi (yst : EvmState) (out left right : U256) : U256 :=
  loadWord (pointAddLeftCopyState3 yst out left right).memory
    (pointAddLeftCopyRightPtr yst out left right + 64).toNat

def pointAddLeftCopyState4 (yst : EvmState) (out left right : U256) : EvmState :=
  touchMemory (pointAddLeftCopyState3 yst out left right)
    (pointAddLeftCopyRightPtr yst out left right + 64).toNat 32

def pointAddLeftCopyXLo (yst : EvmState) (out left right : U256) : U256 :=
  loadWord (pointAddLeftCopyState4 yst out left right).memory
    (pointAddLeftCopyRightPtr yst out left right + 32).toNat

def pointAddLeftCopyState5 (yst : EvmState) (out left right : U256) : EvmState :=
  touchMemory (pointAddLeftCopyState4 yst out left right)
    (pointAddLeftCopyRightPtr yst out left right + 32).toNat 32

def pointAddLeftCopyXHi (yst : EvmState) (out left right : U256) : U256 :=
  loadWord (pointAddLeftCopyState5 yst out left right).memory
    (pointAddLeftCopyRightPtr yst out left right).toNat

def pointAddLeftCopyState6 (yst : EvmState) (out left right : U256) : EvmState :=
  touchMemory (pointAddLeftCopyState5 yst out left right)
    (pointAddLeftCopyRightPtr yst out left right).toNat 32

def pointAddLeftCopyState7 (yst : EvmState) (out left right : U256) : EvmState :=
  pointAddStore (pointAddLeftCopyState6 yst out left right)
    (pointAddLeftCopyOutPtr yst out left right).toNat
    (pointAddLeftCopyXHi yst out left right)

def pointAddLeftCopyState8 (yst : EvmState) (out left right : U256) : EvmState :=
  pointAddStore (pointAddLeftCopyState7 yst out left right)
    (pointAddLeftCopyOutPtr yst out left right + 32).toNat
    (pointAddLeftCopyXLo yst out left right)

def pointAddLeftCopyState9 (yst : EvmState) (out left right : U256) : EvmState :=
  pointAddStore (pointAddLeftCopyState8 yst out left right)
    (pointAddLeftCopyOutPtr yst out left right + 64).toNat
    (pointAddLeftCopyYHi yst out left right)

def pointAddLeftCopyState (yst : EvmState) (out left right : U256) : EvmState :=
  pointAddStore (pointAddLeftCopyState9 yst out left right)
    (pointAddLeftCopyOutPtr yst out left right + 96).toNat
    (pointAddLeftCopyYLo yst out left right)

def pointAddLeftCopyEnv1 (out left right : U256) (rightPtr : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  [("fc1_19", rightPtr)] ++ pointAddInitialEnv out left right

def pointAddLeftCopyEnv2 (out left right rightPtr outPtr : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  [("fc1_20", outPtr), ("fc1_19", rightPtr)] ++
    pointAddInitialEnv out left right

def pointAddLeftCopyEnv3 (out left right rightPtr outPtr ylo : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  [("fc1_21", ylo), ("fc1_20", outPtr), ("fc1_19", rightPtr)] ++
    pointAddInitialEnv out left right

private theorem soundStmt {n funs V st stmt V' st' outcome}
    (h : Interp.execStmt Challenge.EvmProof.modexpExec n funs V st stmt =
      .ok (V', st', outcome)) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect funs V st stmt
      V' st' outcome :=
  (Interp.sound_all_of (E := Challenge.EvmProof.modexpExec)
    (fun _ _ _ _ hb => Challenge.EvmProof.modexpBuiltinFn_sound hb) n).2.2.1
    _ _ _ _ _ _ _ h

private theorem soundStmts {n funs V st stmts V' st' outcome}
    (h : Interp.execStmts Challenge.EvmProof.modexpExec n funs V st stmts =
      .ok (V', st', outcome)) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect funs V st stmts
      V' st' outcome :=
  (Interp.sound_all_of (E := Challenge.EvmProof.modexpExec)
    (fun _ _ _ _ hb => Challenge.EvmProof.modexpBuiltinFn_sound hb) n).2.2.2.1
    _ _ _ _ _ _ _ h

private theorem execStmts_append_normal {funs V st xs Vmid stmid ys Vend stend o}
    (hprefix : ExecStmts Challenge.EvmProof.modexpExec.toDialect funs V st
      xs Vmid stmid .normal)
    (hsuffix : ExecStmts Challenge.EvmProof.modexpExec.toDialect funs Vmid stmid
      ys Vend stend o) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect funs V st
      (xs ++ ys) Vend stend o := by
  induction xs generalizing V st with
  | nil =>
      cases hprefix
      simpa using hsuffix
  | cons head tail ih =>
      cases hprefix with
      | seqCons hhead htail =>
          exact Step.seqCons hhead (ih htail)
      | seqStop _ hnot => exact False.elim (hnot rfl)

private theorem exec_pointAddLeftCopyPrefix (yst : EvmState)
    (out left right : U256) :
    Interp.execStmts Challenge.EvmProof.modexpExec 70
      ([] :: [] :: pointAddBodyFuns)
      (pointAddInitialEnv out left right)
      (pointAddLeftCopyState0 yst out left right)
      [pointAddLeftCopyStmt0, pointAddLeftCopyStmt1,
        pointAddLeftCopyStmt2, pointAddLeftCopyStmt3,
        pointAddLeftCopyStmt4] =
    .ok (pointAddLeftCopyEnv3 out left right
        (pointAddLeftCopyRightPtr yst out left right)
        (pointAddLeftCopyOutPtr yst out left right)
        (pointAddLeftCopyYLo yst out left right),
      pointAddLeftCopyState3 yst out left right, .normal) := by
  rfl

private theorem exec_pointAddLeftCopyNested (yst : EvmState)
    (out left right : U256) :
    Interp.execStmt Challenge.EvmProof.modexpExec 70
      ([] :: [] :: pointAddBodyFuns)
      (pointAddLeftCopyEnv3 out left right
        (pointAddLeftCopyRightPtr yst out left right)
        (pointAddLeftCopyOutPtr yst out left right)
        (pointAddLeftCopyYLo yst out left right))
      (pointAddLeftCopyState3 yst out left right)
      pointAddLeftCopyStmt5 =
    .ok (pointAddLeftCopyEnv3 out left right
        (pointAddLeftCopyRightPtr yst out left right)
        (pointAddLeftCopyOutPtr yst out left right)
        (pointAddLeftCopyYLo yst out left right),
      pointAddLeftCopyState9 yst out left right, .normal) := by
  rfl

private theorem exec_pointAddLeftCopyFinal (yst : EvmState)
    (out left right : U256) :
    Interp.execStmt Challenge.EvmProof.modexpExec 70
      ([] :: [] :: pointAddBodyFuns)
      (pointAddLeftCopyEnv3 out left right
        (pointAddLeftCopyRightPtr yst out left right)
        (pointAddLeftCopyOutPtr yst out left right)
        (pointAddLeftCopyYLo yst out left right))
      (pointAddLeftCopyState9 yst out left right)
      pointAddLeftCopyStmt6 =
    .ok (pointAddLeftCopyEnv3 out left right
        (pointAddLeftCopyRightPtr yst out left right)
        (pointAddLeftCopyOutPtr yst out left right)
        (pointAddLeftCopyYLo yst out left right),
      pointAddLeftCopyState yst out left right, .normal) := by
  rfl

private theorem step_pointAddLeftInfinityBlock (yst : EvmState)
    (out left right : U256) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddInitialEnv out left right)
      (pointAddLeftInfinityState yst out left right)
      (.block pointAddLeftInfinityBody)
      (pointAddInitialEnv out left right)
      (pointAddLeftCopyState yst out left right) .leave := by
  have hprefix := soundStmts (exec_pointAddLeftCopyPrefix yst out left right)
  have hnested := soundStmt (exec_pointAddLeftCopyNested yst out left right)
  have hfinal := soundStmt (exec_pointAddLeftCopyFinal yst out left right)
  have hcopySeq : ExecStmts Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) (pointAddInitialEnv out left right)
      (pointAddLeftCopyState0 yst out left right) pointAddLeftCopyBody
      (pointAddLeftCopyEnv3 out left right
        (pointAddLeftCopyRightPtr yst out left right)
        (pointAddLeftCopyOutPtr yst out left right)
        (pointAddLeftCopyYLo yst out left right))
      (pointAddLeftCopyState yst out left right) .normal := by
    rw [pointAddLeftCopyBody_eq]
    exact execStmts_append_normal hprefix
      (Step.seqCons hnested (Step.seqCons hfinal Step.seqNil))
  have hcopy : ExecStmt Challenge.EvmProof.modexpExec.toDialect
      ([] :: pointAddBodyFuns) (pointAddInitialEnv out left right)
      (pointAddLeftCopyState0 yst out left right) pointAddLeftCopyStmt
      (pointAddInitialEnv out left right)
      (pointAddLeftCopyState yst out left right) .normal := by
    rw [pointAddLeftCopyStmt_eq]
    have hblock := Step.block (D := Challenge.EvmProof.modexpExec.toDialect)
      (body := pointAddLeftCopyBody) hcopySeq
    simpa [restore, pointAddLeftCopyEnv3, pointAddInitialEnv] using
      hblock
  rw [pointAddLeftInfinityBody_eq]
  exact Step.block (D := Challenge.EvmProof.modexpExec.toDialect)
    (body := [pointAddLeftCopyStmt, .leave])
    (Step.seqCons hcopy (Step.seqStop Step.leave (by decide)))

theorem step_pointAddLeftInfinity (yst : EvmState) (out left right : U256)
    (hinfinity : pointInfinityResult
      (pointAddLeftPointerState yst out left right)
      (pointAddLeftPointer yst out left right) ≠ 0) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddInitialEnv out left right)
      (pointAddPrefixState yst out left right) pointAddStmt3
      (pointAddInitialEnv out left right)
      (pointAddLeftCopyState yst out left right) .leave := by
  rw [pointAddStmt3_eq]
  exact Step.ifTrue (step_pointAddLeftInfinityCondition yst out left right)
    hinfinity (step_pointAddLeftInfinityBlock yst out left right)

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
