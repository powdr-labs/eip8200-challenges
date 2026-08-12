import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddRightInfinityCond
import Challenge.EvmProof.ExecSound

set_option warningAsError true

/-! Exact right-infinity identity branch of G1MSM `pointAdd`. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def pointAddRightCopyState0 (yst : EvmState) (out left right : U256) : EvmState :=
  pointAddRightInfinityState yst out left right

def pointAddRightCopyLeftPtr (yst : EvmState) (out left right : U256) : U256 :=
  loadWord (pointAddRightCopyState0 yst out left right).memory 1568

def pointAddRightCopyState1 (yst : EvmState) (out left right : U256) : EvmState :=
  touchMemory (pointAddRightCopyState0 yst out left right) 1568 32

def pointAddRightCopyOutPtr (yst : EvmState) (out left right : U256) : U256 :=
  loadWord (pointAddRightCopyState1 yst out left right).memory 1536

def pointAddRightCopyState2 (yst : EvmState) (out left right : U256) : EvmState :=
  touchMemory (pointAddRightCopyState1 yst out left right) 1536 32

def pointAddRightCopyYLo (yst : EvmState) (out left right : U256) : U256 :=
  loadWord (pointAddRightCopyState2 yst out left right).memory
    (pointAddRightCopyLeftPtr yst out left right + 96).toNat

def pointAddRightCopyState3 (yst : EvmState) (out left right : U256) : EvmState :=
  touchMemory (pointAddRightCopyState2 yst out left right)
    (pointAddRightCopyLeftPtr yst out left right + 96).toNat 32

def pointAddRightCopyYHi (yst : EvmState) (out left right : U256) : U256 :=
  loadWord (pointAddRightCopyState3 yst out left right).memory
    (pointAddRightCopyLeftPtr yst out left right + 64).toNat

def pointAddRightCopyState4 (yst : EvmState) (out left right : U256) : EvmState :=
  touchMemory (pointAddRightCopyState3 yst out left right)
    (pointAddRightCopyLeftPtr yst out left right + 64).toNat 32

def pointAddRightCopyXLo (yst : EvmState) (out left right : U256) : U256 :=
  loadWord (pointAddRightCopyState4 yst out left right).memory
    (pointAddRightCopyLeftPtr yst out left right + 32).toNat

def pointAddRightCopyState5 (yst : EvmState) (out left right : U256) : EvmState :=
  touchMemory (pointAddRightCopyState4 yst out left right)
    (pointAddRightCopyLeftPtr yst out left right + 32).toNat 32

def pointAddRightCopyXHi (yst : EvmState) (out left right : U256) : U256 :=
  loadWord (pointAddRightCopyState5 yst out left right).memory
    (pointAddRightCopyLeftPtr yst out left right).toNat

def pointAddRightCopyState6 (yst : EvmState) (out left right : U256) : EvmState :=
  touchMemory (pointAddRightCopyState5 yst out left right)
    (pointAddRightCopyLeftPtr yst out left right).toNat 32

def pointAddRightCopyState7 (yst : EvmState) (out left right : U256) : EvmState :=
  pointAddStore (pointAddRightCopyState6 yst out left right)
    (pointAddRightCopyOutPtr yst out left right).toNat
    (pointAddRightCopyXHi yst out left right)

def pointAddRightCopyState8 (yst : EvmState) (out left right : U256) : EvmState :=
  pointAddStore (pointAddRightCopyState7 yst out left right)
    (pointAddRightCopyOutPtr yst out left right + 32).toNat
    (pointAddRightCopyXLo yst out left right)

def pointAddRightCopyState9 (yst : EvmState) (out left right : U256) : EvmState :=
  pointAddStore (pointAddRightCopyState8 yst out left right)
    (pointAddRightCopyOutPtr yst out left right + 64).toNat
    (pointAddRightCopyYHi yst out left right)

def pointAddRightCopyState (yst : EvmState) (out left right : U256) : EvmState :=
  pointAddStore (pointAddRightCopyState9 yst out left right)
    (pointAddRightCopyOutPtr yst out left right + 96).toNat
    (pointAddRightCopyYLo yst out left right)

def pointAddRightCopyEnv1 (out left right : U256) (rightPtr : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  [("fc1_31", rightPtr)] ++ pointAddInitialEnv out left right

def pointAddRightCopyEnv2 (out left right rightPtr outPtr : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  [("fc1_32", outPtr), ("fc1_31", rightPtr)] ++
    pointAddInitialEnv out left right

def pointAddRightCopyEnv3 (out left right rightPtr outPtr ylo : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  [("fc1_33", ylo), ("fc1_32", outPtr), ("fc1_31", rightPtr)] ++
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

private theorem exec_pointAddRightCopyPrefix (yst : EvmState)
    (out left right : U256) :
    Interp.execStmts Challenge.EvmProof.modexpExec 70
      ([] :: [] :: pointAddBodyFuns)
      (pointAddInitialEnv out left right)
      (pointAddRightCopyState0 yst out left right)
      [pointAddRightCopyStmt0, pointAddRightCopyStmt1,
        pointAddRightCopyStmt2, pointAddRightCopyStmt3,
        pointAddRightCopyStmt4] =
    .ok (pointAddRightCopyEnv3 out left right
        (pointAddRightCopyLeftPtr yst out left right)
        (pointAddRightCopyOutPtr yst out left right)
        (pointAddRightCopyYLo yst out left right),
      pointAddRightCopyState3 yst out left right, .normal) := by
  rfl

private theorem exec_pointAddRightCopyNested (yst : EvmState)
    (out left right : U256) :
    Interp.execStmt Challenge.EvmProof.modexpExec 70
      ([] :: [] :: pointAddBodyFuns)
      (pointAddRightCopyEnv3 out left right
        (pointAddRightCopyLeftPtr yst out left right)
        (pointAddRightCopyOutPtr yst out left right)
        (pointAddRightCopyYLo yst out left right))
      (pointAddRightCopyState3 yst out left right)
      pointAddRightCopyStmt5 =
    .ok (pointAddRightCopyEnv3 out left right
        (pointAddRightCopyLeftPtr yst out left right)
        (pointAddRightCopyOutPtr yst out left right)
        (pointAddRightCopyYLo yst out left right),
      pointAddRightCopyState9 yst out left right, .normal) := by
  rfl

private theorem exec_pointAddRightCopyFinal (yst : EvmState)
    (out left right : U256) :
    Interp.execStmt Challenge.EvmProof.modexpExec 70
      ([] :: [] :: pointAddBodyFuns)
      (pointAddRightCopyEnv3 out left right
        (pointAddRightCopyLeftPtr yst out left right)
        (pointAddRightCopyOutPtr yst out left right)
        (pointAddRightCopyYLo yst out left right))
      (pointAddRightCopyState9 yst out left right)
      pointAddRightCopyStmt6 =
    .ok (pointAddRightCopyEnv3 out left right
        (pointAddRightCopyLeftPtr yst out left right)
        (pointAddRightCopyOutPtr yst out left right)
        (pointAddRightCopyYLo yst out left right),
      pointAddRightCopyState yst out left right, .normal) := by
  rfl

private theorem step_pointAddRightInfinityBlock (yst : EvmState)
    (out left right : U256) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddInitialEnv out left right)
      (pointAddRightInfinityState yst out left right)
      (.block pointAddRightInfinityBody)
      (pointAddInitialEnv out left right)
      (pointAddRightCopyState yst out left right) .leave := by
  have hprefix := soundStmts (exec_pointAddRightCopyPrefix yst out left right)
  have hnested := soundStmt (exec_pointAddRightCopyNested yst out left right)
  have hfinal := soundStmt (exec_pointAddRightCopyFinal yst out left right)
  have hcopySeq : ExecStmts Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns) (pointAddInitialEnv out left right)
      (pointAddRightCopyState0 yst out left right) pointAddRightCopyBody
      (pointAddRightCopyEnv3 out left right
        (pointAddRightCopyLeftPtr yst out left right)
        (pointAddRightCopyOutPtr yst out left right)
        (pointAddRightCopyYLo yst out left right))
      (pointAddRightCopyState yst out left right) .normal := by
    rw [pointAddRightCopyBody_eq]
    exact execStmts_append_normal hprefix
      (Step.seqCons hnested (Step.seqCons hfinal Step.seqNil))
  have hcopy : ExecStmt Challenge.EvmProof.modexpExec.toDialect
      ([] :: pointAddBodyFuns) (pointAddInitialEnv out left right)
      (pointAddRightCopyState0 yst out left right) pointAddRightCopyStmt
      (pointAddInitialEnv out left right)
      (pointAddRightCopyState yst out left right) .normal := by
    rw [pointAddRightCopyStmt_eq]
    have hblock := Step.block (D := Challenge.EvmProof.modexpExec.toDialect)
      (body := pointAddRightCopyBody) hcopySeq
    simpa [restore, pointAddRightCopyEnv3, pointAddInitialEnv] using
      hblock
  rw [pointAddRightInfinityBody_eq]
  exact Step.block (D := Challenge.EvmProof.modexpExec.toDialect)
    (body := [pointAddRightCopyStmt, .leave])
    (Step.seqCons hcopy (Step.seqStop Step.leave (by decide)))

theorem step_pointAddRightInfinity (yst : EvmState) (out left right : U256)
    (hinfinity : pointInfinityResult
      (pointAddRightPointerState yst out left right)
      (pointAddRightPointer yst out left right) ≠ 0) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddInitialEnv out left right)
      (pointAddLeftInfinityState yst out left right) pointAddStmt4
      (pointAddInitialEnv out left right)
      (pointAddRightCopyState yst out left right) .leave := by
  rw [pointAddStmt4_eq]
  exact Step.ifTrue (step_pointAddRightInfinityCondition yst out left right)
    hinfinity (step_pointAddRightInfinityBlock yst out left right)

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
