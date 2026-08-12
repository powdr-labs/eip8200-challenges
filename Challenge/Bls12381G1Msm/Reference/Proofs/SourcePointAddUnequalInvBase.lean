import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalInv
import Challenge.EvmProof.ExecSound

set_option warningAsError true

/-! Relational firebreak for the nested base stores in unequal inversion. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def pointAddUnequalInvBaseBody : Block Op :=
  match pointAddUnequalInvStmt1 with
  | .block body => body
  | _ => []

def pointAddUnequalInvBaseStmt0 : Stmt Op := pointAddUnequalInvBaseBody[0]!
def pointAddUnequalInvBaseStmt1 : Stmt Op := pointAddUnequalInvBaseBody[1]!
def pointAddUnequalInvBaseStmt2 : Stmt Op := pointAddUnequalInvBaseBody[2]!

def pointAddUnequalInvBaseInnerBody : Block Op :=
  match pointAddUnequalInvBaseStmt1 with
  | .block body => body
  | _ => []

theorem pointAddUnequalInvBaseBody_eq : pointAddUnequalInvBaseBody =
    [pointAddUnequalInvBaseStmt0, pointAddUnequalInvBaseStmt1,
      pointAddUnequalInvBaseStmt2] := by rfl

theorem pointAddUnequalInvBaseStmt0_eq : pointAddUnequalInvBaseStmt0 =
    .letDecl ["fc2_9"] (some (.var "\x00131")) := by rfl

theorem pointAddUnequalInvBaseStmt1_eq : pointAddUnequalInvBaseStmt1 =
    .block pointAddUnequalInvBaseInnerBody := by rfl

theorem pointAddUnequalInvBaseInnerBody_eq : pointAddUnequalInvBaseInnerBody =
    [.letDecl ["fc2_10"] (some (.var "\x00130")),
     .exprStmt (.builtin .mstore
      [.lit (.number 1024), .lit (.number 48)]),
     .exprStmt (.builtin .mstore
      [.lit (.number 1056), .lit (.number 48)]),
     .exprStmt (.builtin .mstore
      [.lit (.number 1088), .lit (.number 48)]),
     .letDecl [] none,
     .exprStmt (.builtin .mstore
      [.lit (.number 1120),
       .builtin .shl [.lit (.number 128), .var "fc2_10"]])] := by rfl

theorem hoist_pointAddUnequalInvBaseInnerBody :
    hoist Challenge.EvmProof.modexpExec.toDialect
      pointAddUnequalInvBaseInnerBody = [] := by rfl

theorem hoist_pointAddUnequalInvBaseBody :
    hoist Challenge.EvmProof.modexpExec.toDialect
      pointAddUnequalInvBaseBody = [] := by rfl

theorem pointAddUnequalInvBaseStmt2_eq : pointAddUnequalInvBaseStmt2 =
    .exprStmt (.builtin .mstore
      [.lit (.number 1136), .var "fc2_9"]) := by rfl

def pointAddUnequalInvLoEnv
    (tail : VEnv Challenge.EvmProof.modexpExec.toDialect)
    (hi lo : U256) :=
  ("fc2_9", lo) :: pointAddUnequalInvGenericWorkEnv tail hi lo

def pointAddUnequalInvHiEnv
    (tail : VEnv Challenge.EvmProof.modexpExec.toDialect)
    (hi lo : U256) :=
  ("fc2_10", hi) :: pointAddUnequalInvLoEnv tail hi lo

def pointAddUnequalInvHiState (yst : EvmState) (hi : U256) : EvmState :=
  pointAddUnequalInvMstoreState (pointAddUnequalInvHeaderState yst)
    1120 (hi <<< 128)

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

private theorem exec_varsLo (tail : VEnv Challenge.EvmProof.modexpExec.toDialect)
    (hi lo : U256) (yst : EvmState) :
    Interp.execStmt Challenge.EvmProof.modexpExec 70
      ([] :: [] :: pointAddBodyFuns)
      (pointAddUnequalInvGenericWorkEnv tail hi lo) yst
      pointAddUnequalInvBaseStmt0 =
    .ok (pointAddUnequalInvLoEnv tail hi lo, yst, .normal) := by
  rw [pointAddUnequalInvBaseStmt0_eq]
  rfl

private theorem exec_inner (tail : VEnv Challenge.EvmProof.modexpExec.toDialect)
    (hi lo : U256) (yst : EvmState) :
    Interp.execStmts Challenge.EvmProof.modexpExec 70
      ([] :: [] :: [] :: pointAddBodyFuns)
      (pointAddUnequalInvLoEnv tail hi lo) yst
      pointAddUnequalInvBaseInnerBody =
    .ok (pointAddUnequalInvHiEnv tail hi lo,
      pointAddUnequalInvHiState yst hi, .normal) := by
  rw [pointAddUnequalInvBaseInnerBody_eq]
  rfl

private theorem exec_storeLo
    (tail : VEnv Challenge.EvmProof.modexpExec.toDialect)
    (hi lo : U256) (yst : EvmState) :
    Interp.execStmt Challenge.EvmProof.modexpExec 70
      ([] :: [] :: pointAddBodyFuns)
      (pointAddUnequalInvLoEnv tail hi lo)
      (pointAddUnequalInvHiState yst hi)
      pointAddUnequalInvBaseStmt2 =
    .ok (pointAddUnequalInvLoEnv tail hi lo,
      pointAddUnequalInvBaseState yst hi lo, .normal) := by
  rw [pointAddUnequalInvBaseStmt2_eq]
  rfl

theorem step_pointAddUnequalInvBaseGeneric
    (tail : VEnv Challenge.EvmProof.modexpExec.toDialect)
    (hi lo : U256) (yst : EvmState) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect
      ([] :: pointAddBodyFuns)
      (pointAddUnequalInvGenericWorkEnv tail hi lo) yst
      pointAddUnequalInvStmt1
      (pointAddUnequalInvGenericWorkEnv tail hi lo)
      (pointAddUnequalInvBaseState yst hi lo) .normal := by
  have hinner : ExecStmt Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns)
      (pointAddUnequalInvLoEnv tail hi lo) yst
      pointAddUnequalInvBaseStmt1
      (pointAddUnequalInvLoEnv tail hi lo)
      (pointAddUnequalInvHiState yst hi) .normal := by
    rw [pointAddUnequalInvBaseStmt1_eq]
    have hseq := soundStmts (exec_inner tail hi lo yst)
    have hseq' : ExecStmts Challenge.EvmProof.modexpExec.toDialect
        (hoist Challenge.EvmProof.modexpExec.toDialect
          pointAddUnequalInvBaseInnerBody :: [] :: [] :: pointAddBodyFuns)
        (pointAddUnequalInvLoEnv tail hi lo) yst
        pointAddUnequalInvBaseInnerBody
        (pointAddUnequalInvHiEnv tail hi lo)
        (pointAddUnequalInvHiState yst hi) .normal := by
      rw [hoist_pointAddUnequalInvBaseInnerBody]
      exact hseq
    have hblock := Step.block hseq'
    have hrestore : @restore Challenge.EvmProof.modexpExec.toDialect
        (pointAddUnequalInvLoEnv tail hi lo)
        (pointAddUnequalInvHiEnv tail hi lo) =
        pointAddUnequalInvLoEnv tail hi lo := by
      simpa [pointAddUnequalInvHiEnv] using
        (@restore_append_of_length_eq
          Challenge.EvmProof.modexpExec.toDialect
          (pointAddUnequalInvLoEnv tail hi lo)
          [("fc2_10", hi)] (pointAddUnequalInvLoEnv tail hi lo) rfl)
    rw [hrestore] at hblock
    exact hblock
  have hbody : ExecStmts Challenge.EvmProof.modexpExec.toDialect
      ([] :: [] :: pointAddBodyFuns)
      (pointAddUnequalInvGenericWorkEnv tail hi lo) yst
      pointAddUnequalInvBaseBody
      (pointAddUnequalInvLoEnv tail hi lo)
      (pointAddUnequalInvBaseState yst hi lo) .normal := by
    rw [pointAddUnequalInvBaseBody_eq]
    exact Step.seqCons (soundStmt (exec_varsLo tail hi lo yst))
      (Step.seqCons hinner
        (Step.seqCons (soundStmt (exec_storeLo tail hi lo yst)) Step.seqNil))
  rw [pointAddUnequalInvStmt1_eq]
  have hbody' : ExecStmts Challenge.EvmProof.modexpExec.toDialect
      (hoist Challenge.EvmProof.modexpExec.toDialect
        pointAddUnequalInvBaseBody :: [] :: pointAddBodyFuns)
      (pointAddUnequalInvGenericWorkEnv tail hi lo) yst
      pointAddUnequalInvBaseBody
      (pointAddUnequalInvLoEnv tail hi lo)
      (pointAddUnequalInvBaseState yst hi lo) .normal := by
    rw [hoist_pointAddUnequalInvBaseBody]
    exact hbody
  have hblock := Step.block hbody'
  have hrestore : @restore Challenge.EvmProof.modexpExec.toDialect
      (pointAddUnequalInvGenericWorkEnv tail hi lo)
      (pointAddUnequalInvLoEnv tail hi lo) =
      pointAddUnequalInvGenericWorkEnv tail hi lo := by
    simpa [pointAddUnequalInvLoEnv] using
      (@restore_append_of_length_eq
        Challenge.EvmProof.modexpExec.toDialect
        (pointAddUnequalInvGenericWorkEnv tail hi lo)
        [("fc2_9", lo)] (pointAddUnequalInvGenericWorkEnv tail hi lo) rfl)
  rw [hrestore] at hblock
  exact hblock

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
