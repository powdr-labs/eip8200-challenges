import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalInvBase
import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalDenominatorEnvEq

set_option warningAsError true

/-! Concrete prefix of the optimizer-inlined unequal-denominator inversion. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def pointAddUnequalInvInitialEnv (yst : EvmState)
    (out left right : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  bindZeros Challenge.EvmProof.modexpExec.toDialect ["\x00132", "\x00133"] ++
    pointAddUnequalDenominatorEnv yst out left right

def pointAddUnequalInvWorkEnv (yst : EvmState)
    (out left right : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  pointAddUnequalInvGenericWorkEnv
    (pointAddUnequalNumeratorEnv yst out left right)
    (pointAddUnequalDenominatorResult yst out left right).1
    (pointAddUnequalDenominatorResult yst out left right).2

def pointAddUnequalInvInputState (yst : EvmState)
    (out left right : U256) : EvmState :=
  pointAddUnequalInvInputStateGeneric
    (pointAddUnequalNumeratorInputsState yst out left right)
    (pointAddUnequalDenominatorResult yst out left right).1
    (pointAddUnequalDenominatorResult yst out left right).2

theorem pointAddUnequalInvInitialEnv_eq (yst : EvmState)
    (out left right : U256) :
    pointAddUnequalInvInitialEnv yst out left right =
      pointAddUnequalInvGenericEnv
        (pointAddUnequalNumeratorEnv yst out left right)
        (pointAddUnequalDenominatorResult yst out left right).1
        (pointAddUnequalDenominatorResult yst out left right).2 := by
  rw [pointAddUnequalInvInitialEnv, pointAddUnequalDenominatorEnv_eq]
  rfl

theorem step_pointAddUnequalInvInit (yst : EvmState)
    (out left right : U256) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddUnequalDenominatorEnv yst out left right)
      (pointAddUnequalNumeratorInputsState yst out left right)
      pointAddUnequalInvInitStmt
      (pointAddUnequalInvInitialEnv yst out left right)
      (pointAddUnequalNumeratorInputsState yst out left right) .normal := by
  rw [pointAddUnequalInvInitStmt_eq]
  simpa [pointAddUnequalInvInitialEnv] using
    (Step.letZero (D := Challenge.EvmProof.modexpExec.toDialect)
      (funs := pointAddBodyFuns)
      (V := pointAddUnequalDenominatorEnv yst out left right)
      (st := pointAddUnequalNumeratorInputsState yst out left right)
      (vars := ["\x00132", "\x00133"]))

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

theorem step_pointAddUnequalInvPrefix (yst : EvmState)
    (out left right : U256) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect
      ([] :: pointAddBodyFuns)
      (pointAddUnequalInvInitialEnv yst out left right)
      (pointAddUnequalNumeratorInputsState yst out left right)
      [pointAddUnequalInvStmt0, pointAddUnequalInvStmt1,
        pointAddUnequalInvStmt2, pointAddUnequalInvStmt3,
        pointAddUnequalInvStmt4, pointAddUnequalInvStmt5,
        pointAddUnequalInvStmt6, pointAddUnequalInvStmt7,
        pointAddUnequalInvStmt8]
      (pointAddUnequalInvWorkEnv yst out left right)
      (pointAddUnequalInvInputState yst out left right) .normal := by
  rw [pointAddUnequalInvInitialEnv_eq]
  exact Step.seqCons
    (soundStmt (exec_pointAddUnequalInvVarsGeneric
      (pointAddUnequalNumeratorEnv yst out left right)
      (pointAddUnequalDenominatorResult yst out left right).1
      (pointAddUnequalDenominatorResult yst out left right).2
      (pointAddUnequalNumeratorInputsState yst out left right)))
    (Step.seqCons
      (step_pointAddUnequalInvBaseGeneric
        (pointAddUnequalNumeratorEnv yst out left right)
        (pointAddUnequalDenominatorResult yst out left right).1
        (pointAddUnequalDenominatorResult yst out left right).2
        (pointAddUnequalNumeratorInputsState yst out left right))
      (soundStmts (exec_pointAddUnequalInvFixedGeneric
        (pointAddUnequalNumeratorEnv yst out left right)
        (pointAddUnequalDenominatorResult yst out left right).1
        (pointAddUnequalDenominatorResult yst out left right).2
        (pointAddUnequalNumeratorInputsState yst out left right))))

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
