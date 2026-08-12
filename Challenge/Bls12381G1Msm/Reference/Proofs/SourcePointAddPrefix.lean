import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddDefs
import Challenge.EvmProof.ExecSound

set_option warningAsError true

/-! Relational execution of the three G1MSM `pointAdd` pointer stores. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def pointAddStore (yst : EvmState) (ptr : Nat) (value : U256) : EvmState :=
  { touchMemory yst ptr 32 with memory := storeWord yst.memory ptr value }

def pointAddPrefixState (yst : EvmState) (out left right : U256) : EvmState :=
  pointAddStore (pointAddStore (pointAddStore yst 1536 out) 1568 left)
    1600 right

private theorem exec_pointAddPrefix (yst : EvmState) (out left right : U256) :
    Interp.execStmts Challenge.EvmProof.modexpExec 70 pointAddBodyFuns
      (pointAddInitialEnv out left right) yst
      [pointAddStmt0, pointAddStmt1, pointAddStmt2] =
    .ok (pointAddInitialEnv out left right,
      pointAddPrefixState yst out left right, .normal) := by
  rfl

private theorem soundStmts {n funs V st stmts V' st' outcome}
    (h : Interp.execStmts Challenge.EvmProof.modexpExec n funs V st stmts =
      .ok (V', st', outcome)) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect funs V st stmts
      V' st' outcome :=
  (Interp.sound_all_of (E := Challenge.EvmProof.modexpExec)
    (fun _ _ _ _ hb => Challenge.EvmProof.modexpBuiltinFn_sound hb) n).2.2.2.1
    _ _ _ _ _ _ _ h

theorem step_pointAddPrefix (yst : EvmState) (out left right : U256) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddInitialEnv out left right) yst
      [pointAddStmt0, pointAddStmt1, pointAddStmt2]
      (pointAddInitialEnv out left right)
      (pointAddPrefixState yst out left right) .normal :=
  soundStmts (exec_pointAddPrefix yst out left right)

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
