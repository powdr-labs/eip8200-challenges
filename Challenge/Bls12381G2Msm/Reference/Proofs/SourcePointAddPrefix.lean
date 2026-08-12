import Challenge.Bls12381G2Msm.Reference.Proofs.SourcePointAddDefs
import Challenge.EvmProof.ExecSound

set_option warningAsError true

/-! Pointer-storage prefix of G2MSM `pointAdd`. -/

namespace Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

private def storePointer (yst : EvmState) (offset : Nat) (value : U256) :
    EvmState :=
  { touchMemory yst offset 32 with memory := storeWord yst.memory offset value }

def pointAddPrefixState (yst : EvmState) (out left right : U256) : EvmState :=
  storePointer (storePointer (storePointer yst 1920 out) 1952 left) 1984 right

/-- The pointer prefix changes exactly its three low memory words. -/
theorem pointAddPrefixState_memory (yst : EvmState) (out left right : U256) :
    (pointAddPrefixState yst out left right).memory =
      storeWord (storeWord (storeWord yst.memory 1920 out) 1952 left)
        1984 right := by
  rfl

private theorem exec_pointAddPrefix (yst : EvmState) (out left right : U256) :
    Interp.execStmts Challenge.EvmProof.modexpExec 70 pointAddBodyFuns
      (pointAddInitialEnv out left right) yst
      [pointAddStmt0, pointAddStmt1, pointAddStmt2] =
    .ok (pointAddInitialEnv out left right,
      pointAddPrefixState yst out left right, .normal) := by rfl

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

end Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics
