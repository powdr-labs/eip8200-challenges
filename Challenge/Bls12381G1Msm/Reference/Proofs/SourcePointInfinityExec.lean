import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointInfinityDefs
import Challenge.EvmProof.ExecSound

set_option warningAsError true

/-! Exact execution of the frozen G1MSM `pointInfinity` helper. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def pointInfinityWords (yst : EvmState) (ptr : U256) :
    U256 × U256 × U256 × U256 :=
  (loadWord yst.memory ptr.toNat,
   loadWord yst.memory (ptr + 32).toNat,
   loadWord yst.memory (ptr + 64).toNat,
   loadWord yst.memory (ptr + 96).toNat)

def pointInfinityResult (yst : EvmState) (ptr : U256) : U256 :=
  let w := pointInfinityWords yst ptr
  fpZeroValue w.1 w.2.1 &&& fpZeroValue w.2.2.1 w.2.2.2

def pointInfinityFinalState (yst : EvmState) (ptr : U256) : EvmState :=
  touchMemory
    (touchMemory
      (touchMemory
        (touchMemory yst (ptr + 96).toNat 32)
        (ptr + 64).toNat 32)
      (ptr + 32).toNat 32)
    ptr.toNat 32

def pointInfinityReturnEnv (yst : EvmState) (ptr : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  VEnv.setMany (pointInfinityInitialEnv ptr) ["\x00106"]
    [pointInfinityResult yst ptr]

private theorem exec_pointInfinityStmt (yst : EvmState) (ptr : U256) :
    Interp.execStmt Challenge.EvmProof.modexpExec 70 pointInfinityBodyFuns
      (pointInfinityInitialEnv ptr) yst pointInfinityStmt =
    .ok (pointInfinityReturnEnv yst ptr,
      pointInfinityFinalState yst ptr, .normal) := by
  rfl

private theorem soundStmt {n funs V st stmt V' st' outcome}
    (h : Interp.execStmt Challenge.EvmProof.modexpExec n funs V st stmt =
      .ok (V', st', outcome)) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect funs V st stmt
      V' st' outcome :=
  (Interp.sound_all_of (E := Challenge.EvmProof.modexpExec)
    (fun _ _ _ _ hb => Challenge.EvmProof.modexpBuiltinFn_sound hb) n).2.2.1
    _ _ _ _ _ _ _ h

theorem step_pointInfinityBody (yst : EvmState) (ptr : U256) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect pointInfinityBodyFuns
      (pointInfinityInitialEnv ptr) yst pointInfinityStmt
      (pointInfinityReturnEnv yst ptr)
      (pointInfinityFinalState yst ptr) .normal :=
  soundStmt (exec_pointInfinityStmt yst ptr)

theorem step_pointInfinity_of_args {funs V st argState args} (ptr : U256)
    (hargs : EvalArgs Challenge.EvmProof.modexpExec.toDialect funs V st args
      (.vals [ptr] argState))
    (hlookup : lookupFun funs "\x0015" =
      some (pointInfinityDecl, sourceFuns)) :
    EvalExpr Challenge.EvmProof.modexpExec.toDialect funs V st
      (.call "\x0015" args)
      (.vals [pointInfinityResult argState ptr]
        (pointInfinityFinalState argState ptr)) := by
  have hseq : ExecStmts Challenge.EvmProof.modexpExec.toDialect
      pointInfinityBodyFuns (pointInfinityInitialEnv ptr) argState
      pointInfinityBody (pointInfinityReturnEnv argState ptr)
      (pointInfinityFinalState argState ptr) .normal := by
    rw [pointInfinityBody_eq]
    exact Step.seqCons (step_pointInfinityBody argState ptr) Step.seqNil
  have hblock : ExecStmt Challenge.EvmProof.modexpExec.toDialect sourceFuns
      (pointInfinityInitialEnv ptr) argState (.block pointInfinityBody)
      (restore (pointInfinityInitialEnv ptr) (pointInfinityReturnEnv argState ptr))
      (pointInfinityFinalState argState ptr) .normal := Step.block hseq
  have hcall := Step.callOk hargs hlookup rfl hblock (Or.inl rfl)
  change EvalExpr Challenge.EvmProof.modexpExec.toDialect funs V st
    (.call "\x0015" args)
    (.vals [(VEnv.get
      (restore (pointInfinityInitialEnv ptr) (pointInfinityReturnEnv argState ptr))
      "\x00106").getD 0] (pointInfinityFinalState argState ptr)) at hcall
  simpa [pointInfinityInitialEnv, pointInfinityReturnEnv, restore,
    VEnv.get, VEnv.setMany, VEnv.set] using hcall

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
