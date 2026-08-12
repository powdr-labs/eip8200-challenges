import Challenge.Bls12381G2Msm.Reference.Proofs.SourceFpInvCall
import Challenge.EvmProof.ExecSound

set_option warningAsError true

/-! Frozen G2MSM `fpInv` output and complete body. -/

namespace Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def fpInvHighEnv (yst : EvmState) (hi lo : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  VEnv.setMany (fpInvInitialEnv hi lo) ["\x0097"]
    [(fpInvResult yst hi lo).1]

def fpInvReturnEnv (yst : EvmState) (hi lo : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  VEnv.setMany (fpInvHighEnv yst hi lo) ["\x0098"]
    [(fpInvResult yst hi lo).2]

theorem exec_fpInvOutput (hi lo : U256) (yst : EvmState) :
    Interp.execStmts Challenge.EvmProof.modexpExec 60 fpInvBodyFuns
      (fpInvInitialEnv hi lo) (fpInvCallState yst hi lo)
      [fpInvStmt7, fpInvStmt8] =
    .ok (fpInvReturnEnv yst hi lo, fpInvFinalState yst hi lo, .normal) := by
  rfl

theorem fpInvReturnEnv_hi (yst : EvmState) (hi lo : U256) :
    (VEnv.get (fpInvReturnEnv yst hi lo) "\x0097").getD 0 =
      (fpInvResult yst hi lo).1 := by
  rfl

theorem fpInvReturnEnv_lo (yst : EvmState) (hi lo : U256) :
    (VEnv.get (fpInvReturnEnv yst hi lo) "\x0098").getD 0 =
      (fpInvResult yst hi lo).2 := by
  rfl

def fpInvBodyResultEnv (yst : EvmState) (hi lo : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  restore (fpInvInitialEnv hi lo) (fpInvReturnEnv yst hi lo)

theorem exec_fpInvBody (hi lo : U256) (yst : EvmState)
    (hhi : hi.toNat < 2 ^ 128) :
    Interp.execStmt Challenge.EvmProof.modexpExec 67 fpInvFuns
      (fpInvInitialEnv hi lo) yst (.block fpInvBody) =
    .ok (fpInvBodyResultEnv yst hi lo, fpInvFinalState yst hi lo,
      .normal) := by
  have hcallOutput :
      Interp.execStmts Challenge.EvmProof.modexpExec 61 fpInvBodyFuns
          (fpInvInitialEnv hi lo) (fpInvInputState yst hi lo)
          [fpInvStmt6, fpInvStmt7, fpInvStmt8] =
        .ok (fpInvReturnEnv yst hi lo, fpInvFinalState yst hi lo,
          .normal) := by
    exact Interp.execStmts_cons_normal
      (exec_fpInvCall hi lo yst hhi) (exec_fpInvOutput hi lo yst)
  have hbody :
      Interp.execStmts Challenge.EvmProof.modexpExec 66 fpInvBodyFuns
          (fpInvInitialEnv hi lo) yst
          [fpInvStmt0, fpInvStmt1, fpInvStmt2, fpInvStmt3, fpInvStmt4,
            fpInvStmt5, fpInvStmt6, fpInvStmt7, fpInvStmt8] =
        .ok (fpInvReturnEnv yst hi lo, fpInvFinalState yst hi lo,
          .normal) := by
    exact Interp.execStmts_append_normal
      (E := Challenge.EvmProof.modexpExec) (n := 60)
      (pre := [fpInvStmt0, fpInvStmt1, fpInvStmt2, fpInvStmt3,
        fpInvStmt4, fpInvStmt5])
      (tail := [fpInvStmt6, fpInvStmt7, fpInvStmt8])
      (by omega) (exec_fpInvStores hi lo yst) hcallOutput
  rw [Interp.execStmt, fpInvBodyFuns_eq, fpInvBody_eq, hbody]
  rfl

theorem fpInvBodyResultEnv_hi (yst : EvmState) (hi lo : U256) :
    (VEnv.get (fpInvBodyResultEnv yst hi lo) "\x0097").getD 0 =
      (fpInvResult yst hi lo).1 := by
  rfl

theorem fpInvBodyResultEnv_lo (yst : EvmState) (hi lo : U256) :
    (VEnv.get (fpInvBodyResultEnv yst hi lo) "\x0098").getD 0 =
      (fpInvResult yst hi lo).2 := by
  rfl

end Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics
