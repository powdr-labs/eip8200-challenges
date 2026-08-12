import Challenge.Bls12381G1Add.Reference.Proofs.SourceFpInvOutput
import Challenge.EvmProof.ExecSound

set_option warningAsError true

/-! # Complete frozen G1ADD `fpInv` body -/

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def fpInvBodyResultEnv (yst : EvmState) (hi lo : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  restore (fpInvInitialEnv hi lo) (fpInvReturnEnv yst hi lo)

/-- The nine independently checked source statements compose to the normally
completed frozen `fpInv` body. -/
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
    (VEnv.get (fpInvBodyResultEnv yst hi lo) "\x0079").getD 0 =
      (fpInvResult yst hi lo).1 := by
  rfl

theorem fpInvBodyResultEnv_lo (yst : EvmState) (hi lo : U256) :
    (VEnv.get (fpInvBodyResultEnv yst hi lo) "\x0080").getD 0 =
      (fpInvResult yst hi lo).2 := by
  rfl

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
