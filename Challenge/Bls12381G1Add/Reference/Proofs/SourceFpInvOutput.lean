import Challenge.Bls12381G1Add.Reference.Proofs.SourceFpInvCall

set_option warningAsError true

/-! # Frozen G1ADD `fpInv` output loads -/

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def fpInvHighEnv (yst : EvmState) (hi lo : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  VEnv.setMany (fpInvInitialEnv hi lo) ["\x0079"]
    [(fpInvResult yst hi lo).1]

def fpInvReturnEnv (yst : EvmState) (hi lo : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  VEnv.setMany (fpInvHighEnv yst hi lo) ["\x0080"]
    [(fpInvResult yst hi lo).2]

/-- The final two source statements load the returned high and low limbs in
their exact order. -/
theorem exec_fpInvOutput (hi lo : U256) (yst : EvmState) :
    Interp.execStmts Challenge.EvmProof.modexpExec 60 fpInvBodyFuns
      (fpInvInitialEnv hi lo) (fpInvCallState yst hi lo)
      [fpInvStmt7, fpInvStmt8] =
    .ok (fpInvReturnEnv yst hi lo, fpInvFinalState yst hi lo, .normal) := by
  rfl

theorem fpInvReturnEnv_hi (yst : EvmState) (hi lo : U256) :
    (VEnv.get (fpInvReturnEnv yst hi lo) "\x0079").getD 0 =
      (fpInvResult yst hi lo).1 := by
  rfl

theorem fpInvReturnEnv_lo (yst : EvmState) (hi lo : U256) :
    (VEnv.get (fpInvReturnEnv yst hi lo) "\x0080").getD 0 =
      (fpInvResult yst hi lo).2 := by
  rfl

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
