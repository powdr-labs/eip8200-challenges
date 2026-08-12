import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddFiniteEntry
import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddVerticalEqual
import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddDoubleLawful

set_option warningAsError true

/-! Complete frozen point-add execution for finite equal-x branches. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM
open Challenge.Bls12381.ProofSupport

private theorem step_pointAddFullEqualPrefix (yst : EvmState)
    (out left right : U256)
    (hleftFinite : pointAddLeftInfinityValue yst out left right = 0)
    (hrightFinite : pointAddRightInfinityValue yst out left right = 0)
    {Vend : VEnv Challenge.EvmProof.modexpExec.toDialect} {stend : EvmState}
    (hsuffix : ExecStmt Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddInitialEnv out left right)
      (pointAddFiniteState yst out left right) pointAddStmt5 Vend stend .leave) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddInitialEnv out left right) yst pointAddBody Vend stend .leave := by
  rw [show pointAddBody = pointAddFiniteEntryCode ++
      (pointAddStmt5 :: pointAddBody.drop 6) by
    exact (List.take_append_drop 5 pointAddBody).symm]
  exact step_pointAddUnequal_appendNormal
    (step_pointAddFiniteEntry yst out left right hleftFinite hrightFinite)
    (Step.seqStop hsuffix (by decide))

theorem step_pointAddFullVertical (yst : EvmState)
    (out left right : U256)
    (hleftFinite : pointAddLeftInfinityValue yst out left right = 0)
    (hrightFinite : pointAddRightInfinityValue yst out left right = 0)
    (hxeq : pointAddXEqValue yst out left right ≠ 0)
    (hzero : pointAddYZeroValue yst out left right ≠ 0) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddInitialEnv out left right) yst pointAddBody
      (pointAddInitialEnv out left right)
      (pointAddYZeroState yst out left right) .leave :=
  step_pointAddFullEqualPrefix yst out left right hleftFinite hrightFinite
    (step_pointAddVerticalEqual yst out left right hxeq hzero)

theorem step_pointAddFullDouble_lawful (yst : EvmState)
    (out left right : U256)
    (hleftFinite : pointAddLeftInfinityValue yst out left right = 0)
    (hrightFinite : pointAddRightInfinityValue yst out left right = 0)
    (hxeq : pointAddXEqValue yst out left right ≠ 0)
    (hleft : Fp.Canonical (pointAddFiniteLeftYLimbs yst out left right))
    (hright : Fp.Canonical (pointAddFiniteRightYLimbs yst out left right))
    (hdoubleLeft :
      Fp.Canonical (pointAddDoubleLeftYLimbs yst out left right))
    (hsum : Fp.toField (pointAddFiniteLeftYLimbs yst out left right) +
      Fp.toField (pointAddFiniteRightYLimbs yst out left right) ≠ 0) :
    ∃ Vend stend,
      ExecStmts Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
        (pointAddInitialEnv out left right) yst pointAddBody
        Vend stend .leave := by
  obtain ⟨Vend, stend, hsuffix⟩ := step_pointAddDoubleEqual_lawful
    yst out left right hxeq hleft hright hdoubleLeft hsum
  exact ⟨Vend, stend, step_pointAddFullEqualPrefix yst out left right
    hleftFinite hrightFinite hsuffix⟩

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
