import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalXSubLeftOutputHi

set_option warningAsError true

/-! Second output assignment and opaque output sequence of the first subtraction. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def pointAddUnequalXSubLeftWorkEnv (yst : EvmState)
    (out left right : U256) : VEnv Challenge.EvmProof.modexpExec.toDialect :=
  VEnv.set (pointAddUnequalXSubLeftHighEnv yst out left right)
    "\x00137" (pointAddUnequalXSubLeftResult yst out left right).2

private theorem get_cons_ne
    {V : VEnv Challenge.EvmProof.modexpExec.toDialect}
    {name target : String} {value : U256} (hne : name ≠ target) :
    VEnv.get ((name, value) :: V) target = VEnv.get V target := by
  simp [VEnv.get, hne]

private theorem get_set_ne {V : VEnv Challenge.EvmProof.modexpExec.toDialect}
    {x y : String} {v : U256} (hxy : x ≠ y) :
    VEnv.get (VEnv.set V x v) y = VEnv.get V y := by
  induction V with
  | nil => rfl
  | cons head tail ih =>
      rcases head with ⟨name, value⟩
      by_cases hname : name = x
      · subst name
        simp [VEnv.set, VEnv.get, hxy]
      · by_cases htarget : name = y
        · subst name
          simp [VEnv.set, VEnv.get, hname]
        · rw [VEnv.set, if_neg hname, get_cons_ne htarget,
            get_cons_ne htarget]
          exact ih

theorem step_pointAddUnequalXSubLeftOutputLoExplicit (yst : EvmState)
    (out left right : U256) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect ([] :: pointAddBodyFuns)
      (pointAddUnequalXSubLeftHighEnv yst out left right)
      (pointAddUnequalXSubLeftRawState yst out left right)
      (.assign ["\x00137"] (.var "fc0_82"))
      (pointAddUnequalXSubLeftWorkEnv yst out left right)
      (pointAddUnequalXSubLeftRawState yst out left right) .normal := by
  have hlo : VEnv.get (pointAddUnequalXSubLeftHighEnv yst out left right)
      "fc0_82" = some (pointAddUnequalXSubLeftResult yst out left right).2 := by
    rw [pointAddUnequalXSubLeftHighEnv, get_set_ne (by decide)]
    exact pointAddUnequalXSubLeftSelectedEnv_lo yst out left right
  exact step_assignVar hlo

theorem step_pointAddUnequalXSubLeftOutputs (yst : EvmState)
    (out left right : U256) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect ([] :: pointAddBodyFuns)
      (pointAddUnequalXSubLeftSelectedEnv yst out left right)
      (pointAddUnequalXSubLeftRawState yst out left right)
      [.assign ["\x00136"] (.var "fc0_81"),
       .assign ["\x00137"] (.var "fc0_82")]
      (pointAddUnequalXSubLeftWorkEnv yst out left right)
      (pointAddUnequalXSubLeftRawState yst out left right) .normal :=
  Step.seqCons (step_pointAddUnequalXSubLeftOutputHiExplicit yst out left right)
    (Step.seqCons (step_pointAddUnequalXSubLeftOutputLoExplicit yst out left right)
      Step.seqNil)

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
