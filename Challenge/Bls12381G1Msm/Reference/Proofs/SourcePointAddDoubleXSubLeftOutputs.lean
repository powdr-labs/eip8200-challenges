import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddDoubleXSubLeftOutputHi

set_option warningAsError true

/-! Second output assignment and opaque output sequence of the first subtraction. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def pointAddDoubleXSubLeftWorkEnv (yst : EvmState)
    (out left right : U256) : VEnv Challenge.EvmProof.modexpExec.toDialect :=
  VEnv.set (pointAddDoubleXSubLeftHighEnv yst out left right)
    "\x00123" (pointAddDoubleXSubLeftResult yst out left right).2

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

theorem step_pointAddDoubleXSubLeftOutputLoExplicit (yst : EvmState)
    (out left right : U256) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect ([] :: pointAddBodyFuns)
      (pointAddDoubleXSubLeftHighEnv yst out left right)
      (pointAddDoubleXSubLeftRawState yst out left right)
      (.assign ["\x00123"] (.var "fc0_29"))
      (pointAddDoubleXSubLeftWorkEnv yst out left right)
      (pointAddDoubleXSubLeftRawState yst out left right) .normal := by
  have hlo : VEnv.get (pointAddDoubleXSubLeftHighEnv yst out left right)
      "fc0_29" = some (pointAddDoubleXSubLeftResult yst out left right).2 := by
    rw [pointAddDoubleXSubLeftHighEnv, get_set_ne (by decide)]
    exact pointAddDoubleXSubLeftSelectedEnv_lo yst out left right
  exact step_assignVar hlo

theorem step_pointAddDoubleXSubLeftOutputs (yst : EvmState)
    (out left right : U256) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect ([] :: pointAddBodyFuns)
      (pointAddDoubleXSubLeftSelectedEnv yst out left right)
      (pointAddDoubleXSubLeftRawState yst out left right)
      [.assign ["\x00122"] (.var "fc0_28"),
       .assign ["\x00123"] (.var "fc0_29")]
      (pointAddDoubleXSubLeftWorkEnv yst out left right)
      (pointAddDoubleXSubLeftRawState yst out left right) .normal :=
  Step.seqCons (step_pointAddDoubleXSubLeftOutputHiExplicit yst out left right)
    (Step.seqCons (step_pointAddDoubleXSubLeftOutputLoExplicit yst out left right)
      Step.seqNil)

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
