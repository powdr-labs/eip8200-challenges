import YulSemantics.BigStep

set_option warningAsError true

/-! Tiny opaque relational adapters for source variable assignments. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics

theorem step_assignVar {D : Dialect} [DecidableEq D.Value]
    {funs : FunEnv D} {V : VEnv D} {st : D.State}
    {source target : String} {value : D.Value}
    (hget : VEnv.get V source = some value) :
    ExecStmt D funs V st (.assign [target] (.var source))
      (VEnv.set V target value) st .normal :=
  Step.assignVal (Step.var hget) rfl

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
