import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalXSubEnvLookup
import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalDeltaFull

set_option warningAsError true

/-! Single concrete bridge from the computed `x3` words to the generic delta proof. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def pointAddUnequalDeltaInitialConcreteEnv (yst : EvmState)
    (out left right : U256) : VEnv Challenge.EvmProof.modexpExec.toDialect :=
  bindZeros Challenge.EvmProof.modexpExec.toDialect ["\x00138", "\x00139"] ++
    pointAddUnequalXSubEnv yst out left right

private theorem pointAddUnequalDeltaInitialConcreteEnv_hi (yst : EvmState)
    (out left right : U256) :
    VEnv.get (pointAddUnequalDeltaInitialConcreteEnv yst out left right)
      "\x00136" = some (pointAddUnequalXSubResult yst out left right).1 := by
  rw [pointAddUnequalDeltaInitialConcreteEnv]
  rw [venv_get_append_of_names_ne _ _ _ (by simp [bindZeros])]
  exact pointAddUnequalXSubEnv_hi yst out left right

private theorem pointAddUnequalDeltaInitialConcreteEnv_lo (yst : EvmState)
    (out left right : U256) :
    VEnv.get (pointAddUnequalDeltaInitialConcreteEnv yst out left right)
      "\x00137" = some (pointAddUnequalXSubResult yst out left right).2 := by
  rw [pointAddUnequalDeltaInitialConcreteEnv]
  rw [venv_get_append_of_names_ne _ _ _ (by simp [bindZeros])]
  exact pointAddUnequalXSubEnv_lo yst out left right

def pointAddUnequalDeltaContext (yst : EvmState)
    (out left right : U256) : PointAddUnequalDeltaContext where
  env := pointAddUnequalDeltaInitialConcreteEnv yst out left right
  state := pointAddUnequalXSubState yst out left right
  x3Hi := (pointAddUnequalXSubResult yst out left right).1
  x3Lo := (pointAddUnequalXSubResult yst out left right).2
  env_hi := pointAddUnequalDeltaInitialConcreteEnv_hi yst out left right
  env_lo := pointAddUnequalDeltaInitialConcreteEnv_lo yst out left right

def pointAddUnequalDeltaConcreteEnv (yst : EvmState)
    (out left right : U256) : VEnv Challenge.EvmProof.modexpExec.toDialect :=
  pointAddUnequalDeltaEnv (pointAddUnequalDeltaContext yst out left right)

def pointAddUnequalDeltaConcreteState (yst : EvmState)
    (out left right : U256) : EvmState :=
  pointAddUnequalDeltaRawState (pointAddUnequalDeltaContext yst out left right)

theorem step_pointAddUnequalDeltaInit (yst : EvmState)
    (out left right : U256) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddUnequalXSubEnv yst out left right)
      (pointAddUnequalXSubState yst out left right)
      pointAddUnequalDeltaInitStmt
      (pointAddUnequalDeltaInitialConcreteEnv yst out left right)
      (pointAddUnequalXSubState yst out left right) .normal := by
  rw [pointAddUnequalDeltaInitStmt_eq]
  simpa [pointAddUnequalDeltaInitialConcreteEnv] using
    (Step.letZero
      (D := Challenge.EvmProof.modexpExec.toDialect)
      (funs := pointAddBodyFuns)
      (V := pointAddUnequalXSubEnv yst out left right)
      (st := pointAddUnequalXSubState yst out left right)
      (vars := ["\x00138", "\x00139"]))

theorem step_pointAddUnequalDeltaInitAndStmt (yst : EvmState)
    (out left right : U256) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddUnequalXSubEnv yst out left right)
      (pointAddUnequalXSubState yst out left right)
      [pointAddUnequalDeltaInitStmt, pointAddUnequalDeltaStmt]
      (pointAddUnequalDeltaConcreteEnv yst out left right)
      (pointAddUnequalDeltaConcreteState yst out left right) .normal := by
  exact Step.seqCons (step_pointAddUnequalDeltaInit yst out left right)
    (Step.seqCons
      (step_pointAddUnequalDeltaGeneric
        (pointAddUnequalDeltaContext yst out left right)) Step.seqNil)

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
