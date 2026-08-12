import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddDoubleXSubEnvLookup
import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddDoubleDeltaFull

set_option warningAsError true

/-! Single concrete bridge from the computed `x3` words to the generic delta proof. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def pointAddDoubleDeltaInitialConcreteEnv (yst : EvmState)
    (out left right : U256) : VEnv Challenge.EvmProof.modexpExec.toDialect :=
  bindZeros Challenge.EvmProof.modexpExec.toDialect ["\x00124", "\x00125"] ++
    pointAddDoubleXSubEnv yst out left right

private theorem pointAddDoubleDeltaInitialConcreteEnv_hi (yst : EvmState)
    (out left right : U256) :
    VEnv.get (pointAddDoubleDeltaInitialConcreteEnv yst out left right)
      "\x00122" = some (pointAddDoubleXSubResult yst out left right).1 := by
  rw [pointAddDoubleDeltaInitialConcreteEnv]
  rw [venv_get_append_of_names_ne _ _ _ (by simp [bindZeros])]
  exact pointAddDoubleXSubEnv_hi yst out left right

private theorem pointAddDoubleDeltaInitialConcreteEnv_lo (yst : EvmState)
    (out left right : U256) :
    VEnv.get (pointAddDoubleDeltaInitialConcreteEnv yst out left right)
      "\x00123" = some (pointAddDoubleXSubResult yst out left right).2 := by
  rw [pointAddDoubleDeltaInitialConcreteEnv]
  rw [venv_get_append_of_names_ne _ _ _ (by simp [bindZeros])]
  exact pointAddDoubleXSubEnv_lo yst out left right

def pointAddDoubleDeltaContext (yst : EvmState)
    (out left right : U256) : PointAddDoubleDeltaContext where
  env := pointAddDoubleDeltaInitialConcreteEnv yst out left right
  state := pointAddDoubleXSubState yst out left right
  x3Hi := (pointAddDoubleXSubResult yst out left right).1
  x3Lo := (pointAddDoubleXSubResult yst out left right).2
  env_hi := pointAddDoubleDeltaInitialConcreteEnv_hi yst out left right
  env_lo := pointAddDoubleDeltaInitialConcreteEnv_lo yst out left right

def pointAddDoubleDeltaConcreteEnv (yst : EvmState)
    (out left right : U256) : VEnv Challenge.EvmProof.modexpExec.toDialect :=
  pointAddDoubleDeltaEnv (pointAddDoubleDeltaContext yst out left right)

def pointAddDoubleDeltaConcreteState (yst : EvmState)
    (out left right : U256) : EvmState :=
  pointAddDoubleDeltaRawState (pointAddDoubleDeltaContext yst out left right)

theorem step_pointAddDoubleDeltaInit (yst : EvmState)
    (out left right : U256) :
    ExecStmt Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddDoubleXSubEnv yst out left right)
      (pointAddDoubleXSubState yst out left right)
      pointAddDoubleDeltaInitStmt
      (pointAddDoubleDeltaInitialConcreteEnv yst out left right)
      (pointAddDoubleXSubState yst out left right) .normal := by
  rw [pointAddDoubleDeltaInitStmt_eq]
  simpa [pointAddDoubleDeltaInitialConcreteEnv] using
    (Step.letZero
      (D := Challenge.EvmProof.modexpExec.toDialect)
      (funs := pointAddBodyFuns)
      (V := pointAddDoubleXSubEnv yst out left right)
      (st := pointAddDoubleXSubState yst out left right)
      (vars := ["\x00124", "\x00125"]))

theorem step_pointAddDoubleDeltaInitAndStmt (yst : EvmState)
    (out left right : U256) :
    ExecStmts Challenge.EvmProof.modexpExec.toDialect pointAddBodyFuns
      (pointAddDoubleXSubEnv yst out left right)
      (pointAddDoubleXSubState yst out left right)
      [pointAddDoubleDeltaInitStmt, pointAddDoubleDeltaStmt]
      (pointAddDoubleDeltaConcreteEnv yst out left right)
      (pointAddDoubleDeltaConcreteState yst out left right) .normal := by
  exact Step.seqCons (step_pointAddDoubleDeltaInit yst out left right)
    (Step.seqCons
      (step_pointAddDoubleDeltaGeneric
        (pointAddDoubleDeltaContext yst out left right)) Step.seqNil)

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
