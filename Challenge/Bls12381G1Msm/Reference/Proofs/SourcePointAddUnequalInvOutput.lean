import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalInvCall

set_option warningAsError true

/-! Output loads of the inlined unequal-denominator inversion. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def pointAddUnequalInvResult (yst : EvmState)
    (out left right : U256) : U256 × U256 :=
  Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpInvResult
    (pointAddUnequalNumeratorInputsState yst out left right)
    (pointAddUnequalDenominatorResult yst out left right).1
    (pointAddUnequalDenominatorResult yst out left right).2

def pointAddUnequalInvFinalState (yst : EvmState)
    (out left right : U256) : EvmState :=
  Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpInvFinalState
    (pointAddUnequalNumeratorInputsState yst out left right)
    (pointAddUnequalDenominatorResult yst out left right).1
    (pointAddUnequalDenominatorResult yst out left right).2

def pointAddUnequalInvOutputEnv (yst : EvmState)
    (out left right : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  VEnv.setMany (pointAddUnequalInvInitialEnv yst out left right)
    ["\x00132", "\x00133"]
    [(pointAddUnequalInvResult yst out left right).1,
      (pointAddUnequalInvResult yst out left right).2]

def pointAddUnequalInvFinalWorkEnv (yst : EvmState)
    (out left right : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  VEnv.setMany
    (VEnv.setMany
      (VEnv.setMany
        (VEnv.setMany (pointAddUnequalInvWorkEnv yst out left right)
          ["fc2_7"] [(pointAddUnequalInvResult yst out left right).1])
        ["fc2_8"] [(pointAddUnequalInvResult yst out left right).2])
      ["\x00132"] [(pointAddUnequalInvResult yst out left right).1])
    ["\x00133"] [(pointAddUnequalInvResult yst out left right).2]

theorem exec_pointAddUnequalInvOutput (yst : EvmState)
    (out left right : U256) :
    Interp.execStmts Challenge.EvmProof.modexpExec 70
      ([] :: pointAddBodyFuns)
      (pointAddUnequalInvWorkEnv yst out left right)
      (pointAddUnequalInvCallState yst out left right)
      [pointAddUnequalInvStmt10, pointAddUnequalInvStmt11,
        pointAddUnequalInvStmt12, pointAddUnequalInvStmt13] =
    .ok (pointAddUnequalInvFinalWorkEnv yst out left right,
      pointAddUnequalInvFinalState yst out left right, .normal) := by
  rfl

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
