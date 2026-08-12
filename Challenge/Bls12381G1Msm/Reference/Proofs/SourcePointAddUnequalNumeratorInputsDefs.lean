import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalNumerator

set_option warningAsError true

/-! State and environment firebreaks for unequal-numerator input loads. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

@[simp] theorem pointAddUnequal_touchMemory_memory (yst : EvmState)
    (offset size : Nat) : (touchMemory yst offset size).memory = yst.memory := by
  rfl

def pointAddUnequalNumeratorRawInitialEnv (out left right : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  bindZeros Challenge.EvmProof.modexpExec.toDialect ["fc0_67", "fc0_68"] ++
    pointAddUnequalNumeratorInitialEnv out left right

def pointAddUnequalNumeratorLeftLoEnv (yst : EvmState)
    (out left right : U256) : VEnv Challenge.EvmProof.modexpExec.toDialect :=
  ("fc0_69", pointAddUnequalLeftYLo yst out left right) ::
    pointAddUnequalNumeratorRawInitialEnv out left right

def pointAddUnequalNumeratorLeftHiEnv (yst : EvmState)
    (out left right : U256) : VEnv Challenge.EvmProof.modexpExec.toDialect :=
  ("fc0_70", pointAddUnequalLeftYHi yst out left right) ::
    pointAddUnequalNumeratorLeftLoEnv yst out left right

def pointAddUnequalNumeratorRightLoEnv (yst : EvmState)
    (out left right : U256) : VEnv Challenge.EvmProof.modexpExec.toDialect :=
  ("fc0_71", pointAddUnequalRightYLo yst out left right) ::
    pointAddUnequalNumeratorLeftHiEnv yst out left right

def pointAddUnequalNumeratorInputsEnv (yst : EvmState)
    (out left right : U256) : VEnv Challenge.EvmProof.modexpExec.toDialect :=
  ("fc0_72", pointAddUnequalRightYHi yst out left right) ::
    pointAddUnequalNumeratorRightLoEnv yst out left right

def pointAddUnequalNumeratorState1 (yst : EvmState)
    (out left right : U256) :=
  touchMemory (pointAddXEqState yst out left right) 1568 32

def pointAddUnequalNumeratorState2 (yst : EvmState)
    (out left right : U256) :=
  touchMemory (pointAddUnequalNumeratorState1 yst out left right)
    (pointAddUnequalLeftPtr yst out left right + 96).toNat 32

def pointAddUnequalNumeratorState3 (yst : EvmState)
    (out left right : U256) :=
  touchMemory (pointAddUnequalNumeratorState2 yst out left right) 1568 32

def pointAddUnequalNumeratorState4 (yst : EvmState)
    (out left right : U256) :=
  touchMemory (pointAddUnequalNumeratorState3 yst out left right)
    (pointAddUnequalLeftPtr yst out left right + 64).toNat 32

def pointAddUnequalNumeratorState5 (yst : EvmState)
    (out left right : U256) :=
  touchMemory (pointAddUnequalNumeratorState4 yst out left right) 1600 32

def pointAddUnequalNumeratorState6 (yst : EvmState)
    (out left right : U256) :=
  touchMemory (pointAddUnequalNumeratorState5 yst out left right)
    (pointAddUnequalRightPtr yst out left right + 96).toNat 32

def pointAddUnequalNumeratorState7 (yst : EvmState)
    (out left right : U256) :=
  touchMemory (pointAddUnequalNumeratorState6 yst out left right) 1600 32

def pointAddUnequalNumeratorInputsState (yst : EvmState)
    (out left right : U256) :=
  touchMemory (pointAddUnequalNumeratorState7 yst out left right)
    (pointAddUnequalRightPtr yst out left right + 64).toNat 32

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
