import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalDenominator
import Challenge.Bls12381G1Msm.Reference.Proofs.SourcePointAddUnequalNumeratorRightHiMemory

set_option warningAsError true

/-! State/environment firebreaks for unequal-denominator input loads. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def pointAddUnequalDenominatorInitialEnv (yst : EvmState)
    (out left right : U256) :=
  bindZeros Challenge.EvmProof.modexpExec.toDialect ["\x00130", "\x00131"] ++
    pointAddUnequalNumeratorEnv yst out left right

def pointAddUnequalDenominatorRawInitialEnv (yst : EvmState)
    (out left right : U256) :=
  bindZeros Challenge.EvmProof.modexpExec.toDialect ["fc0_74", "fc0_75"] ++
    pointAddUnequalDenominatorInitialEnv yst out left right

def pointAddUnequalDenominatorLeftLoEnv (yst : EvmState)
    (out left right : U256) :=
  ("fc0_76", pointAddUnequalLeftXLo yst out left right) ::
    pointAddUnequalDenominatorRawInitialEnv yst out left right

def pointAddUnequalDenominatorLeftHiEnv (yst : EvmState)
    (out left right : U256) :=
  ("fc0_77", pointAddUnequalLeftXHi yst out left right) ::
    pointAddUnequalDenominatorLeftLoEnv yst out left right

def pointAddUnequalDenominatorRightLoEnv (yst : EvmState)
    (out left right : U256) :=
  ("fc0_78", pointAddUnequalRightXLo yst out left right) ::
    pointAddUnequalDenominatorLeftHiEnv yst out left right

def pointAddUnequalDenominatorInputsEnv (yst : EvmState)
    (out left right : U256) :=
  ("fc0_79", pointAddUnequalRightXHi yst out left right) ::
    pointAddUnequalDenominatorRightLoEnv yst out left right

def pointAddUnequalDenominatorState1 (yst : EvmState)
    (out left right : U256) :=
  touchMemory (pointAddUnequalNumeratorInputsState yst out left right) 1568 32
def pointAddUnequalDenominatorState2 (yst : EvmState)
    (out left right : U256) :=
  touchMemory (pointAddUnequalDenominatorState1 yst out left right)
    (pointAddUnequalLeftPtr yst out left right + 32).toNat 32
def pointAddUnequalDenominatorState3 (yst : EvmState)
    (out left right : U256) :=
  touchMemory (pointAddUnequalDenominatorState2 yst out left right) 1568 32
def pointAddUnequalDenominatorState4 (yst : EvmState)
    (out left right : U256) :=
  touchMemory (pointAddUnequalDenominatorState3 yst out left right)
    (pointAddUnequalLeftPtr yst out left right).toNat 32
def pointAddUnequalDenominatorState5 (yst : EvmState)
    (out left right : U256) :=
  touchMemory (pointAddUnequalDenominatorState4 yst out left right) 1600 32
def pointAddUnequalDenominatorState6 (yst : EvmState)
    (out left right : U256) :=
  touchMemory (pointAddUnequalDenominatorState5 yst out left right)
    (pointAddUnequalRightPtr yst out left right + 32).toNat 32
def pointAddUnequalDenominatorState7 (yst : EvmState)
    (out left right : U256) :=
  touchMemory (pointAddUnequalDenominatorState6 yst out left right) 1600 32
def pointAddUnequalDenominatorInputsState (yst : EvmState)
    (out left right : U256) :=
  touchMemory (pointAddUnequalDenominatorState7 yst out left right)
    (pointAddUnequalRightPtr yst out left right).toNat 32

@[simp] theorem pointAddUnequalDenominator_touchMemory_memory (yst : EvmState)
    (offset size : Nat) : (touchMemory yst offset size).memory = yst.memory := by rfl

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
