import Challenge.Bls12381G1Add.Reference.Proofs.SourceMainFiniteUnequalDefs
import Challenge.Bls12381G1Add.Reference.Proofs.SourceMainFiniteExceptional
import Challenge.Bls12381G1Add.Reference.Proofs.SourceFpInvResultDefs
import Challenge.Bls12381G1Add.Reference.Proofs.SourceFpMulExecDefs

set_option warningAsError true

/-! # G1ADD unequal-x slope state graph -/

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def mainFiniteUnequalConditionState (yst : EvmState) : EvmState :=
  afterFourLoads (mainFiniteXEqArgsState yst) 0 32 128 160

theorem mainFiniteXEqArgsState_loadWord (yst : EvmState) (offset : Nat)
    (hend : offset + 32 ≤ 1024) :
    loadWord (mainFiniteXEqArgsState yst).memory offset =
      mainDecodedWord yst offset := by
  rw [mainFiniteXEqArgsState, afterFourLoads_memory]
  exact mainValidatedState_loadWord yst offset hend

def mainFiniteUnequalNumeratorArgsState (yst : EvmState) : EvmState :=
  afterFourLoads (mainFiniteUnequalConditionState yst) 192 224 64 96

def mainFiniteUnequalDenominatorArgsState (yst : EvmState) : EvmState :=
  afterFourLoads (mainFiniteUnequalNumeratorArgsState yst) 128 160 0 32

theorem mainFiniteUnequalConditionState_loadWord (yst : EvmState)
    (offset : Nat) (hend : offset + 32 ≤ 1024) :
    loadWord (mainFiniteUnequalConditionState yst).memory offset =
      mainDecodedWord yst offset := by
  rw [mainFiniteUnequalConditionState, afterFourLoads_memory,
    mainFiniteXEqArgsState, afterFourLoads_memory]
  exact mainValidatedState_loadWord yst offset hend

theorem mainFiniteUnequalNumeratorArgsState_loadWord (yst : EvmState)
    (offset : Nat) (hend : offset + 32 ≤ 1024) :
    loadWord (mainFiniteUnequalNumeratorArgsState yst).memory offset =
      mainDecodedWord yst offset := by
  rw [mainFiniteUnequalNumeratorArgsState, afterFourLoads_memory]
  exact mainFiniteUnequalConditionState_loadWord yst offset hend

theorem mainFiniteUnequalDenominatorArgsState_loadWord (yst : EvmState)
    (offset : Nat) (hend : offset + 32 ≤ 1024) :
    loadWord (mainFiniteUnequalDenominatorArgsState yst).memory offset =
      mainDecodedWord yst offset := by
  rw [mainFiniteUnequalDenominatorArgsState, afterFourLoads_memory]
  exact mainFiniteUnequalNumeratorArgsState_loadWord yst offset hend

def mainFiniteUnequalNumeratorWords (yst : EvmState) : U256 × U256 :=
  fpSubValue (mainDecodedWord yst 192) (mainDecodedWord yst 224)
    (mainDecodedWord yst 64) (mainDecodedWord yst 96)

def mainFiniteUnequalDenominatorWords (yst : EvmState) : U256 × U256 :=
  fpSubValue (mainDecodedWord yst 128) (mainDecodedWord yst 160)
    (mainDecodedWord yst 0) (mainDecodedWord yst 32)

def mainFiniteUnequalDenInvWords (yst : EvmState) : U256 × U256 :=
  let den := mainFiniteUnequalDenominatorWords yst
  fpInvResultWords den.1 den.2

def mainFiniteUnequalState1 (yst : EvmState) : EvmState :=
  mainFiniteUnequalDenominatorArgsState yst

theorem mainFiniteUnequalState1_eq (yst : EvmState) :
    mainFiniteUnequalState1 yst =
      mainFiniteUnequalDenominatorArgsState yst := by
  rfl

def mainFiniteUnequalLambdaWords (yst : EvmState) : U256 × U256 :=
  let num := mainFiniteUnequalNumeratorWords yst
  let denInv := mainFiniteUnequalDenInvWords yst
  fpMulResult (mainFiniteUnequalState1 yst)
    num.1 num.2 denInv.1 denInv.2

def mainFiniteUnequalFinalState (yst : EvmState) : EvmState :=
  let num := mainFiniteUnequalNumeratorWords yst
  let denInv := mainFiniteUnequalDenInvWords yst
  fpMulFinalState (mainFiniteUnequalState1 yst)
    num.1 num.2 denInv.1 denInv.2

def mainFiniteUnequalEnv1 (yst : EvmState) :
    VEnv Challenge.YulProof.ClosedEvm.exec.toDialect :=
  [("\x00111", (mainFiniteUnequalNumeratorWords yst).1),
    ("\x00112", (mainFiniteUnequalNumeratorWords yst).2)] ++ mainFiniteEnv yst

def mainFiniteUnequalEnv2 (yst : EvmState) :
    VEnv Challenge.YulProof.ClosedEvm.exec.toDialect :=
  [("\x00113", (mainFiniteUnequalDenominatorWords yst).1),
    ("\x00114", (mainFiniteUnequalDenominatorWords yst).2)] ++
      mainFiniteUnequalEnv1 yst

def mainFiniteUnequalEnv3 (yst : EvmState) :
    VEnv Challenge.YulProof.ClosedEvm.exec.toDialect :=
  [("\x00115", (mainFiniteUnequalDenInvWords yst).1),
    ("\x00116", (mainFiniteUnequalDenInvWords yst).2)] ++
      mainFiniteUnequalEnv2 yst

theorem mainFiniteUnequalEnv3_eq (yst : EvmState) :
    let den := mainFiniteUnequalDenominatorWords yst
    mainFiniteUnequalEnv3 yst =
      [("\x00115", (fpInvResultWords den.1 den.2).1),
       ("\x00116", (fpInvResultWords den.1 den.2).2)] ++
        mainFiniteUnequalEnv2 yst := by
  rfl

def mainFiniteUnequalEnv4 (yst : EvmState) :
    VEnv Challenge.YulProof.ClosedEvm.exec.toDialect :=
  VEnv.setMany (mainFiniteUnequalEnv3 yst) ["\x00101", "\x00102"]
    [(mainFiniteUnequalLambdaWords yst).1,
      (mainFiniteUnequalLambdaWords yst).2]

def mainFiniteUnequalResultEnv (yst : EvmState) :
    VEnv Challenge.YulProof.ClosedEvm.exec.toDialect :=
  restore (mainFiniteEnv yst) (mainFiniteUnequalEnv4 yst)

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
