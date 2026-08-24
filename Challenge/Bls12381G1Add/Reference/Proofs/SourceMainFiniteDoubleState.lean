import Challenge.Bls12381G1Add.Reference.Proofs.SourceMainFiniteDoubleDefs
import Challenge.Bls12381G1Add.Reference.Proofs.SourceMainFiniteExceptional
import Challenge.Bls12381G1Add.Reference.Proofs.SourceFpInvResultDefs
import Challenge.Bls12381G1Add.Reference.Proofs.SourceFpMulMemory

set_option warningAsError true

/-! # G1ADD equal-point doubling-slope state graph -/

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def mainFiniteDoubleXWords (yst : EvmState) : U256 × U256 :=
  (mainDecodedWord yst 0, mainDecodedWord yst 32)

def mainFiniteDoubleYWords (yst : EvmState) : U256 × U256 :=
  (mainDecodedWord yst 64, mainDecodedWord yst 96)

def mainFiniteDoubleXSqArgsState (yst : EvmState) : EvmState :=
  afterFourLoads (mainFiniteYZeroArgsState yst) 0 32 0 32

def mainFiniteDoubleXSqWords (yst : EvmState) : U256 × U256 :=
  let x := mainFiniteDoubleXWords yst
  fpMulResult (mainFiniteDoubleXSqArgsState yst) x.1 x.2 x.1 x.2

def mainFiniteDoubleState1 (yst : EvmState) : EvmState :=
  let x := mainFiniteDoubleXWords yst
  fpMulFinalState (mainFiniteDoubleXSqArgsState yst) x.1 x.2 x.1 x.2

theorem mainFiniteDoubleState1_eq (yst : EvmState) :
    mainFiniteDoubleState1 yst = mainFiniteDoubleXSqArgsState yst := by
  rfl

def mainFiniteDoubleTwiceWords (yst : EvmState) : U256 × U256 :=
  let xSq := mainFiniteDoubleXSqWords yst
  fpAddValue xSq.1 xSq.2 xSq.1 xSq.2

def mainFiniteDoubleNumeratorWords (yst : EvmState) : U256 × U256 :=
  let twice := mainFiniteDoubleTwiceWords yst
  let xSq := mainFiniteDoubleXSqWords yst
  fpAddValue twice.1 twice.2 xSq.1 xSq.2

def mainFiniteDoubleDenominatorWords (yst : EvmState) : U256 × U256 :=
  let y := mainFiniteDoubleYWords yst
  fpAddValue y.1 y.2 y.1 y.2

def mainFiniteDoubleDenArgsState (yst : EvmState) : EvmState :=
  afterFourLoads (mainFiniteDoubleState1 yst) 64 96 64 96

def mainFiniteDoubleDenInvWords (yst : EvmState) : U256 × U256 :=
  let den := mainFiniteDoubleDenominatorWords yst
  fpInvResultWords den.1 den.2

def mainFiniteDoubleState2 (yst : EvmState) : EvmState :=
  mainFiniteDoubleDenArgsState yst

theorem mainFiniteDoubleState2_eq (yst : EvmState) :
    mainFiniteDoubleState2 yst = mainFiniteDoubleDenArgsState yst := by
  rfl

def mainFiniteDoubleLambdaWords (yst : EvmState) : U256 × U256 :=
  let num := mainFiniteDoubleNumeratorWords yst
  let denInv := mainFiniteDoubleDenInvWords yst
  fpMulResult (mainFiniteDoubleState2 yst)
    num.1 num.2 denInv.1 denInv.2

def mainFiniteDoubleFinalState (yst : EvmState) : EvmState :=
  let num := mainFiniteDoubleNumeratorWords yst
  let denInv := mainFiniteDoubleDenInvWords yst
  fpMulFinalState (mainFiniteDoubleState2 yst)
    num.1 num.2 denInv.1 denInv.2

def mainFiniteDoubleEnv1 (yst : EvmState) :
    VEnv Challenge.YulProof.ClosedEvm.exec.toDialect :=
  [("\x00103", (mainFiniteDoubleXSqWords yst).1),
    ("\x00104", (mainFiniteDoubleXSqWords yst).2)] ++ mainFiniteEnv yst

theorem mainFiniteDoubleEnv1_eq (yst : EvmState) :
    let x := mainFiniteDoubleXWords yst
    mainFiniteDoubleEnv1 yst =
      [("\x00103", (fpMulResult (mainFiniteDoubleXSqArgsState yst)
        x.1 x.2 x.1 x.2).1),
       ("\x00104", (fpMulResult (mainFiniteDoubleXSqArgsState yst)
        x.1 x.2 x.1 x.2).2)] ++ mainFiniteEnv yst := by
  rfl

def mainFiniteDoubleEnv2 (yst : EvmState) :
    VEnv Challenge.YulProof.ClosedEvm.exec.toDialect :=
  [("\x00105", (mainFiniteDoubleTwiceWords yst).1),
    ("\x00106", (mainFiniteDoubleTwiceWords yst).2)] ++
      mainFiniteDoubleEnv1 yst

def mainFiniteDoubleEnv3 (yst : EvmState) :
    VEnv Challenge.YulProof.ClosedEvm.exec.toDialect :=
  VEnv.setMany (mainFiniteDoubleEnv2 yst) ["\x00105", "\x00106"]
    [(mainFiniteDoubleNumeratorWords yst).1,
      (mainFiniteDoubleNumeratorWords yst).2]

def mainFiniteDoubleEnv4 (yst : EvmState) :
    VEnv Challenge.YulProof.ClosedEvm.exec.toDialect :=
  [("\x00107", (mainFiniteDoubleDenominatorWords yst).1),
    ("\x00108", (mainFiniteDoubleDenominatorWords yst).2)] ++
      mainFiniteDoubleEnv3 yst

theorem mainFiniteDoubleEnv4_eq (yst : EvmState) :
    let y := mainFiniteDoubleYWords yst
    mainFiniteDoubleEnv4 yst =
      [("\x00107", (fpAddValue y.1 y.2 y.1 y.2).1),
       ("\x00108", (fpAddValue y.1 y.2 y.1 y.2).2)] ++
        mainFiniteDoubleEnv3 yst := by
  rfl

def mainFiniteDoubleEnv5 (yst : EvmState) :
    VEnv Challenge.YulProof.ClosedEvm.exec.toDialect :=
  [("\x00109", (mainFiniteDoubleDenInvWords yst).1),
    ("\x00110", (mainFiniteDoubleDenInvWords yst).2)] ++
      mainFiniteDoubleEnv4 yst

theorem mainFiniteDoubleEnv5_eq (yst : EvmState) :
    let den := mainFiniteDoubleDenominatorWords yst
    mainFiniteDoubleEnv5 yst =
      [("\x00109", (fpInvResultWords den.1 den.2).1),
       ("\x00110", (fpInvResultWords den.1 den.2).2)] ++
        mainFiniteDoubleEnv4 yst := by
  rfl

def mainFiniteDoubleEnv6 (yst : EvmState) :
    VEnv Challenge.YulProof.ClosedEvm.exec.toDialect :=
  VEnv.setMany (mainFiniteDoubleEnv5 yst) ["\x00101", "\x00102"]
    [(mainFiniteDoubleLambdaWords yst).1,
      (mainFiniteDoubleLambdaWords yst).2]

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
