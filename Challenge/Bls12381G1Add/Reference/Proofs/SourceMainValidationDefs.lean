import Challenge.Bls12381G1Add.Reference.Proofs.SourceOnCurveLawful

set_option warningAsError true

/-! # Frozen G1ADD main validation prefix -/

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def mainFuns : FunEnv Challenge.EvmProof.modexpExec.toDialect :=
  [hoist Challenge.EvmProof.modexpExec.toDialect
    Compilation.referenceCompiledBlock]

def mainLengthStmt : Stmt Op := Compilation.referenceCompiledBlock[13]!
def mainStore0 : Stmt Op := Compilation.referenceCompiledBlock[14]!
def mainStore1 : Stmt Op := Compilation.referenceCompiledBlock[15]!
def mainStore2 : Stmt Op := Compilation.referenceCompiledBlock[16]!
def mainStore3 : Stmt Op := Compilation.referenceCompiledBlock[17]!
def mainStore4 : Stmt Op := Compilation.referenceCompiledBlock[18]!
def mainStore5 : Stmt Op := Compilation.referenceCompiledBlock[19]!
def mainStore6 : Stmt Op := Compilation.referenceCompiledBlock[20]!
def mainStore7 : Stmt Op := Compilation.referenceCompiledBlock[21]!
def mainPaddingStmt : Stmt Op := Compilation.referenceCompiledBlock[22]!
def mainCanonicalStmt : Stmt Op := Compilation.referenceCompiledBlock[23]!
def mainPointScope : Stmt Op := Compilation.referenceCompiledBlock[24]!

def mainCanonicalCondition : Expr Op :=
  match mainCanonicalStmt with
  | .cond condition _ => condition
  | _ => .lit (.number 0)

def mainDecodePrefix : List (Stmt Op) :=
  [mainLengthStmt, mainStore0, mainStore1, mainStore2, mainStore3,
    mainStore4, mainStore5, mainStore6, mainStore7, mainPaddingStmt,
    mainCanonicalStmt]

theorem mainDecodePrefix_eq :
    (Compilation.referenceCompiledBlock.drop 13).take 11 = mainDecodePrefix := by
  rfl

def mainPointScopeBody : Block Op :=
  match mainPointScope with
  | .block body => body
  | _ => []

def mainInf1Stmt : Stmt Op := mainPointScopeBody[0]!
def mainInf2Stmt : Stmt Op := mainPointScopeBody[1]!
def mainCurve1Stmt : Stmt Op := mainPointScopeBody[2]!
def mainCurve2Stmt : Stmt Op := mainPointScopeBody[3]!

def mainPointValidationPrefix : List (Stmt Op) :=
  [mainInf1Stmt, mainInf2Stmt, mainCurve1Stmt, mainCurve2Stmt]

theorem mainPointValidationPrefix_eq : mainPointScopeBody.take 4 =
    mainPointValidationPrefix := by
  rfl

def mainInputWord (yst : EvmState) (offset : Nat) : U256 :=
  wordFrom yst.env.calldata offset

private def mstoreState (yst : EvmState) (offset : Nat) (value : U256) :
    EvmState :=
  { touchMemory yst offset 32 with
    memory := storeWord yst.memory offset value }

def mainDecodedState (yst : EvmState) : EvmState :=
  let s0 := mstoreState yst 0 (mainInputWord yst 0)
  let s1 := mstoreState s0 32 (mainInputWord yst 32)
  let s2 := mstoreState s1 64 (mainInputWord yst 64)
  let s3 := mstoreState s2 96 (mainInputWord yst 96)
  let s4 := mstoreState s3 128 (mainInputWord yst 128)
  let s5 := mstoreState s4 160 (mainInputWord yst 160)
  let s6 := mstoreState s5 192 (mainInputWord yst 192)
  mstoreState s6 224 (mainInputWord yst 224)

def mainDecodedWord (yst : EvmState) (offset : Nat) : U256 :=
  loadWord (mainDecodedState yst).memory offset

/-- Memory-touch state after evaluating the four padding loads. The source
evaluator visits builtin arguments from right to left. -/
def mainAfterPaddingReads (yst : EvmState) : EvmState :=
  touchMemory
    (touchMemory
      (touchMemory
        (touchMemory (mainDecodedState yst) 192 32) 128 32) 64 32) 0 32

/-- Exact source word checked by the four high-padding shifts. -/
def mainPaddingValue (yst : EvmState) : U256 :=
  ((mainDecodedWord yst 0 >>> 128) ||| (mainDecodedWord yst 64 >>> 128)) |||
    ((mainDecodedWord yst 128 >>> 128) |||
      (mainDecodedWord yst 192 >>> 128))

/-- Exact conjunction returned by the four frozen field-validity calls. -/
def mainCanonicalValue (yst : EvmState) : U256 :=
  (fpValidValue (mainDecodedWord yst 0) (mainDecodedWord yst 32) &&&
      fpValidValue (mainDecodedWord yst 64) (mainDecodedWord yst 96)) &&&
    (fpValidValue (mainDecodedWord yst 128) (mainDecodedWord yst 160) &&&
      fpValidValue (mainDecodedWord yst 192) (mainDecodedWord yst 224))

/-- Memory-touch state after the eight field-validity argument loads. -/
def mainAfterCanonicalReads (yst : EvmState) : EvmState :=
  touchMemory
    (touchMemory
      (touchMemory
        (touchMemory
          (touchMemory
            (touchMemory
              (touchMemory
                (touchMemory (mainAfterPaddingReads yst) 224 32) 192 32)
              160 32) 128 32) 96 32) 64 32) 32 32) 0 32

def mainX1 (yst : EvmState) := onCurveX (mainDecodedWord yst 0) (mainDecodedWord yst 32)
def mainY1 (yst : EvmState) := onCurveY (mainDecodedWord yst 64) (mainDecodedWord yst 96)
def mainX2 (yst : EvmState) := onCurveX (mainDecodedWord yst 128) (mainDecodedWord yst 160)
def mainY2 (yst : EvmState) := onCurveY (mainDecodedWord yst 192) (mainDecodedWord yst 224)

def mainInf1 (yst : EvmState) : U256 :=
  fpZeroValue (mainDecodedWord yst 0) (mainDecodedWord yst 32) &&&
    fpZeroValue (mainDecodedWord yst 64) (mainDecodedWord yst 96)

def mainInf2 (yst : EvmState) : U256 :=
  fpZeroValue (mainDecodedWord yst 128) (mainDecodedWord yst 160) &&&
    fpZeroValue (mainDecodedWord yst 192) (mainDecodedWord yst 224)

def mainAfterInf1Reads (yst : EvmState) : EvmState :=
  touchMemory
    (touchMemory
      (touchMemory
        (touchMemory (mainAfterCanonicalReads yst) 96 32) 64 32) 32 32) 0 32

def mainAfterInf2Reads (yst : EvmState) : EvmState :=
  touchMemory
    (touchMemory
      (touchMemory
        (touchMemory (mainAfterInf1Reads yst) 224 32) 192 32) 160 32) 128 32

def mainPointEnv (yst : EvmState) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  [("\x0097", mainInf2 yst), ("\x0096", mainInf1 yst)]

def afterFourLoads (yst : EvmState)
    (xHiOffset xLoOffset yHiOffset yLoOffset : Nat) : EvmState :=
  touchMemory
    (touchMemory
      (touchMemory
        (touchMemory yst yLoOffset 32) yHiOffset 32) xLoOffset 32)
    xHiOffset 32

/-- State after the first `onCurve` call's four arguments are evaluated from
right to left. The helper call itself always runs, including for infinity. -/
def mainCurve1ArgsState (yst : EvmState) : EvmState :=
  afterFourLoads (mainAfterInf2Reads yst) 0 32 64 96

def mainCurve1Result (yst : EvmState) : U256 :=
  onCurveResult (mainCurve1ArgsState yst)
    (mainDecodedWord yst 0) (mainDecodedWord yst 32)
    (mainDecodedWord yst 64) (mainDecodedWord yst 96)

def mainCurve1ConditionValue (yst : EvmState) : U256 :=
  b2w (mainInf1 yst = 0) &&& b2w (mainCurve1Result yst = 0)

def mainAfterCurve1 (yst : EvmState) : EvmState :=
  onCurveFinalState (mainCurve1ArgsState yst)
    (mainDecodedWord yst 0) (mainDecodedWord yst 32)
    (mainDecodedWord yst 64) (mainDecodedWord yst 96)

/-- State after the second `onCurve` call's four arguments are evaluated from
right to left. -/
def mainCurve2ArgsState (yst : EvmState) : EvmState :=
  afterFourLoads (mainAfterCurve1 yst) 128 160 192 224

def mainCurve2Result (yst : EvmState) : U256 :=
  onCurveResult (mainCurve2ArgsState yst)
    (mainDecodedWord yst 128) (mainDecodedWord yst 160)
    (mainDecodedWord yst 192) (mainDecodedWord yst 224)

def mainCurve2ConditionValue (yst : EvmState) : U256 :=
  b2w (mainInf2 yst = 0) &&& b2w (mainCurve2Result yst = 0)

def mainValidatedState (yst : EvmState) : EvmState :=
  onCurveFinalState (mainCurve2ArgsState yst)
    (mainDecodedWord yst 128) (mainDecodedWord yst 160)
    (mainDecodedWord yst 192) (mainDecodedWord yst 224)

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
