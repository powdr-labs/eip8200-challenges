import Challenge.Bls12381G2Add.Reference.Proofs.SourceMainPointScope
import Challenge.Bls12381G2Add.Reference.Proofs.SourceFp2InvImag
import Challenge.Bls12381G2Add.Reference.Proofs.SourceFp2MulImag
import Challenge.Bls12381G2Add.Reference.Proofs.SourceFp2AddPreservation

set_option warningAsError true

/-! # Frozen G2ADD finite-path syntax and initial state graph -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def mainFiniteStmt0 : Stmt Op := Compilation.referenceCompiledBlock[44]!
def mainFiniteStmt1 : Stmt Op := Compilation.referenceCompiledBlock[45]!
def mainFiniteStmt2 : Stmt Op := Compilation.referenceCompiledBlock[46]!
def mainFiniteStmt3 : Stmt Op := Compilation.referenceCompiledBlock[47]!
def mainFiniteStmt4 : Stmt Op := Compilation.referenceCompiledBlock[48]!
def mainFiniteStmt5 : Stmt Op := Compilation.referenceCompiledBlock[49]!
def mainFiniteStmt6 : Stmt Op := Compilation.referenceCompiledBlock[50]!
def mainFiniteStmt7 : Stmt Op := Compilation.referenceCompiledBlock[51]!
def mainFiniteStmt8 : Stmt Op := Compilation.referenceCompiledBlock[52]!
def mainFiniteStmt9 : Stmt Op := Compilation.referenceCompiledBlock[53]!

def mainFiniteBody : Block Op := (Compilation.referenceCompiledBlock).drop 44

theorem mainFiniteBody_eq : mainFiniteBody =
    [mainFiniteStmt0, mainFiniteStmt1, mainFiniteStmt2, mainFiniteStmt3,
      mainFiniteStmt4, mainFiniteStmt5, mainFiniteStmt6, mainFiniteStmt7,
      mainFiniteStmt8, mainFiniteStmt9] := by rfl

def mainFiniteXEq1 (yst : EvmState) : U256 :=
  fp2EqValue (mainValidatedState yst) 0 256

def mainAfterFiniteXEq1 (yst : EvmState) : EvmState :=
  fp2EqReadState (mainValidatedState yst) 0 256

def mainFiniteXEq2 (yst : EvmState) : U256 :=
  fp2EqValue (mainAfterFiniteXEq1 yst) 0 256

def mainAfterFiniteXEq2 (yst : EvmState) : EvmState :=
  fp2EqReadState (mainAfterFiniteXEq1 yst) 0 256

def mainDoubleBody : Block Op :=
  match mainFiniteStmt0 with
  | .cond _ body => body.drop 2
  | _ => []

def mainDoubleYEq (yst : EvmState) : U256 :=
  fp2EqValue (mainAfterFiniteXEq1 yst) 128 384

def mainAfterDoubleYEq (yst : EvmState) : EvmState :=
  fp2EqReadState (mainAfterFiniteXEq1 yst) 128 384

def mainDoubleYZero (yst : EvmState) : U256 :=
  fp2ZeroValue (mainAfterDoubleYEq yst) 128

def mainAfterDoubleYZero (yst : EvmState) : EvmState :=
  fp2ReadState (mainAfterDoubleYEq yst) 128

def mainDoubleState0 (yst : EvmState) : EvmState :=
  fp2MulFinalState (mainAfterDoubleYZero yst) 2176 0 0

def mainDoubleState1 (yst : EvmState) : EvmState :=
  fp2AddContractState (mainDoubleState0 yst) 2304 2176 2176

def mainDoubleState2 (yst : EvmState) : EvmState :=
  fp2AddContractState (mainDoubleState1 yst) 2304 2304 2176

def mainDoubleState3 (yst : EvmState) : EvmState :=
  fp2AddContractState (mainDoubleState2 yst) 2432 128 128

def mainDoubleState4 (yst : EvmState) : EvmState :=
  fp2InvFinalState (mainDoubleState3 yst) 2560 2432

def mainDoubleFinalState (yst : EvmState) : EvmState :=
  fp2MulFinalState (mainDoubleState4 yst) 2048 2304 2560

def mainFiniteClearState (yst : EvmState) : EvmState := clearPointState yst

def mainFiniteClearReturnState (yst : EvmState) : EvmState :=
  { touchMemory (mainFiniteClearState yst) 0 256 with
    halted := some (.ret, readBytes (mainFiniteClearState yst).memory 0 256) }

def mainUnequalState0 (yst : EvmState) : EvmState :=
  fp2SubFinalState (mainAfterFiniteXEq2 yst) 2304 384 128

def mainUnequalState1 (yst : EvmState) : EvmState :=
  fp2SubFinalState (mainUnequalState0 yst) 2432 256 0

def mainUnequalState2 (yst : EvmState) : EvmState :=
  fp2InvFinalState (mainUnequalState1 yst) 2560 2432

def mainUnequalFinalState (yst : EvmState) : EvmState :=
  fp2MulFinalState (mainUnequalState2 yst) 2048 2304 2560

def mainUnequalBody : Block Op :=
  match mainFiniteStmt1 with
  | .cond _ body => body
  | _ => []

def mainDoubleXEq2 (yst : EvmState) : U256 :=
  fp2EqValue (mainDoubleFinalState yst) 0 256

def mainAfterDoubleXEq2 (yst : EvmState) : EvmState :=
  fp2EqReadState (mainDoubleFinalState yst) 0 256

def mainPostState0 (yst : EvmState) : EvmState :=
  fp2MulFinalState yst 2688 2048 2048

def mainPostState1 (yst : EvmState) : EvmState :=
  fp2SubFinalState (mainPostState0 yst) 2688 2688 0

def mainPostState2 (yst : EvmState) : EvmState :=
  fp2SubFinalState (mainPostState1 yst) 2688 2688 256

def mainPostState3 (yst : EvmState) : EvmState :=
  fp2SubFinalState (mainPostState2 yst) 2816 0 2688

def mainPostState4 (yst : EvmState) : EvmState :=
  fp2MulFinalState (mainPostState3 yst) 2944 2048 2816

def mainPostState5 (yst : EvmState) : EvmState :=
  fp2SubFinalState (mainPostState4 yst) 2944 2944 128

def mainPostStoredState (yst : EvmState) : EvmState :=
  storePointState (mainPostState5 yst) 2688 2944

def mainPostReturnState (yst : EvmState) : EvmState :=
  { touchMemory (mainPostStoredState yst) 0 256 with
    halted := some (.ret, readBytes (mainPostStoredState yst).memory 0 256) }

def mainPostBody : Block Op := (Compilation.referenceCompiledBlock).drop 46

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
