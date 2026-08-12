import Challenge.Bls12381G2Add.Reference.Proofs.SourceFp2MulCorrect
import Challenge.Bls12381G2Add.Reference.Proofs.SourceFp2AddPreservation

set_option warningAsError true

/-! # Frozen G2ADD `onCurve` syntax and state graph -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def onCurveFuns : FunEnv Challenge.EvmProof.modexpExec.toDialect := fp2MulFuns

def onCurveBody : Block Op :=
  match Compilation.referenceCompiledBlock[18]? with
  | some (Stmt.funDef _ _ _ body) => body
  | _ => []

def onCurveStmt0 : Stmt Op := onCurveBody[0]!
def onCurveStmt1 : Stmt Op := onCurveBody[1]!
def onCurveStmt2 : Stmt Op := onCurveBody[2]!
def onCurveStmt3 : Stmt Op := onCurveBody[3]!
def onCurveStmt4 : Stmt Op := onCurveBody[4]!
def onCurveStmt5 : Stmt Op := onCurveBody[5]!
def onCurveStmt6 : Stmt Op := onCurveBody[6]!
def onCurveStmt7 : Stmt Op := onCurveBody[7]!
def onCurveStmt8 : Stmt Op := onCurveBody[8]!

theorem onCurveBody_eq : onCurveBody =
    [onCurveStmt0, onCurveStmt1, onCurveStmt2, onCurveStmt3,
      onCurveStmt4, onCurveStmt5, onCurveStmt6, onCurveStmt7,
      onCurveStmt8] := by rfl

theorem hoist_onCurveBody :
    hoist Challenge.EvmProof.modexpExec.toDialect onCurveBody = [] := by rfl

def onCurveBodyFuns : FunEnv Challenge.EvmProof.modexpExec.toDialect :=
  [] :: onCurveFuns

theorem onCurveBodyFuns_eq :
    hoist Challenge.EvmProof.modexpExec.toDialect onCurveBody ::
      onCurveFuns = onCurveBodyFuns := by
  rw [hoist_onCurveBody]
  rfl

def onCurveDecl : FDecl Challenge.EvmProof.modexpExec.toDialect :=
  { params := ["\x00119", "\x00120"]
    rets := ["\x00121"]
    body := onCurveBody }

theorem lookup_onCurve : lookupFun onCurveFuns "\x0018" =
    some (onCurveDecl, onCurveFuns) := by rfl

def onCurveInitialEnv (x y : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  [("\x00119", x), ("\x00120", y), ("\x00121", 0)]

def onCurveStateAfterY2 (yst : EvmState) (y : U256) : EvmState :=
  fp2MulFinalState yst (BitVec.ofNat 256 2048) y y

def onCurveStateAfterX2 (yst : EvmState) (x y : U256) : EvmState :=
  fp2MulFinalState (onCurveStateAfterY2 yst y)
    (BitVec.ofNat 256 2176) x x

def onCurveStateAfterX3 (yst : EvmState) (x y : U256) : EvmState :=
  fp2MulFinalState (onCurveStateAfterX2 yst x y)
    (BitVec.ofNat 256 2304) (BitVec.ofNat 256 2176) x

private def mstoreState (yst : EvmState) (offset : Nat) (value : U256) :
    EvmState :=
  { touchMemory yst offset 32 with memory := storeWord yst.memory offset value }

def onCurveStateAfterConstant (yst : EvmState) (x y : U256) : EvmState :=
  let s0 := mstoreState (onCurveStateAfterX3 yst x y) 2432 0
  let s1 := mstoreState s0 2464 4
  let s2 := mstoreState s1 2496 0
  mstoreState s2 2528 4

def onCurveStateAfterAdd (yst : EvmState) (x y : U256) : EvmState :=
  fp2AddContractState (onCurveStateAfterConstant yst x y)
    (BitVec.ofNat 256 2304) (BitVec.ofNat 256 2304)
    (BitVec.ofNat 256 2432)

def onCurveFinalState (yst : EvmState) (x y : U256) : EvmState :=
  fp2EqReadState (onCurveStateAfterAdd yst x y)
    (BitVec.ofNat 256 2048) (BitVec.ofNat 256 2304)

def onCurveResult (yst : EvmState) (x y : U256) : U256 :=
  fp2EqValue (onCurveStateAfterAdd yst x y)
    (BitVec.ofNat 256 2048) (BitVec.ofNat 256 2304)

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
