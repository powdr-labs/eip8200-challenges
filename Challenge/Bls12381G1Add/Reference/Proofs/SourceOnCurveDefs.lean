import Challenge.Bls12381G1Add.Reference.Proofs.SourceFpMulRefinement

set_option warningAsError true

/-! # Frozen G1ADD `onCurve` schedule and result graph -/

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def onCurveFuns : FunEnv Challenge.EvmProof.modexpExec.toDialect :=
  [hoist Challenge.EvmProof.modexpExec.toDialect
    Compilation.referenceCompiledBlock]

def onCurveBody : Block Op :=
  match Compilation.referenceCompiledBlock[11]? with
  | some (Stmt.funDef _ _ _ body) => body
  | _ => []

def onCurveStmt0 : Stmt Op := onCurveBody[0]!
def onCurveStmt1 : Stmt Op := onCurveBody[1]!
def onCurveStmt2 : Stmt Op := onCurveBody[2]!
def onCurveStmt3 : Stmt Op := onCurveBody[3]!
def onCurveStmt4 : Stmt Op := onCurveBody[4]!

theorem onCurveBody_eq : onCurveBody =
    [onCurveStmt0, onCurveStmt1, onCurveStmt2, onCurveStmt3,
      onCurveStmt4] := by
  rfl

theorem hoist_onCurveBody :
    hoist Challenge.EvmProof.modexpExec.toDialect onCurveBody = [] := by
  rfl

def onCurveBodyFuns : FunEnv Challenge.EvmProof.modexpExec.toDialect :=
  [] :: onCurveFuns

theorem onCurveBodyFuns_eq :
    hoist Challenge.EvmProof.modexpExec.toDialect onCurveBody ::
      onCurveFuns = onCurveBodyFuns := by
  rw [hoist_onCurveBody]
  rfl

def onCurveDecl : FDecl Challenge.EvmProof.modexpExec.toDialect :=
  { params := ["\x0081", "\x0082", "\x0083", "\x0084"]
    rets := ["\x0085"]
    body := onCurveBody }

theorem lookup_onCurve : lookupFun onCurveFuns "\x0011" =
    some (onCurveDecl, onCurveFuns) := by
  rfl

def onCurveInitialEnv (xHi xLo yHi yLo : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  [("\x0081", xHi), ("\x0082", xLo), ("\x0083", yHi),
    ("\x0084", yLo), ("\x0085", 0)]

def onCurveLhsWords (yst : EvmState) (yHi yLo : U256) : U256 × U256 :=
  fpMulResult yst yHi yLo yHi yLo

def onCurveState1 (yst : EvmState) (yHi yLo : U256) : EvmState :=
  fpMulFinalState yst yHi yLo yHi yLo

def onCurveX2Words (yst : EvmState) (xHi xLo yHi yLo : U256) :
    U256 × U256 :=
  fpMulResult (onCurveState1 yst yHi yLo) xHi xLo xHi xLo

def onCurveState2 (yst : EvmState) (xHi xLo yHi yLo : U256) : EvmState :=
  fpMulFinalState (onCurveState1 yst yHi yLo) xHi xLo xHi xLo

def onCurveRhsCubeWords (yst : EvmState) (xHi xLo yHi yLo : U256) :
    U256 × U256 :=
  let x2 := onCurveX2Words yst xHi xLo yHi yLo
  fpMulResult (onCurveState2 yst xHi xLo yHi yLo)
    x2.1 x2.2 xHi xLo

def onCurveFinalState (yst : EvmState) (xHi xLo yHi yLo : U256) :
    EvmState :=
  let x2 := onCurveX2Words yst xHi xLo yHi yLo
  fpMulFinalState (onCurveState2 yst xHi xLo yHi yLo)
    x2.1 x2.2 xHi xLo

def onCurveRhsWords (yst : EvmState) (xHi xLo yHi yLo : U256) :
    U256 × U256 :=
  let cube := onCurveRhsCubeWords yst xHi xLo yHi yLo
  fpAddValue cube.1 cube.2 0 4

def onCurveResult (yst : EvmState) (xHi xLo yHi yLo : U256) : U256 :=
  let lhs := onCurveLhsWords yst yHi yLo
  let rhs := onCurveRhsWords yst xHi xLo yHi yLo
  fpEqValue lhs.1 lhs.2 rhs.1 rhs.2

def onCurveX (xHi xLo : U256) :
    Challenge.Bls12381.ProofSupport.Fp.Limbs :=
  { hi := YulEvmCompiler.conv xHi, lo := YulEvmCompiler.conv xLo }

def onCurveY (yHi yLo : U256) :
    Challenge.Bls12381.ProofSupport.Fp.Limbs :=
  { hi := YulEvmCompiler.conv yHi, lo := YulEvmCompiler.conv yLo }

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
