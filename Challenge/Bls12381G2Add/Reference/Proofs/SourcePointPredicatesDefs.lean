import Challenge.Bls12381G2Add.Reference.Proofs.SourceOnCurveCorrect

set_option warningAsError true

/-! # Frozen G2ADD point predicate definitions -/
namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def pointPaddingZeroValue (yst : EvmState) (point : U256) : U256 :=
  b2w (((loadWord yst.memory point.toNat >>> 128) |||
      (loadWord yst.memory (point + BitVec.ofNat 256 64).toNat >>> 128)) |||
    ((loadWord yst.memory (point + BitVec.ofNat 256 128).toNat >>> 128) |||
      (loadWord yst.memory (point + BitVec.ofNat 256 192).toNat >>> 128)) = 0)

def pointValidValue (yst : EvmState) (point : U256) : U256 :=
  (fp2ValidValue yst point &&&
    fp2ValidValue yst (point + BitVec.ofNat 256 128)) &&&
  pointPaddingZeroValue yst point

def pointZeroValue (yst : EvmState) (point : U256) : U256 :=
  fp2ZeroValue yst point &&&
    fp2ZeroValue yst (point + BitVec.ofNat 256 128)

def pointPaddingZeroBody : Block Op :=
  match Compilation.referenceCompiledBlock[19]? with
  | some (Stmt.funDef _ _ _ body) => body
  | _ => []

def pointPaddingZeroDecl : FDecl Challenge.EvmProof.modexpExec.toDialect :=
  { params := ["\x00122"], rets := ["\x00123"], body := pointPaddingZeroBody }

theorem lookup_pointPaddingZero : lookupFun fp2Funs "\x0019" =
    some (pointPaddingZeroDecl, fp2Funs) := by rfl

def pointValidBody : Block Op :=
  match Compilation.referenceCompiledBlock[20]? with
  | some (Stmt.funDef _ _ _ body) => body
  | _ => []

def pointValidDecl : FDecl Challenge.EvmProof.modexpExec.toDialect :=
  { params := ["\x00124"], rets := ["\x00125"], body := pointValidBody }

theorem lookup_pointValid : lookupFun fp2Funs "\x0020" =
    some (pointValidDecl, fp2Funs) := by rfl

def pointZeroBody : Block Op :=
  match Compilation.referenceCompiledBlock[21]? with
  | some (Stmt.funDef _ _ _ body) => body
  | _ => []

def pointZeroDecl : FDecl Challenge.EvmProof.modexpExec.toDialect :=
  { params := ["\x00126"], rets := ["\x00127"], body := pointZeroBody }

theorem lookup_pointZero : lookupFun fp2Funs "\x0021" =
    some (pointZeroDecl, fp2Funs) := by rfl

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
