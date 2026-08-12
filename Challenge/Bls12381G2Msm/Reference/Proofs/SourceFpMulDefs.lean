import Challenge.Bls12381G2Msm.Reference.Proofs.SourceFpSub
import Challenge.Bls12381G2Add.Reference.Proofs.SourceFpModexpDefs

set_option warningAsError true

/-! Frozen local definitions and reused pure refinement for G2MSM `fpMul`. -/

namespace Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics

open EvmSemantics EvmSemantics.EVM
open YulSemantics YulSemantics.EVM
open Challenge.Bls12381G2Msm.Reference.Proofs.Compilation

abbrev fpMulInputState :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fpMulInputState
abbrev fpMulPreModulusState :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fpMulPreModulusState
abbrev convFullMul :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.convFullMul
abbrev fpMulReducedValue :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fpMulReducedValue
abbrev fpMulOutputBytes :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fpMulOutputBytes
abbrev fpMulResponse :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fpMulResponse
abbrev fpMulCallState :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fpMulCallState
abbrev fpMulResult :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fpMulResult
abbrev fpMulFinalState :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fpMulFinalState
abbrev fpMulOutputLimbs :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fpMulOutputLimbs
abbrev fpMulLeft :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fpMulLeft
abbrev fpMulRight :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fpMulRight

export Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
  (fpMulInput_runModexp_raw)

def fpMulFuns : FunEnv Challenge.EvmProof.modexpExec.toDialect :=
  [hoist Challenge.EvmProof.modexpExec.toDialect referenceCompiledBlock]

def fpMulBody : Block Op :=
  match referenceCompiledBlock[9]? with
  | some (Stmt.funDef _ _ _ body) => body
  | _ => []

def fpMulStmt0 : Stmt Op := fpMulBody[0]!
def fpMulStmt1 : Stmt Op := fpMulBody[1]!
def fpMulStmt2 : Stmt Op := fpMulBody[2]!
def fpMulStmt3 : Stmt Op := fpMulBody[3]!
def fpMulStmt4 : Stmt Op := fpMulBody[4]!
def fpMulStmt5 : Stmt Op := fpMulBody[5]!
def fpMulStmt6 : Stmt Op := fpMulBody[6]!
def fpMulStmt7 : Stmt Op := fpMulBody[7]!
def fpMulStmt8 : Stmt Op := fpMulBody[8]!
def fpMulStmt9 : Stmt Op := fpMulBody[9]!
def fpMulStmt10 : Stmt Op := fpMulBody[10]!
def fpMulStmt11 : Stmt Op := fpMulBody[11]!

theorem fpMulBody_eq : fpMulBody =
    [fpMulStmt0, fpMulStmt1, fpMulStmt2, fpMulStmt3,
      fpMulStmt4, fpMulStmt5, fpMulStmt6, fpMulStmt7,
      fpMulStmt8, fpMulStmt9, fpMulStmt10, fpMulStmt11] := by
  rfl

theorem hoist_fpMulBody :
    hoist Challenge.EvmProof.modexpExec.toDialect fpMulBody = [] := by
  rfl

def fpMulBodyFuns : FunEnv Challenge.EvmProof.modexpExec.toDialect :=
  [] :: fpMulFuns

theorem fpMulBodyFuns_eq :
    hoist Challenge.EvmProof.modexpExec.toDialect fpMulBody :: fpMulFuns =
      fpMulBodyFuns := by
  rw [hoist_fpMulBody]
  rfl

def fpMulDecl : FDecl Challenge.EvmProof.modexpExec.toDialect :=
  { params := ["\x0086", "\x0087", "\x0088", "\x0089"]
    rets := ["\x0090", "\x0091"]
    body := fpMulBody }

theorem lookup_fpMul : lookupFun fpMulFuns "\x009" =
    some (fpMulDecl, fpMulFuns) := by
  rfl

def fpMulInitialEnv (ahi alo bhi blo : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  [("\x0086", ahi), ("\x0087", alo), ("\x0088", bhi), ("\x0089", blo),
    ("\x0090", 0), ("\x0091", 0)]

theorem canonical_fpMulOutput (yst : EvmState) (ahi alo bhi blo : U256) :
    Challenge.Bls12381.ProofSupport.Fp.Canonical
      (fpMulOutputLimbs yst ahi alo bhi blo) :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.canonical_fpMulOutput
    yst ahi alo bhi blo

theorem fpMulOutput_toField (yst : EvmState) (ahi alo bhi blo : U256)
    (ha : Challenge.Bls12381.ProofSupport.Fp.Canonical
      (fpMulLeft ahi alo))
    (hb : Challenge.Bls12381.ProofSupport.Fp.Canonical
      (fpMulRight bhi blo)) :
    Challenge.Bls12381.ProofSupport.Fp.toField
        (fpMulOutputLimbs yst ahi alo bhi blo) =
      Challenge.Bls12381.ProofSupport.Fp.toField (fpMulLeft ahi alo) *
        Challenge.Bls12381.ProofSupport.Fp.toField (fpMulRight bhi blo) :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fpMulOutput_toField
    yst ahi alo bhi blo ha hb

theorem fpMulOutput_eq_mulCanonical (yst : EvmState)
    (ahi alo bhi blo : U256)
    (ha : Challenge.Bls12381.ProofSupport.Fp.Canonical
      (fpMulLeft ahi alo))
    (hb : Challenge.Bls12381.ProofSupport.Fp.Canonical
      (fpMulRight bhi blo)) :
    fpMulOutputLimbs yst ahi alo bhi blo =
      Challenge.Bls12381.ProofSupport.Fp.mulCanonical
        (fpMulLeft ahi alo) (fpMulRight bhi blo) :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fpMulOutput_eq_mulCanonical
    yst ahi alo bhi blo ha hb

end Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics
