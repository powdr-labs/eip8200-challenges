import Challenge.Bls12381G2Add.Reference.Proofs.SourceFpCore
import Challenge.Bls12381G1Add.Reference.Proofs.SourceFpInvRefinement
import Challenge.Bls12381G1Add.Reference.Proofs.SourceFpMulRefinement
import Challenge.Bls12381.ProofSupport.FpMul

set_option warningAsError true

/-!
# G2ADD scalar MODEXP helper boundaries

The MODEXP input/output graphs are independent of the enclosing challenge and
are reused from G1ADD.  The function environments, bodies, declarations, and
lookups remain local: they are kernel-checked projections of the frozen G2ADD
source block and are the inputs to the later G2-specific execution proof.
-/

namespace Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics

open EvmSemantics EvmSemantics.EVM
open YulSemantics YulSemantics.EVM

abbrev fpMulInputState :=
  Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpMulInputState
abbrev fpMulPreModulusState :=
  Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpMulPreModulusState
abbrev convFullMul :=
  Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.convFullMul
abbrev fpMulReducedValue :=
  Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpMulReducedValue
abbrev fpMulOutputBytes :=
  Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpMulOutputBytes
abbrev fpMulResponse :=
  Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpMulResponse
abbrev fpMulCallState :=
  Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpMulCallState
abbrev fpMulResult :=
  Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpMulResult
abbrev fpMulFinalState :=
  Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpMulFinalState
abbrev fpMulOutputLimbs :=
  Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpMulOutputLimbs
abbrev fpMulLeft :=
  Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpMulLeft
abbrev fpMulRight :=
  Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpMulRight

abbrev fpInvInputState :=
  Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpInvInputState
abbrev fpInvReducedValue :=
  Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpInvReducedValue
abbrev fpInvOutputBytes :=
  Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpInvOutputBytes
abbrev fpInvResponse :=
  Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpInvResponse
abbrev fpInvCallState :=
  Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpInvCallState
abbrev fpInvResult :=
  Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpInvResult
abbrev fpInvFinalState :=
  Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpInvFinalState
abbrev fpInvOutputLimbs :=
  Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpInvOutputLimbs
abbrev fpInvInputLimbs :=
  Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpInvInputLimbs

export Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
  (fpMulInput_runModexp_raw fpInvInput_runModexp)

def fpMulFuns : FunEnv Challenge.EvmProof.modexpExec.toDialect :=
  [hoist Challenge.EvmProof.modexpExec.toDialect
    Compilation.referenceCompiledBlock]

def fpMulBody : Block Op :=
  match Compilation.referenceCompiledBlock[9]? with
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
  { params := ["\x0080", "\x0081", "\x0082", "\x0083"]
    rets := ["\x0084", "\x0085"]
    body := fpMulBody }

theorem lookup_fpMul : lookupFun fpMulFuns "\x009" =
    some (fpMulDecl, fpMulFuns) := by
  rfl

def fpMulInitialEnv (ahi alo bhi blo : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  [("\x0080", ahi), ("\x0081", alo), ("\x0082", bhi), ("\x0083", blo),
    ("\x0084", 0), ("\x0085", 0)]

def fpInvFuns : FunEnv Challenge.EvmProof.modexpExec.toDialect :=
  [hoist Challenge.EvmProof.modexpExec.toDialect
    Compilation.referenceCompiledBlock]

def fpInvBody : Block Op :=
  match Compilation.referenceCompiledBlock[10]? with
  | some (Stmt.funDef _ _ _ body) => body
  | _ => []

def fpInvStmt0 : Stmt Op := fpInvBody[0]!
def fpInvStmt1 : Stmt Op := fpInvBody[1]!
def fpInvStmt2 : Stmt Op := fpInvBody[2]!
def fpInvStmt3 : Stmt Op := fpInvBody[3]!
def fpInvStmt4 : Stmt Op := fpInvBody[4]!
def fpInvStmt5 : Stmt Op := fpInvBody[5]!
def fpInvStmt6 : Stmt Op := fpInvBody[6]!
def fpInvStmt7 : Stmt Op := fpInvBody[7]!
def fpInvStmt8 : Stmt Op := fpInvBody[8]!

theorem fpInvBody_eq : fpInvBody =
    [fpInvStmt0, fpInvStmt1, fpInvStmt2, fpInvStmt3, fpInvStmt4,
      fpInvStmt5, fpInvStmt6, fpInvStmt7, fpInvStmt8] := by
  rfl

theorem hoist_fpInvBody :
    hoist Challenge.EvmProof.modexpExec.toDialect fpInvBody = [] := by
  rfl

def fpInvBodyFuns : FunEnv Challenge.EvmProof.modexpExec.toDialect :=
  [] :: fpInvFuns

theorem fpInvBodyFuns_eq :
    hoist Challenge.EvmProof.modexpExec.toDialect fpInvBody :: fpInvFuns =
      fpInvBodyFuns := by
  rw [hoist_fpInvBody]
  rfl

def fpInvDecl : FDecl Challenge.EvmProof.modexpExec.toDialect :=
  { params := ["\x0089", "\x0090"]
    rets := ["\x0091", "\x0092"]
    body := fpInvBody }

theorem lookup_fpInv : lookupFun fpInvFuns "\x0010" =
    some (fpInvDecl, fpInvFuns) := by
  rfl

def fpInvInitialEnv (hi lo : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  [("\x0089", hi), ("\x0090", lo), ("\x0091", 0), ("\x0092", 0)]

theorem canonical_fpMulOutput (yst : EvmState) (ahi alo bhi blo : U256) :
    Challenge.Bls12381.ProofSupport.Fp.Canonical
      (fpMulOutputLimbs yst ahi alo bhi blo) :=
  Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.canonical_fpMulOutput
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
  Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpMulOutput_toField
    yst ahi alo bhi blo ha hb

/-- Canonical limb equality used directly by the Fp2 arithmetic layer. -/
theorem fpMulOutput_eq_mulCanonical (yst : EvmState)
    (ahi alo bhi blo : U256)
    (ha : Challenge.Bls12381.ProofSupport.Fp.Canonical
      (fpMulLeft ahi alo))
    (hb : Challenge.Bls12381.ProofSupport.Fp.Canonical
      (fpMulRight bhi blo)) :
    fpMulOutputLimbs yst ahi alo bhi blo =
      Challenge.Bls12381.ProofSupport.Fp.mulCanonical
        (fpMulLeft ahi alo) (fpMulRight bhi blo) := by
  apply Challenge.Bls12381.ProofSupport.Fp.limbs_ext_of_value_eq
  apply Challenge.Bls12381.ProofSupport.Fp.value_eq_of_lawful_eq
    (canonical_fpMulOutput yst ahi alo bhi blo)
    (Challenge.Bls12381.ProofSupport.Fp.canonical_mulCanonical ha hb)
  have hfield := fpMulOutput_toField yst ahi alo bhi blo ha hb
  have hshared := Challenge.Bls12381.ProofSupport.Fp.toField_mulCanonical ha hb
  have hfin := hfield.trans hshared.symm
  simpa only [Challenge.Bls12381.ProofSupport.Fp.finEquiv_toField] using
    congrArg Challenge.Bls12381.ProofSupport.PrimeField.finEquiv hfin

theorem fpInvOutput_eq_invCanonical (yst : EvmState) (hi lo : U256)
    (ha : Challenge.Bls12381.ProofSupport.Fp.Canonical
      (fpInvInputLimbs hi lo)) :
    fpInvOutputLimbs yst hi lo =
      Challenge.Bls12381.ProofSupport.Fp.invCanonical
        (fpInvInputLimbs hi lo) :=
  Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpInvOutput_eq_invCanonical
    yst hi lo ha

end Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
