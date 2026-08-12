import Challenge.Bls12381G2Msm.Reference.Proofs.SourceFp2AddExec
import Challenge.Bls12381G2Add.Reference.Proofs.SourceFp2SubRefinement

set_option warningAsError true

/-! Frozen local boundary and reused pure memory graph for G2MSM `fp2Sub`. -/

namespace Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM
open Challenge.Bls12381G2Msm.Reference.Proofs.Compilation

abbrev fp2SubReadState :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2SubReadState
abbrev fp2SubC0 :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2SubC0
abbrev fp2SubAfterC0Reads :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2SubAfterC0Reads
abbrev fp2SubAfterC0High :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2SubAfterC0High
abbrev fp2SubAfterC0Stores :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2SubAfterC0Stores
abbrev fp2SubC1 :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2SubC1
abbrev fp2SubAfterC1Reads :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2SubAfterC1Reads
abbrev fp2SubAfterC1High :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2SubAfterC1High
abbrev fp2SubFinalState :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2SubFinalState
abbrev fp2SubResult :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2SubResult
abbrev fp2SubScheduledA :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2SubScheduledA
abbrev fp2SubScheduledB :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2SubScheduledB

export Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
  (fp2SubReadState_memory fp2SubResult_eq_subSource
    fp2SubResult_canonical fp2SubResult_toField)

def fp2SubFuns : FunEnv Challenge.EvmProof.modexpExec.toDialect := fp2Funs

def fp2SubBody : Block Op :=
  match referenceCompiledBlock[15]? with
  | some (Stmt.funDef _ _ _ body) => body
  | _ => []

def fp2SubStmt0 : Stmt Op := fp2SubBody[0]!
def fp2SubStmt1 : Stmt Op := fp2SubBody[1]!
def fp2SubStmt2 : Stmt Op := fp2SubBody[2]!
def fp2SubStmt3 : Stmt Op := fp2SubBody[3]!
def fp2SubStmt4 : Stmt Op := fp2SubBody[4]!
def fp2SubStmt5 : Stmt Op := fp2SubBody[5]!

theorem fp2SubBody_eq : fp2SubBody =
    [fp2SubStmt0, fp2SubStmt1, fp2SubStmt2,
      fp2SubStmt3, fp2SubStmt4, fp2SubStmt5] := by
  rfl

theorem hoist_fp2SubBody :
    hoist Challenge.EvmProof.modexpExec.toDialect fp2SubBody = [] := by
  rfl

def fp2SubBodyFuns : FunEnv Challenge.EvmProof.modexpExec.toDialect :=
  [] :: fp2SubFuns

theorem fp2SubBodyFuns_eq :
    hoist Challenge.EvmProof.modexpExec.toDialect fp2SubBody :: fp2SubFuns =
      fp2SubBodyFuns := by
  rw [hoist_fp2SubBody]
  rfl

def fp2SubDecl : FDecl Challenge.EvmProof.modexpExec.toDialect :=
  { params := ["\x00111", "\x00112", "\x00113"]
    rets := []
    body := fp2SubBody }

theorem lookup_fp2Sub : lookupFun fp2SubFuns "\x0015" =
    some (fp2SubDecl, fp2SubFuns) := by
  rfl

def fp2SubInitialEnv (out a b : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  [("\x00111", out), ("\x00112", a), ("\x00113", b)]

end Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics
