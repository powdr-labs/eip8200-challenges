import Challenge.Bls12381G2Msm.Reference.Proofs.SourceFp2Predicates
import Challenge.Bls12381G2Add.Reference.Proofs.SourceFp2AddRefinement

set_option warningAsError true

/-! Frozen local boundary and reused pure memory graph for G2MSM `fp2Add`. -/

namespace Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM
open Challenge.Bls12381G2Msm.Reference.Proofs.Compilation

abbrev fp2AddReadState :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2AddReadState
abbrev fp2AddC0 :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2AddC0
abbrev fp2AddAfterC0Reads :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2AddAfterC0Reads
abbrev fp2AddAfterC0High :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2AddAfterC0High
abbrev fp2AddAfterC0Stores :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2AddAfterC0Stores
abbrev fp2AddC1 :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2AddC1
abbrev fp2AddAfterC1Reads :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2AddAfterC1Reads
abbrev fp2AddAfterC1High :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2AddAfterC1High
abbrev fp2AddFinalState :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2AddFinalState
abbrev fp2AddResult :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2AddResult
abbrev fp2AddScheduledA :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2AddScheduledA
abbrev fp2AddScheduledB :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fp2AddScheduledB

export Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
  (fp2AddReadState_memory fp2AddResult_eq_addSource
    fp2AddResult_canonical fp2AddResult_toField)

def fp2AddFuns : FunEnv Challenge.EvmProof.modexpExec.toDialect := fp2Funs

def fp2AddBody : Block Op :=
  match referenceCompiledBlock[14]? with
  | some (Stmt.funDef _ _ _ body) => body
  | _ => []

def fp2AddStmt0 : Stmt Op := fp2AddBody[0]!
def fp2AddStmt1 : Stmt Op := fp2AddBody[1]!
def fp2AddStmt2 : Stmt Op := fp2AddBody[2]!
def fp2AddStmt3 : Stmt Op := fp2AddBody[3]!
def fp2AddStmt4 : Stmt Op := fp2AddBody[4]!
def fp2AddStmt5 : Stmt Op := fp2AddBody[5]!

theorem fp2AddBody_eq : fp2AddBody =
    [fp2AddStmt0, fp2AddStmt1, fp2AddStmt2,
      fp2AddStmt3, fp2AddStmt4, fp2AddStmt5] := by
  rfl

theorem hoist_fp2AddBody :
    hoist Challenge.EvmProof.modexpExec.toDialect fp2AddBody = [] := by
  rfl

def fp2AddBodyFuns : FunEnv Challenge.EvmProof.modexpExec.toDialect :=
  [] :: fp2AddFuns

theorem fp2AddBodyFuns_eq :
    hoist Challenge.EvmProof.modexpExec.toDialect fp2AddBody :: fp2AddFuns =
      fp2AddBodyFuns := by
  rw [hoist_fp2AddBody]
  rfl

def fp2AddDecl : FDecl Challenge.EvmProof.modexpExec.toDialect :=
  { params := ["\x00106", "\x00107", "\x00108"]
    rets := []
    body := fp2AddBody }

theorem lookup_fp2Add : lookupFun fp2AddFuns "\x0014" =
    some (fp2AddDecl, fp2AddFuns) := by
  rfl

def fp2AddInitialEnv (out a b : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  [("\x00106", out), ("\x00107", a), ("\x00108", b)]

end Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics
