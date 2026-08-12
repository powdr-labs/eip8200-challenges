import Challenge.Bls12381G2Msm.Reference.Proofs.SourceFpMulExec

set_option warningAsError true

/-! Frozen local definitions and reused pure refinement for G2MSM `fpInv`. -/

namespace Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics

open EvmSemantics EvmSemantics.EVM
open YulSemantics YulSemantics.EVM
open Challenge.Bls12381G2Msm.Reference.Proofs.Compilation

abbrev fpInvInputState :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fpInvInputState
abbrev fpInvResult :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fpInvResult
abbrev fpInvCallState :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fpInvCallState
abbrev fpInvFinalState :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fpInvFinalState
abbrev fpInvOutputLimbs :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fpInvOutputLimbs
abbrev fpInvInputLimbs :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fpInvInputLimbs

export Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics
  (fpInvInput_runModexp)

def fpInvFuns : FunEnv Challenge.EvmProof.modexpExec.toDialect :=
  [hoist Challenge.EvmProof.modexpExec.toDialect referenceCompiledBlock]

def fpInvBody : Block Op :=
  match referenceCompiledBlock[10]? with
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
  { params := ["\x0095", "\x0096"]
    rets := ["\x0097", "\x0098"]
    body := fpInvBody }

theorem lookup_fpInv : lookupFun fpInvFuns "\x0010" =
    some (fpInvDecl, fpInvFuns) := by
  rfl

def fpInvInitialEnv (hi lo : U256) :
    VEnv Challenge.EvmProof.modexpExec.toDialect :=
  [("\x0095", hi), ("\x0096", lo), ("\x0097", 0), ("\x0098", 0)]

theorem fpInvOutput_eq_invCanonical (yst : EvmState) (hi lo : U256)
    (ha : Challenge.Bls12381.ProofSupport.Fp.Canonical
      (fpInvInputLimbs hi lo)) :
    fpInvOutputLimbs yst hi lo =
      Challenge.Bls12381.ProofSupport.Fp.invCanonical
        (fpInvInputLimbs hi lo) :=
  Challenge.Bls12381G2Add.Reference.Proofs.SourceSemantics.fpInvOutput_eq_invCanonical
    yst hi lo ha

end Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics
