import Challenge.Bls12381G1Msm.Reference.Proofs.SourceFpAddRefinement

set_option warningAsError true

/-! Frozen declaration boundary for the G1MSM `fullMul` helper. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM
open Challenge.Bls12381G1Msm.Reference.Proofs.Compilation

def fullMulBody : Block Op :=
  match referenceBackendBlock[5]? with
  | some (Stmt.funDef _ _ _ body) => body
  | _ => []

theorem fullMulBody_length : fullMulBody.length = 13 := by
  rfl

theorem hoist_fullMulBody :
    hoist Challenge.EvmProof.modexpExec.toDialect fullMulBody = [] := by
  rfl

def fullMulBodyFuns : FunEnv Challenge.EvmProof.modexpExec.toDialect :=
  [] :: sourceFuns

def fullMulDecl : FDecl Challenge.EvmProof.modexpExec.toDialect :=
  { params := ["\x0052", "\x0053", "\x0054", "\x0055"]
    rets := ["\x0056", "\x0057", "\x0058"]
    body := fullMulBody }

theorem lookup_fullMul : lookupFun sourceFuns "\x006" =
    some (fullMulDecl, sourceFuns) := by
  rfl

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
