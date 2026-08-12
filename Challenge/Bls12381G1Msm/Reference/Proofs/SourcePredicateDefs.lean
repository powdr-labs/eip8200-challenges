import Challenge.Bls12381G1Msm.Reference.Proofs.SourceFpGeDefs

set_option warningAsError true

/-! Frozen declaration boundary for the G1MSM field predicates. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM
open Challenge.Bls12381G1Msm.Reference.Proofs.Compilation

def fpValidBody : Block Op :=
  match referenceBackendBlock[1]? with
  | some (Stmt.funDef _ _ _ body) => body
  | _ => []

def fpValidStmt : Stmt Op :=
  .assign ["\x0025"]
    (.builtin .iszero [.call "\x000" [.var "\x0023", .var "\x0024"]])

theorem fpValidBody_eq : fpValidBody = [fpValidStmt] := by
  rfl

def fpValidDecl : FDecl Challenge.EvmProof.modexpExec.toDialect :=
  { params := ["\x0023", "\x0024"]
    rets := ["\x0025"]
    body := fpValidBody }

theorem lookup_fpValid : lookupFun sourceFuns "\x001" =
    some (fpValidDecl, sourceFuns) := by
  rfl

def fpZeroBody : Block Op :=
  match referenceBackendBlock[2]? with
  | some (Stmt.funDef _ _ _ body) => body
  | _ => []

def fpZeroStmt : Stmt Op :=
  .assign ["\x0028"]
    (.builtin .and
      [.builtin .iszero [.var "\x0026"],
       .builtin .iszero [.var "\x0027"]])

theorem fpZeroBody_eq : fpZeroBody = [fpZeroStmt] := by
  rfl

def fpZeroDecl : FDecl Challenge.EvmProof.modexpExec.toDialect :=
  { params := ["\x0026", "\x0027"]
    rets := ["\x0028"]
    body := fpZeroBody }

theorem lookup_fpZero : lookupFun sourceFuns "\x002" =
    some (fpZeroDecl, sourceFuns) := by
  rfl

def fpEqBody : Block Op :=
  match referenceBackendBlock[3]? with
  | some (Stmt.funDef _ _ _ body) => body
  | _ => []

def fpEqStmt : Stmt Op :=
  .assign ["\x0033"]
    (.builtin .and
      [.builtin .eq [.var "\x0029", .var "\x0031"],
       .builtin .eq [.var "\x0030", .var "\x0032"]])

theorem fpEqBody_eq : fpEqBody = [fpEqStmt] := by
  rfl

def fpEqDecl : FDecl Challenge.EvmProof.modexpExec.toDialect :=
  { params := ["\x0029", "\x0030", "\x0031", "\x0032"]
    rets := ["\x0033"]
    body := fpEqBody }

theorem lookup_fpEq : lookupFun sourceFuns "\x003" =
    some (fpEqDecl, sourceFuns) := by
  rfl

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
