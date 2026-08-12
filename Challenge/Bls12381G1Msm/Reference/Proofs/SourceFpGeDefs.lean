import Challenge.Bls12381G1Msm.Reference.Proofs.Compilation
import Challenge.EvmProof.ModexpExec

set_option warningAsError true

/-! Frozen declaration boundary for the G1MSM `fpGeModulus` helper. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM
open Challenge.Bls12381G1Msm.Reference.Proofs.Compilation

def sourceFuns : FunEnv Challenge.EvmProof.modexpExec.toDialect :=
  [hoist Challenge.EvmProof.modexpExec.toDialect referenceBackendBlock]

def fpGeBody : Block Op :=
  match referenceBackendBlock[0]? with
  | some (Stmt.funDef _ _ _ body) => body
  | _ => []

def fpGeStmt : Stmt Op :=
  .assign ["\x0020"]
    (.builtin .or
      [.builtin .gt
        [.var "\x0018",
         .lit (.number 34565483545414906068789196026815425751)],
       .builtin .and
        [.builtin .eq
          [.var "\x0018",
           .lit (.number 34565483545414906068789196026815425751)],
         .builtin .iszero
          [.builtin .lt
            [.var "\x0019",
             .lit (.number
               45442060874369865957053122457065728162598490762543039060009208264153100167851)]]]])

theorem fpGeBody_eq : fpGeBody = [fpGeStmt] := by
  rfl

def fpGeDecl : FDecl Challenge.EvmProof.modexpExec.toDialect :=
  { params := ["\x0018", "\x0019"]
    rets := ["\x0020"]
    body := fpGeBody }

theorem lookup_fpGe : lookupFun sourceFuns "\x000" =
    some (fpGeDecl, sourceFuns) := by
  rfl

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
