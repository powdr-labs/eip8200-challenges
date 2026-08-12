import Challenge.Bls12381G2Msm.Reference.Proofs.Compilation

set_option warningAsError true

/-! Frozen G2MSM backend shapes used by the invalid-length proof. -/

namespace Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM
open Challenge.Bls12381G2Msm.Reference.Proofs.Compilation

def isFunctionDefinition {Op : Type} : Stmt Op → Bool
  | .funDef .. => true
  | _ => false

def sizeName : Ident := "\x00152"

def sizeStmt : Stmt Op :=
  .letDecl [sizeName] (some (.builtin .calldatasize []))

def invalidLengthStmt : Stmt Op :=
  .cond
    (.builtin .or
      [.builtin .iszero [.var sizeName],
       .builtin .mod [.var sizeName, .lit (.number 288)]])
    [.exprStmt (.builtin .invalid [])]

theorem reference_after_functions :
    referenceCompiledBlock.drop 31 =
      sizeStmt :: invalidLengthStmt :: referenceCompiledBlock.drop 33 := by
  rfl

theorem reference_function_prefix :
    (referenceCompiledBlock.take 31).all isFunctionDefinition = true := by
  rfl

theorem reference_function_prefix_length :
    (referenceCompiledBlock.take 31).length = 31 := by
  rfl

end Challenge.Bls12381G2Msm.Reference.Proofs.SourceSemantics
