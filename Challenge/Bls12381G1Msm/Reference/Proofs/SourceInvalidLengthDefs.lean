import Challenge.Bls12381G1Msm.Reference.Proofs.Compilation

set_option warningAsError true

/-! Frozen G1MSM backend shapes used by the invalid-length proof. -/

namespace Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM
open Challenge.Bls12381G1Msm.Reference.Proofs.Compilation

def isFunctionDefinition {Op : Type} : Stmt Op → Bool
  | .funDef .. => true
  | _ => false

def sizeName : Ident := "\x00146"

def sizeStmt : Stmt Op :=
  .letDecl [sizeName] (some (.builtin .calldatasize []))

def invalidLengthStmt : Stmt Op :=
  .cond
    (.builtin .or
      [.builtin .iszero [.var sizeName],
       .builtin .mod [.var sizeName, .lit (.number 160)]])
    [.exprStmt (.builtin .invalid [])]

theorem reference_after_functions :
    referenceBackendBlock.drop 11 =
      sizeStmt :: invalidLengthStmt :: referenceBackendBlock.drop 13 := by
  rfl

theorem reference_function_prefix :
    (referenceBackendBlock.take 11).all isFunctionDefinition = true := by
  rfl

theorem reference_function_prefix_length :
    (referenceBackendBlock.take 11).length = 11 := by
  rfl

end Challenge.Bls12381G1Msm.Reference.Proofs.SourceSemantics
