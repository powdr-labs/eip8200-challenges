import Challenge.Bls12381G1Add.Reference.Proofs.SourceFpInvExecDefs

set_option warningAsError true

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

example : fpInvBody =
    [fpInvStmt0, fpInvStmt1, fpInvStmt2, fpInvStmt3, fpInvStmt4,
      fpInvStmt5, fpInvStmt6, fpInvStmt7, fpInvStmt8] :=
  fpInvBody_eq

example : lookupFun fpInvFuns "\x0010" = some (fpInvDecl, fpInvFuns) :=
  lookup_fpInv

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.fpInvBody_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms fpInvBody_eq

/-- info: 'Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics.lookup_fpInv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms lookup_fpInv

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
