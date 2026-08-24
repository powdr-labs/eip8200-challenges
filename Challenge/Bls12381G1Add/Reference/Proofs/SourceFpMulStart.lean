import Challenge.Bls12381G1Add.Reference.Proofs.SourceFpMulExec

set_option warningAsError true

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def fpReducePEnv (product : FullMulValue) :
    VEnv Challenge.YulProof.ClosedEvm.exec.toDialect :=
  [("\x00160", fpMulModulusWide.lo), ("\x00159", fpMulModulusWide.hi)] ++
    fpReduceQEnv product

def fpReduceValueEnv (product : FullMulValue) (value : FpMulWideValue) :
    VEnv Challenge.YulProof.ClosedEvm.exec.toDialect :=
  [("\x00160", fpMulModulusWide.lo), ("\x00159", fpMulModulusWide.hi),
    ("\x00139", (fpMulBarrettQuotient product).hi),
    ("\x00138", (fpMulBarrettQuotient product).lo),
    ("\x00133", product.r2), ("\x00134", product.r1),
    ("\x00135", product.r0), ("\x00136", value.hi),
    ("\x00137", value.lo)]

def fpReduceReturnEnv (product : FullMulValue) (value : FpMulWideValue) :
    VEnv Challenge.YulProof.ClosedEvm.exec.toDialect :=
  [("\x00133", product.r2), ("\x00134", product.r1),
    ("\x00135", product.r0), ("\x00136", value.hi),
    ("\x00137", value.lo)]

theorem restore_fpReduceValueEnv (product : FullMulValue)
    (value : FpMulWideValue) :
    restore (fpReduceInitialEnv product) (fpReduceValueEnv product value) =
      fpReduceReturnEnv product value := by
  rfl

def fpReduceReturned (product : FullMulValue) (value : FpMulWideValue) :
    U256 × U256 :=
  ((VEnv.get (fpReduceReturnEnv product value) "\x00136").getD 0,
    (VEnv.get (fpReduceReturnEnv product value) "\x00137").getD 0)

theorem fpReduceReturned_eq (product : FullMulValue) (value : FpMulWideValue) :
    fpReduceReturned product value = (value.hi, value.lo) := by
  rfl

theorem fpReduceReturn_hi (product : FullMulValue) (value : FpMulWideValue) :
    (VEnv.get (fpReduceReturnEnv product value) "\x00136").getD 0 =
      value.hi := by
  rfl

theorem fpReduceReturn_lo (product : FullMulValue) (value : FpMulWideValue) :
    (VEnv.get (fpReduceReturnEnv product value) "\x00137").getD 0 =
      value.lo := by
  rfl

theorem fpReduceReturn_values (product : FullMulValue)
    (value : FpMulWideValue) :
    [(VEnv.get (fpReduceReturnEnv product value) "\x00136").getD 0,
      (VEnv.get (fpReduceReturnEnv product value) "\x00137").getD 0] =
      [value.hi, value.lo] := by
  rfl

theorem exec_fpReducePDecls (product : FullMulValue) (yst : EvmState) :
    Interp.execStmts Challenge.YulProof.ClosedEvm.exec 60 fpReduceBodyFuns
      (fpReduceQEnv product) yst [fpReduceStmt3, fpReduceStmt4] =
    .ok (fpReducePEnv product, yst, .normal) := by
  rfl

theorem exec_fpReduceRemainder (product : FullMulValue) (yst : EvmState) :
    Interp.execStmt Challenge.YulProof.ClosedEvm.exec 57 fpReduceBodyFuns
      (fpReducePEnv product) yst fpReduceStmt5 =
    .ok (fpReduceValueEnv product (fpMulRemainderValue product),
      yst, .normal) := by
  rfl

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
