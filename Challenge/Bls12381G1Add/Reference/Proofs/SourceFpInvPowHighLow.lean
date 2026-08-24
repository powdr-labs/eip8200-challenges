import Challenge.Bls12381G1Add.Reference.Proofs.SourceFpInvPowPrefix

set_option warningAsError true

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM
private abbrev D := Challenge.YulProof.ClosedEvm.dialect

def fpPowHighWordNat : Nat := 34565483545414906068789196026815425751
def fpPowLowWordNat : Nat :=
  45442060874369865957053122457065728162598490762543039060009208264153100167849

theorem fpPowStmt3_shape : fpPowStmt3 =
    fpPowForStmt "\x00131" fpPowHighWordNat 124 := by rfl

theorem fpPowStmt4_shape : fpPowStmt4 =
    fpPowForStmt "\x00132" fpPowLowWordNat 256 := by rfl

/-- The two frozen exponent windows execute sequentially, with the high-window
result becoming the low-window accumulator. -/
theorem step_fpPowHighLow (aHi aLo : U256) (base : MontResultValue)
    (yst : EvmState) :
    ∃ Vhigh Vlow afterHigh afterLow,
      ExecStmts D fpPowBodyFuns (fpPowAccEnv aHi aLo base base) yst
        [fpPowStmt3, fpPowStmt4] Vlow yst .normal ∧
      PowAccInv Vhigh base afterHigh ∧
      PowAccInv Vlow base afterLow ∧
      NativeFoldDown base fpPowHighWordNat 124 base afterHigh ∧
      NativeFoldDown base fpPowLowWordNat 256 afterHigh afterLow := by
  have hstart : PowAccInv (fpPowAccEnv aHi aLo base base) base base :=
    ⟨by rfl, by rfl, by rfl, by rfl⟩
  obtain ⟨Vhigh, afterHigh, hhigh, hhighInv, hhighFold⟩ :=
    step_fpPowForLoop "\x00131" base fpPowHighWordNat 124
      (fpPowAccEnv aHi aLo base base) base yst hstart
      (by norm_num) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨Vlow, afterLow, hlow, hlowInv, hlowFold⟩ :=
    step_fpPowForLoop "\x00132" base fpPowLowWordNat 256
      Vhigh afterHigh yst hhighInv
      (by norm_num) (by decide) (by decide) (by decide) (by decide)
  rw [← fpPowStmt3_shape] at hhigh
  rw [← fpPowStmt4_shape] at hlow
  have hnil : ExecStmts D fpPowBodyFuns Vlow yst [] Vlow yst .normal :=
    Step.seqNil
  exact ⟨Vhigh, Vlow, afterHigh, afterLow,
    Step.seqCons hhigh (Step.seqCons hlow hnil),
    hhighInv, hlowInv, hhighFold, hlowFold⟩

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
