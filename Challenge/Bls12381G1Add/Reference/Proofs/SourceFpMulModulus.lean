import Challenge.Bls12381G1Add.Reference.Proofs.SourceFpMulStores

set_option warningAsError true

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

private def correction64 : Block Op :=
  [.letDecl ["\x00164"] (some (.builtin .sub
      [.var "\x00137", .var "\x00160"])),
   .assign ["\x00136"] (.builtin .sub
      [.builtin .sub [.var "\x00136", .var "\x00159"],
        .builtin .gt [.var "\x00160", .var "\x00137"]]),
   .assign ["\x00137"] (.var "\x00164")]

private def correction65 : Block Op :=
  [.letDecl ["\x00165"] (some (.builtin .sub
      [.var "\x00137", .var "\x00160"])),
   .assign ["\x00136"] (.builtin .sub
      [.builtin .sub [.var "\x00136", .var "\x00159"],
        .builtin .gt [.var "\x00160", .var "\x00137"]]),
   .assign ["\x00137"] (.var "\x00165")]

theorem exec_fpReduceCorrection58 (product : FullMulValue)
    (value : FpMulWideValue) (yst : EvmState) :
    Interp.execStmt Challenge.YulProof.ClosedEvm.exec 56 fpReduceBodyFuns
      (fpReduceValueEnv product value) yst
      (.cond (.call "\x000" [.var "\x00136", .var "\x00137"])
        correction64) =
    .ok (fpReduceValueEnv product (fpMulCorrectOnce value), yst, .normal) := by
  rw [Interp.execStmt, eval_fpReduceGe58 product value yst]
  change (if fpGeModulusValue value.hi value.lo = 0 then
    .ok (fpReduceValueEnv product value, yst, .normal)
  else Interp.execStmt Challenge.YulProof.ClosedEvm.exec 55 fpReduceBodyFuns
    (fpReduceValueEnv product value) yst (.block correction64)) = _
  by_cases hzero : fpGeModulusValue value.hi value.lo = 0
  · rw [if_pos hzero]
    rw [show fpMulCorrectOnce value = value by
      unfold fpMulCorrectOnce
      rw [if_pos hzero]]
  · rw [if_neg hzero]
    rw [show correction64 =
      [.letDecl ["\x00164"] (some (.builtin .sub
          [.var "\x00137", .var "\x00160"])),
       .assign ["\x00136"] (.builtin .sub
          [.builtin .sub [.var "\x00136", .var "\x00159"],
            .builtin .gt [.var "\x00160", .var "\x00137"]]),
       .assign ["\x00137"] (.var "\x00164")] by rfl,
      exec_fpReduceCorrectionBlock58 product value yst]
    rw [show fpMulCorrectOnce value =
        fpMulSubWide value fpMulModulusWide by
      unfold fpMulCorrectOnce
      rw [if_neg hzero]]

theorem exec_fpReduceCorrection57 (product : FullMulValue)
    (value : FpMulWideValue) (yst : EvmState) :
    Interp.execStmt Challenge.YulProof.ClosedEvm.exec 55 fpReduceBodyFuns
      (fpReduceValueEnv product value) yst
      (.cond (.call "\x000" [.var "\x00136", .var "\x00137"])
        correction65) =
    .ok (fpReduceValueEnv product (fpMulCorrectOnce value), yst, .normal) := by
  rw [Interp.execStmt, eval_fpReduceGe57 product value yst]
  change (if fpGeModulusValue value.hi value.lo = 0 then
    .ok (fpReduceValueEnv product value, yst, .normal)
  else Interp.execStmt Challenge.YulProof.ClosedEvm.exec 54 fpReduceBodyFuns
    (fpReduceValueEnv product value) yst (.block correction65)) = _
  by_cases hzero : fpGeModulusValue value.hi value.lo = 0
  · rw [if_pos hzero]
    rw [show fpMulCorrectOnce value = value by
      unfold fpMulCorrectOnce
      rw [if_pos hzero]]
  · rw [if_neg hzero]
    rw [show correction65 =
      [.letDecl ["\x00165"] (some (.builtin .sub
          [.var "\x00137", .var "\x00160"])),
       .assign ["\x00136"] (.builtin .sub
          [.builtin .sub [.var "\x00136", .var "\x00159"],
            .builtin .gt [.var "\x00160", .var "\x00137"]]),
       .assign ["\x00137"] (.var "\x00165")] by rfl,
      exec_fpReduceCorrectionBlock57 product value yst]
    rw [show fpMulCorrectOnce value =
        fpMulSubWide value fpMulModulusWide by
      unfold fpMulCorrectOnce
      rw [if_neg hzero]]

theorem exec_fpReduceCorrection1 (product : FullMulValue) (yst : EvmState) :
    Interp.execStmt Challenge.YulProof.ClosedEvm.exec 56 fpReduceBodyFuns
      (fpReduceValueEnv product (fpMulRemainderValue product)) yst
        fpReduceStmt6 =
    .ok (fpReduceValueEnv product
      (fpMulCorrectOnce (fpMulRemainderValue product)), yst, .normal) := by
  rw [show fpReduceStmt6 =
    .cond (.call "\x000" [.var "\x00136", .var "\x00137"])
      correction64 by rfl]
  exact exec_fpReduceCorrection58 product (fpMulRemainderValue product) yst

theorem exec_fpReduceCorrection2 (product : FullMulValue) (yst : EvmState) :
    Interp.execStmt Challenge.YulProof.ClosedEvm.exec 55 fpReduceBodyFuns
      (fpReduceValueEnv product
        (fpMulCorrectOnce (fpMulRemainderValue product))) yst fpReduceStmt7 =
    .ok (fpReduceValueEnv product (fpReduceProductValue product),
      yst, .normal) := by
  rw [show fpReduceStmt7 =
    .cond (.call "\x000" [.var "\x00136", .var "\x00137"])
      correction65 by rfl]
  simpa only [fpReduceProductValue] using
    exec_fpReduceCorrection57 product
      (fpMulCorrectOnce (fpMulRemainderValue product)) yst

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
