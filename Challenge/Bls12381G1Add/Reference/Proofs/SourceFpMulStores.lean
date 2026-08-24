import Challenge.Bls12381G1Add.Reference.Proofs.SourceFpMulStep0

set_option warningAsError true

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

def fpReduceCorrectionLocalEnv (product : FullMulValue)
    (value : FpMulWideValue) (localName : String) :
    VEnv Challenge.YulProof.ClosedEvm.exec.toDialect :=
  [(localName, value.lo - fpMulModulusWide.lo)] ++
    fpReduceValueEnv product value

def fpReduceCorrectionHighEnv (product : FullMulValue)
    (value : FpMulWideValue) (localName : String) :
    VEnv Challenge.YulProof.ClosedEvm.exec.toDialect :=
  [(localName, value.lo - fpMulModulusWide.lo)] ++ fpReduceValueEnv product
    { hi := (fpMulSubWide value fpMulModulusWide).hi, lo := value.lo }

def fpReduceCorrectionFinalEnv (product : FullMulValue)
    (value : FpMulWideValue) (localName : String) :
    VEnv Challenge.YulProof.ClosedEvm.exec.toDialect :=
  [(localName, value.lo - fpMulModulusWide.lo)] ++
    fpReduceValueEnv product (fpMulSubWide value fpMulModulusWide)

theorem exec_fpReduceCorrectionBlock58 (product : FullMulValue)
    (value : FpMulWideValue) (yst : EvmState) :
    Interp.execStmt Challenge.YulProof.ClosedEvm.exec 55 fpReduceBodyFuns
      (fpReduceValueEnv product value) yst
      (.block [
        .letDecl ["\x00164"] (some (.builtin .sub
          [.var "\x00137", .var "\x00160"])),
        .assign ["\x00136"] (.builtin .sub
          [.builtin .sub [.var "\x00136", .var "\x00159"],
            .builtin .gt [.var "\x00160", .var "\x00137"]]),
        .assign ["\x00137"] (.var "\x00164")]) =
    .ok (fpReduceValueEnv product (fpMulSubWide value fpMulModulusWide),
      yst, .normal) := by
  have h0 : Interp.execStmt Challenge.YulProof.ClosedEvm.exec 53
      ([] :: fpReduceBodyFuns) (fpReduceValueEnv product value) yst
      (.letDecl ["\x00164"] (some (.builtin .sub
        [.var "\x00137", .var "\x00160"]))) =
      .ok (fpReduceCorrectionLocalEnv product value "\x00164", yst,
        .normal) := by rfl
  have h1 : Interp.execStmt Challenge.YulProof.ClosedEvm.exec 52
      ([] :: fpReduceBodyFuns)
      (fpReduceCorrectionLocalEnv product value "\x00164") yst
      (.assign ["\x00136"] (.builtin .sub
        [.builtin .sub [.var "\x00136", .var "\x00159"],
          .builtin .gt [.var "\x00160", .var "\x00137"]])) =
      .ok (fpReduceCorrectionHighEnv product value "\x00164", yst,
        .normal) := by rfl
  have h2 : Interp.execStmt Challenge.YulProof.ClosedEvm.exec 51
      ([] :: fpReduceBodyFuns)
      (fpReduceCorrectionHighEnv product value "\x00164") yst
      (.assign ["\x00137"] (.var "\x00164")) =
      .ok (fpReduceCorrectionFinalEnv product value "\x00164", yst,
        .normal) := by rfl
  have hstmts : Interp.execStmts Challenge.YulProof.ClosedEvm.exec 54
      ([] :: fpReduceBodyFuns) (fpReduceValueEnv product value) yst [
        .letDecl ["\x00164"] (some (.builtin .sub
          [.var "\x00137", .var "\x00160"])),
        .assign ["\x00136"] (.builtin .sub
          [.builtin .sub [.var "\x00136", .var "\x00159"],
            .builtin .gt [.var "\x00160", .var "\x00137"]]),
        .assign ["\x00137"] (.var "\x00164")] =
      .ok (fpReduceCorrectionFinalEnv product value "\x00164", yst,
        .normal) := by
    exact Interp.execStmts_cons_normal h0
      (Interp.execStmts_cons_normal h1
        (Interp.execStmts_cons_normal h2 (by rfl)))
  rw [Interp.execStmt]
  change (do
    let (V, st, outcome) ← Interp.execStmts Challenge.YulProof.ClosedEvm.exec 54
      ([] :: fpReduceBodyFuns) (fpReduceValueEnv product value) yst [
        .letDecl ["\x00164"] (some (.builtin .sub
          [.var "\x00137", .var "\x00160"])),
        .assign ["\x00136"] (.builtin .sub
          [.builtin .sub [.var "\x00136", .var "\x00159"],
            .builtin .gt [.var "\x00160", .var "\x00137"]]),
        .assign ["\x00137"] (.var "\x00164")]
    return (restore (fpReduceValueEnv product value) V, st, outcome)) = _
  rw [hstmts]
  rfl

theorem exec_fpReduceCorrectionBlock57 (product : FullMulValue)
    (value : FpMulWideValue) (yst : EvmState) :
    Interp.execStmt Challenge.YulProof.ClosedEvm.exec 54 fpReduceBodyFuns
      (fpReduceValueEnv product value) yst
      (.block [
        .letDecl ["\x00165"] (some (.builtin .sub
          [.var "\x00137", .var "\x00160"])),
        .assign ["\x00136"] (.builtin .sub
          [.builtin .sub [.var "\x00136", .var "\x00159"],
            .builtin .gt [.var "\x00160", .var "\x00137"]]),
        .assign ["\x00137"] (.var "\x00165")]) =
    .ok (fpReduceValueEnv product (fpMulSubWide value fpMulModulusWide),
      yst, .normal) := by
  have h0 : Interp.execStmt Challenge.YulProof.ClosedEvm.exec 52
      ([] :: fpReduceBodyFuns) (fpReduceValueEnv product value) yst
      (.letDecl ["\x00165"] (some (.builtin .sub
        [.var "\x00137", .var "\x00160"]))) =
      .ok (fpReduceCorrectionLocalEnv product value "\x00165", yst,
        .normal) := by rfl
  have h1 : Interp.execStmt Challenge.YulProof.ClosedEvm.exec 51
      ([] :: fpReduceBodyFuns)
      (fpReduceCorrectionLocalEnv product value "\x00165") yst
      (.assign ["\x00136"] (.builtin .sub
        [.builtin .sub [.var "\x00136", .var "\x00159"],
          .builtin .gt [.var "\x00160", .var "\x00137"]])) =
      .ok (fpReduceCorrectionHighEnv product value "\x00165", yst,
        .normal) := by rfl
  have h2 : Interp.execStmt Challenge.YulProof.ClosedEvm.exec 50
      ([] :: fpReduceBodyFuns)
      (fpReduceCorrectionHighEnv product value "\x00165") yst
      (.assign ["\x00137"] (.var "\x00165")) =
      .ok (fpReduceCorrectionFinalEnv product value "\x00165", yst,
        .normal) := by rfl
  have hstmts : Interp.execStmts Challenge.YulProof.ClosedEvm.exec 53
      ([] :: fpReduceBodyFuns) (fpReduceValueEnv product value) yst [
        .letDecl ["\x00165"] (some (.builtin .sub
          [.var "\x00137", .var "\x00160"])),
        .assign ["\x00136"] (.builtin .sub
          [.builtin .sub [.var "\x00136", .var "\x00159"],
            .builtin .gt [.var "\x00160", .var "\x00137"]]),
        .assign ["\x00137"] (.var "\x00165")] =
      .ok (fpReduceCorrectionFinalEnv product value "\x00165", yst,
        .normal) := by
    exact Interp.execStmts_cons_normal h0
      (Interp.execStmts_cons_normal h1
        (Interp.execStmts_cons_normal h2 (by rfl)))
  rw [Interp.execStmt]
  change (do
    let (V, st, outcome) ← Interp.execStmts Challenge.YulProof.ClosedEvm.exec 53
      ([] :: fpReduceBodyFuns) (fpReduceValueEnv product value) yst [
        .letDecl ["\x00165"] (some (.builtin .sub
          [.var "\x00137", .var "\x00160"])),
        .assign ["\x00136"] (.builtin .sub
          [.builtin .sub [.var "\x00136", .var "\x00159"],
            .builtin .gt [.var "\x00160", .var "\x00137"]]),
        .assign ["\x00137"] (.var "\x00165")]
    return (restore (fpReduceValueEnv product value) V, st, outcome)) = _
  rw [hstmts]
  rfl

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
