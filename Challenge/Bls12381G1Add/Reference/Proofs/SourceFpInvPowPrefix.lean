import Challenge.Bls12381G1Add.Reference.Proofs.SourceFpInvPowForLoop

set_option warningAsError true

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM
private abbrev D := Challenge.YulProof.ClosedEvm.dialect

def fpPowR2Lo : U256 := BitVec.ofNat 256
  92286679234085438351495039074048687640204382693166976402664901553327635873368
def fpPowR2Hi : U256 := BitVec.ofNat 256 86499536527081971458999430873902347

def fpPowBaseEnvWith (aHi aLo : U256) (base : MontResultValue) : VEnv D :=
  [("\x00127", base.lo), ("\x00128", base.hi)] ++ fpPowInitialEnv aHi aLo

theorem fpPowStmt0_shape : fpPowStmt0 =
    .letDecl ["\x00127", "\x00128"] (some (.call "\x0015"
      [.var "\x00124", .var "\x00123",
       .lit (.number 92286679234085438351495039074048687640204382693166976402664901553327635873368),
       .lit (.number 86499536527081971458999430873902347)])) := by
  rfl

theorem fpPowStmt1_shape : fpPowStmt1 =
    .letDecl ["\x00129"] (some (.var "\x00127")) := by rfl

theorem fpPowStmt2_shape : fpPowStmt2 =
    .letDecl ["\x00130"] (some (.var "\x00128")) := by rfl

theorem step_fpPowPrefix (aHi aLo : U256) (yst : EvmState) :
    ∃ base,
      ExecStmts D fpPowBodyFuns (fpPowInitialEnv aHi aLo) yst
        [fpPowStmt0, fpPowStmt1, fpPowStmt2]
        (fpPowAccEnv aHi aLo base base) yst .normal ∧
      NativeMontMulResult aLo aHi fpPowR2Lo fpPowR2Hi base.lo base.hi ∧
      PowAccInv (fpPowAccEnv aHi aLo base base) base base := by
  have hargs : EvalArgs D fpPowBodyFuns (fpPowInitialEnv aHi aLo) yst
      [.var "\x00124", .var "\x00123",
       .lit (.number 92286679234085438351495039074048687640204382693166976402664901553327635873368),
       .lit (.number 86499536527081971458999430873902347)]
      (.vals [aLo, aHi, fpPowR2Lo, fpPowR2Hi] yst) :=
    Step.argsCons
      (Step.argsCons
        (Step.argsCons
          (Step.argsCons Step.argsNil Step.lit)
          Step.lit)
        (Step.var (by rfl)))
      (Step.var (by rfl))
  obtain ⟨baseLo, baseHi, hcall, hbaseNative⟩ :=
    step_montMul2_nativeResult
      (callerFuns := fpPowBodyFuns) (V := fpPowInitialEnv aHi aLo)
      (args := [.var "\x00124", .var "\x00123",
        .lit (.number 92286679234085438351495039074048687640204382693166976402664901553327635873368),
        .lit (.number 86499536527081971458999430873902347)])
      (yst := yst) aLo aHi fpPowR2Lo fpPowR2Hi
      lookup_montMul2_fpPowBody hargs
  let base : MontResultValue := { lo := baseLo, hi := baseHi }
  have hstmt0 : ExecStmt D fpPowBodyFuns (fpPowInitialEnv aHi aLo) yst
      fpPowStmt0 (fpPowBaseEnvWith aHi aLo base) yst .normal := by
    rw [fpPowStmt0_shape]
    exact Step.letVal hcall rfl
  have hstmt1 : ExecStmt D fpPowBodyFuns (fpPowBaseEnvWith aHi aLo base) yst
      fpPowStmt1
      (("\x00129", base.lo) :: fpPowBaseEnvWith aHi aLo base) yst .normal := by
    rw [fpPowStmt1_shape]
    have hvar : EvalExpr D fpPowBodyFuns (fpPowBaseEnvWith aHi aLo base) yst
        (.var "\x00127") (.vals [base.lo] yst) := Step.var (by rfl)
    exact Step.letVal hvar rfl
  have hstmt2 : ExecStmt D fpPowBodyFuns
      (("\x00129", base.lo) :: fpPowBaseEnvWith aHi aLo base) yst fpPowStmt2
      (fpPowAccEnv aHi aLo base base) yst .normal := by
    rw [fpPowStmt2_shape]
    have hvar : EvalExpr D fpPowBodyFuns
        (("\x00129", base.lo) :: fpPowBaseEnvWith aHi aLo base) yst
        (.var "\x00128") (.vals [base.hi] yst) := Step.var (by rfl)
    exact Step.letVal hvar rfl
  have hnil : ExecStmts D fpPowBodyFuns
      (fpPowAccEnv aHi aLo base base) yst []
      (fpPowAccEnv aHi aLo base base) yst .normal := Step.seqNil
  refine ⟨base,
    Step.seqCons hstmt0 (Step.seqCons hstmt1 (Step.seqCons hstmt2 hnil)),
    hbaseNative, ?_⟩
  exact ⟨by rfl, by rfl, by rfl, by rfl⟩

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
