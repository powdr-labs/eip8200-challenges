import Challenge.Bls12381G1Add.Reference.Proofs.SourceFpInvPowLoopCountdown

set_option warningAsError true

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM
private abbrev D := Challenge.YulProof.ClosedEvm.dialect

structure PowAccInv (V : VEnv D) (base acc : MontResultValue) : Prop where
  accLo : VEnv.get V "\x00129" = some acc.lo
  accHi : VEnv.get V "\x00130" = some acc.hi
  baseLo : VEnv.get V "\x00127" = some base.lo
  baseHi : VEnv.get V "\x00128" = some base.hi

def fpPowForInit (bitName : Ident) (count : Nat) : Block Op :=
  [.letDecl [bitName] (some (.lit (.number count)))]

def fpPowForStmt (bitName : Ident) (word count : Nat) : Stmt Op :=
  .forLoop (fpPowForInit bitName count) (fpPowLoopGuard bitName) []
    (fpPowLoopBody bitName word)

theorem step_fpPowForInit {V : VEnv D} (bitName : Ident) (count : Nat)
    (base acc : MontResultValue) (yst : EvmState)
    (hinv : PowAccInv V base acc)
    (hfreshLo : bitName ≠ "\x00129") (hfreshHi : bitName ≠ "\x00130")
    (hfreshBaseLo : bitName ≠ "\x00127")
    (hfreshBaseHi : bitName ≠ "\x00128") :
    ExecStmts D loopFuns V yst (fpPowForInit bitName count)
      ((bitName, BitVec.ofNat 256 count) :: V) yst .normal ∧
    PowLoopInv ((bitName, BitVec.ofNat 256 count) :: V)
      bitName count base acc ∧
    PowLoopHead ((bitName, BitVec.ofNat 256 count) :: V) bitName count := by
  have hlit : EvalExpr D loopFuns V yst (.lit (.number count))
      (.vals [BitVec.ofNat 256 count] yst) := Step.lit
  have hstmt : ExecStmt D loopFuns V yst
      (.letDecl [bitName] (some (.lit (.number count))))
      ((bitName, BitVec.ofNat 256 count) :: V) yst .normal :=
    Step.letVal hlit rfl
  have hnil : ExecStmts D loopFuns
      ((bitName, BitVec.ofNat 256 count) :: V) yst []
      ((bitName, BitVec.ofNat 256 count) :: V) yst .normal := Step.seqNil
  refine ⟨Step.seqCons hstmt hnil, ?_, ⟨V, rfl⟩⟩
  constructor
  · simp [VEnv.get]
  · simpa [VEnv.get, hfreshLo] using hinv.accLo
  · simpa [VEnv.get, hfreshHi] using hinv.accHi
  · simpa [VEnv.get, hfreshBaseLo] using hinv.baseLo
  · simpa [VEnv.get, hfreshBaseHi] using hinv.baseHi

theorem PowLoopInv.tail {V tail : VEnv D} {bitName : Ident} {bit : Nat}
    {base acc : MontResultValue}
    (hinv : PowLoopInv V bitName bit base acc)
    (hhead : V = (bitName, BitVec.ofNat 256 bit) :: tail)
    (hfreshLo : bitName ≠ "\x00129") (hfreshHi : bitName ≠ "\x00130")
    (hfreshBaseLo : bitName ≠ "\x00127")
    (hfreshBaseHi : bitName ≠ "\x00128") :
    PowAccInv tail base acc := by
  subst V
  constructor
  · simpa [VEnv.get, hfreshLo] using hinv.accLo
  · simpa [VEnv.get, hfreshHi] using hinv.accHi
  · simpa [VEnv.get, hfreshBaseLo] using hinv.baseLo
  · simpa [VEnv.get, hfreshBaseHi] using hinv.baseHi

/-- Execute one complete source `for` loop and remove only its local bit
binding at scope exit. -/
theorem step_fpPowForLoop (bitName : Ident) (aHi aLo : U256)
    (base : MontResultValue)
    (word count : Nat) (V : VEnv D) (acc : MontResultValue) (yst : EvmState)
    (hinv : PowAccInv V base acc)
    (hframe : V = fpPowAccEnv aHi aLo base acc)
    (hbound : count < 2 ^ 256)
    (hfreshLo : bitName ≠ "\x00129") (hfreshHi : bitName ≠ "\x00130")
    (hfreshBaseLo : bitName ≠ "\x00127")
    (hfreshBaseHi : bitName ≠ "\x00128") :
    ∃ result,
      ExecStmt D fpPowBodyFuns V yst (fpPowForStmt bitName word count)
        (fpPowAccEnv aHi aLo base result) yst .normal ∧
      NativeFoldDown base word count acc result := by
  obtain ⟨hinit, hloopInv, hloopHead⟩ :=
    step_fpPowForInit bitName count base acc yst hinv
      hfreshLo hfreshHi hfreshBaseLo hfreshBaseHi
  have hloopFrame : PowLoopFrame
      ((bitName, BitVec.ofNat 256 count) :: V)
      aHi aLo bitName count base acc := by
    unfold PowLoopFrame
    rw [hframe]
  obtain ⟨Vfinal, result, hloop, _hfinalLength, _hfinalInv, _hfinalHead,
      hfinalFrame, hfold⟩ :=
    step_fpPowLoop bitName aHi aLo base word count
      ((bitName, BitVec.ofNat 256 count) :: V) acc yst
      hloopInv hloopHead hloopFrame hbound
      hfreshLo hfreshHi hfreshBaseLo hfreshBaseHi
  have hrestore : restore V Vfinal = fpPowAccEnv aHi aLo base result := by
    rw [hfinalFrame, hframe]
    rfl
  have hinit' : ExecStmts D
      (hoist D (fpPowForInit bitName count) :: fpPowBodyFuns) V yst
      (fpPowForInit bitName count)
      ((bitName, BitVec.ofNat 256 count) :: V) yst .normal := by
    simpa [loopFuns, fpPowForInit, hoist] using hinit
  have hfor := Step.forLoop (funs := fpPowBodyFuns) hinit' hloop
  change ExecStmt D fpPowBodyFuns V yst (fpPowForStmt bitName word count)
    (restore V Vfinal) yst .normal at hfor
  rw [hrestore] at hfor
  exact ⟨result, hfor, hfold⟩

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
