import Challenge.Bls12381G1Add.Reference.Proofs.SourceFpInvPowLoopBody

set_option warningAsError true

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM
private abbrev D := Challenge.YulProof.ClosedEvm.dialect

def fpPowLoopGuard (bitName : Ident) : Expr Op :=
  .builtin .gt [.var bitName, .lit (.number 0)]

def fpPowGuardValue (bit : Nat) : U256 :=
  b2w ((0 : U256).ult (BitVec.ofNat 256 bit))

theorem eval_fpPowLoopGuard {V : VEnv D} (bitName : Ident) (bit : Nat)
    (base acc : MontResultValue) (yst : EvmState)
    (hinv : PowLoopInv V bitName bit base acc) :
    EvalExpr D loopFuns V yst (fpPowLoopGuard bitName)
      (.vals [fpPowGuardValue bit] yst) := by
  exact Step.builtinOk
    (Step.argsCons (Step.argsCons Step.argsNil Step.lit) (Step.var hinv.bit)) rfl

theorem fpPowGuardValue_zero : fpPowGuardValue 0 = (0 : U256) := by
  rfl

theorem fpPowGuardValue_succ_ne_zero (bit : Nat) (hbound : bit + 1 < 2 ^ 256) :
    fpPowGuardValue (bit + 1) ≠ (0 : U256) := by
  simp only [fpPowGuardValue, BitVec.ult, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hbound, b2w]
  simp

/-- Relational fold of the fixed-window square-and-multiply schedule.  This
records only the abstract contract of each local multiplication call. -/
inductive NativeFoldDown (base : MontResultValue) (word : Nat) :
    Nat → MontResultValue → MontResultValue → Prop
  | zero (acc : MontResultValue) : NativeFoldDown base word 0 acc acc
  | succ {bit : Nat} {acc next result : MontResultValue}
      (hstep : NativeBitStep base acc word bit next)
      (hrest : NativeFoldDown base word bit next result) :
      NativeFoldDown base word (bit + 1) acc result

theorem step_empty_fpPowPost (V : VEnv D) (yst : EvmState) :
    ExecStmt D loopFuns V yst (.block []) V yst .normal := by
  have hseq : ExecStmts D (hoist D [] :: loopFuns) V yst [] V yst .normal :=
    Step.seqNil
  simpa [restore] using (Step.block (funs := loopFuns) hseq)

/-- A `count`-iteration source loop, proved by a compact Nat induction rather
than by interpreter-fuel evaluation or concrete term unrolling. -/
theorem step_fpPowLoop (bitName : Ident) (aHi aLo : U256)
    (base : MontResultValue) (word count : Nat)
    (V : VEnv D) (acc : MontResultValue) (yst : EvmState)
    (hinv : PowLoopInv V bitName count base acc)
    (hhead : PowLoopHead V bitName count)
    (hframe : PowLoopFrame V aHi aLo bitName count base acc)
    (hbound : count < 2 ^ 256)
    (hfreshLo : bitName ≠ "\x00129") (hfreshHi : bitName ≠ "\x00130")
    (hfreshBaseLo : bitName ≠ "\x00127")
    (hfreshBaseHi : bitName ≠ "\x00128") :
    ∃ V' result,
      ExecLoop D loopFuns V yst (fpPowLoopGuard bitName) []
        (fpPowLoopBody bitName word) V' yst .normal ∧
      V'.length = V.length ∧
      PowLoopInv V' bitName 0 base result ∧
      PowLoopHead V' bitName 0 ∧
      PowLoopFrame V' aHi aLo bitName 0 base result ∧
      NativeFoldDown base word count acc result := by
  induction count generalizing V acc with
  | zero =>
      refine ⟨V, acc, Step.loopDone (eval_fpPowLoopGuard bitName 0 base acc yst hinv)
        fpPowGuardValue_zero, rfl, hinv, hhead, hframe,
        NativeFoldDown.zero acc⟩
  | succ bit ih =>
      obtain ⟨Vnext, next, hbody, hnextLength, hnextInv, hnextHead,
          hnextFrame, hstep⟩ :=
        step_fpPowLoopBody bitName bit aHi aLo base acc word yst hinv hhead hframe
          hfreshLo hfreshHi hfreshBaseLo hfreshBaseHi
      obtain ⟨Vfinal, result, hloop, hfinalLength, hfinalInv, hfinalHead,
          hfinalFrame, hrest⟩ :=
        ih Vnext next hnextInv hnextHead hnextFrame (by omega)
      refine ⟨Vfinal, result,
        Step.loopStep
          (eval_fpPowLoopGuard bitName (bit + 1) base acc yst hinv)
          (fpPowGuardValue_succ_ne_zero bit hbound)
          hbody (Or.inl rfl) (step_empty_fpPowPost Vnext yst) hloop,
        hfinalLength.trans hnextLength, hfinalInv, hfinalHead, hfinalFrame,
        NativeFoldDown.succ hstep hrest⟩

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
