import Challenge.Bls12381G1Add.Reference.Proofs.SourceFpInvPowLoopConditional

set_option warningAsError true

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM
private abbrev D := Challenge.YulProof.ClosedEvm.dialect

/-- One abstract exponentiation bit step.  Its only arithmetic assumptions are
the opaque correctness facts returned by the local source `montMul2` calls. -/
inductive NativeBitStep (base acc : MontResultValue) (word bit : Nat) :
    MontResultValue → Prop
  | zero (square : MontResultValue)
      (hsquare : NativeMontMulResult acc.lo acc.hi acc.lo acc.hi
        square.lo square.hi)
      (hzero : sourceWordBit (BitVec.ofNat 256 word) bit = 0) :
      NativeBitStep base acc word bit square
  | nonzero (square result : MontResultValue)
      (hsquare : NativeMontMulResult acc.lo acc.hi acc.lo acc.hi
        square.lo square.hi)
      (hnonzero : sourceWordBit (BitVec.ofNat 256 word) bit ≠ 0)
      (hmultiply : NativeMontMulResult square.lo square.hi base.lo base.hi
        result.lo result.hi) :
      NativeBitStep base acc word bit result

theorem fpPowLoopBody_eq (bitName : Ident) (word : Nat) :
    fpPowLoopBody bitName word =
      [.assign [bitName] (.builtin .sub [.var bitName, .lit (.number 1)]),
       .assign ["\x00129", "\x00130"] (.call "\x0015"
         [.var "\x00129", .var "\x00130", .var "\x00129", .var "\x00130"]),
       fpPowConditionStmt bitName word] := by
  rfl

theorem step_fpPowLoopBody {V : VEnv D} (bitName : Ident) (bit : Nat)
    (aHi aLo : U256) (base acc : MontResultValue) (word : Nat) (yst : EvmState)
    (hinv : PowLoopInv V bitName (bit + 1) base acc)
    (hhead : PowLoopHead V bitName (bit + 1))
    (hframe : PowLoopFrame V aHi aLo bitName (bit + 1) base acc)
    (hfreshLo : bitName ≠ "\x00129") (hfreshHi : bitName ≠ "\x00130")
    (hfreshBaseLo : bitName ≠ "\x00127")
    (hfreshBaseHi : bitName ≠ "\x00128") :
    ∃ V' next,
      ExecStmt D loopFuns V yst (.block (fpPowLoopBody bitName word))
        V' yst .normal ∧
      V'.length = V.length ∧
      PowLoopInv V' bitName bit base next ∧
      PowLoopHead V' bitName bit ∧
      PowLoopFrame V' aHi aLo bitName bit base next ∧
      NativeBitStep base acc word bit next := by
  have hdec := step_loop_decrement' bitName bit base acc yst hinv
  have hdecInv := hinv.afterSetBit bit hfreshLo hfreshHi
    hfreshBaseLo hfreshBaseHi
  have hdecHead := hhead.afterSetBit bit
  obtain ⟨squareLo, squareHi, hsquare, hsquareNative⟩ :=
    step_loop_square bitName bit base acc yst hdecInv
  let square : MontResultValue := { lo := squareLo, hi := squareHi }
  have hsquareInv : PowLoopInv (setAcc (setBit V bitName bit) square)
      bitName bit base square :=
    hdecInv.afterSetAcc square hfreshLo hfreshHi
  have hsquareHead : PowLoopHead (setAcc (setBit V bitName bit) square)
      bitName bit := hdecHead.afterSetAcc square hfreshLo hfreshHi
  by_cases hzero : sourceWordBit (BitVec.ofNat 256 word) bit = 0
  · have hcond := step_loop_condition_zero bitName bit base square word yst
      hsquareInv hzero
    have hseq0 : ExecStmts D loopBodyFuns V yst
        [.assign [bitName] (.builtin .sub [.var bitName, .lit (.number 1)]),
         .assign ["\x00129", "\x00130"] (.call "\x0015"
           [.var "\x00129", .var "\x00130", .var "\x00129", .var "\x00130"]),
         fpPowConditionStmt bitName word]
        (setAcc (setBit V bitName bit) square) yst .normal :=
      Step.seqCons hdec (Step.seqCons hsquare (Step.seqCons hcond Step.seqNil))
    have hseq : ExecStmts D
        (hoist D (fpPowLoopBody bitName word) :: loopFuns) V yst
        (fpPowLoopBody bitName word)
        (setAcc (setBit V bitName bit) square) yst .normal := by
      rw [fpPowLoopBody_eq]
      simpa [loopBodyFuns, fpPowLoopBody, fpPowConditionStmt,
        fpPowMultiplyBody, hoist] using hseq0
    have hblock := Step.block (funs := loopFuns) hseq
    have hlen : (setAcc (setBit V bitName bit) square).length = V.length := by
      rw [setAcc_length, setBit_length]
    rw [restore_of_length_eq V _ hlen] at hblock
    have hsquareFrame : PowLoopFrame
        (setAcc (setBit V bitName bit) square) aHi aLo bitName bit base square := by
      have hframe' := hframe
      unfold PowLoopFrame at hframe' ⊢
      rw [hframe']
      simp [setBit, setAcc, fpPowAccEnv, VEnv.set, hfreshLo, hfreshHi]
    exact ⟨_, square, hblock, hlen, hsquareInv, hsquareHead, hsquareFrame,
      NativeBitStep.zero square hsquareNative hzero⟩
  · obtain ⟨resultLo, resultHi, hcond, hmultiply⟩ :=
      step_loop_condition_nonzero bitName bit base square word yst
        hsquareInv hzero
    let result : MontResultValue := { lo := resultLo, hi := resultHi }
    have hresultInv : PowLoopInv
        (setAcc (setAcc (setBit V bitName bit) square) result)
        bitName bit base result :=
      hsquareInv.afterSetAcc result hfreshLo hfreshHi
    have hresultHead : PowLoopHead
        (setAcc (setAcc (setBit V bitName bit) square) result)
        bitName bit := hsquareHead.afterSetAcc result hfreshLo hfreshHi
    have hseq0 : ExecStmts D loopBodyFuns V yst
        [.assign [bitName] (.builtin .sub [.var bitName, .lit (.number 1)]),
         .assign ["\x00129", "\x00130"] (.call "\x0015"
           [.var "\x00129", .var "\x00130", .var "\x00129", .var "\x00130"]),
         fpPowConditionStmt bitName word]
        (setAcc (setAcc (setBit V bitName bit) square) result) yst .normal :=
      Step.seqCons hdec (Step.seqCons hsquare (Step.seqCons hcond Step.seqNil))
    have hseq : ExecStmts D
        (hoist D (fpPowLoopBody bitName word) :: loopFuns) V yst
        (fpPowLoopBody bitName word)
        (setAcc (setAcc (setBit V bitName bit) square) result)
        yst .normal := by
      rw [fpPowLoopBody_eq]
      simpa [loopBodyFuns, fpPowLoopBody, fpPowConditionStmt,
        fpPowMultiplyBody, hoist] using hseq0
    have hblock := Step.block (funs := loopFuns) hseq
    have hlen :
        (setAcc (setAcc (setBit V bitName bit) square) result).length =
          V.length := by
      rw [setAcc_length, setAcc_length, setBit_length]
    rw [restore_of_length_eq V _ hlen] at hblock
    have hresultFrame : PowLoopFrame
        (setAcc (setAcc (setBit V bitName bit) square) result)
        aHi aLo bitName bit base result := by
      have hframe' := hframe
      unfold PowLoopFrame at hframe' ⊢
      rw [hframe']
      simp [setBit, setAcc, fpPowAccEnv, VEnv.set, hfreshLo, hfreshHi]
    exact ⟨_, result, hblock, hlen, hresultInv, hresultHead, hresultFrame,
      NativeBitStep.nonzero square result hsquareNative hzero hmultiply⟩

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
