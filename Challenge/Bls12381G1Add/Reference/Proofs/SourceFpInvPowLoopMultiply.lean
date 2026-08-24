import Challenge.Bls12381G1Add.Reference.Proofs.SourceFpInvPowLoopCondition

set_option warningAsError true

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM
private abbrev D := Challenge.YulProof.ClosedEvm.dialect

def fpPowMultiplyBody : Block Op :=
  [.assign ["\x00129", "\x00130"] (.call "\x0015"
    [.var "\x00129", .var "\x00130", .var "\x00127", .var "\x00128"])]

theorem step_loop_multiply_assignment {V : VEnv D} (bitName : Ident) (bit : Nat)
    (base acc : MontResultValue) (yst : EvmState)
    (hinv : PowLoopInv V bitName bit base acc) :
    ∃ zLo zHi,
      ExecStmt D loopCondFuns V yst fpPowMultiplyBody[0]!
        (setAcc V { lo := zLo, hi := zHi }) yst .normal ∧
      NativeMontMulResult acc.lo acc.hi base.lo base.hi zLo zHi := by
  have hargs : EvalArgs D loopCondFuns V yst
      [.var "\x00129", .var "\x00130", .var "\x00127", .var "\x00128"]
      (.vals [acc.lo, acc.hi, base.lo, base.hi] yst) :=
    Step.argsCons (Step.argsCons (Step.argsCons (Step.argsCons Step.argsNil
      (Step.var hinv.baseHi)) (Step.var hinv.baseLo)) (Step.var hinv.accHi))
      (Step.var hinv.accLo)
  obtain ⟨zLo, zHi, hcall, hrefines⟩ := step_montMul2_nativeResult
    (callerFuns := loopCondFuns) (V := V)
    (args := [.var "\x00129", .var "\x00130", .var "\x00127", .var "\x00128"])
    (yst := yst) acc.lo acc.hi base.lo base.hi lookup_mont_loopCond hargs
  refine ⟨zLo, zHi, ?_, hrefines⟩
  have hs := Step.assignVal (vars := ["\x00129", "\x00130"]) hcall (by rfl)
  change ExecStmt D loopCondFuns V yst fpPowMultiplyBody[0]!
    (setAcc V { lo := zLo, hi := zHi }) yst .normal at hs
  exact hs

theorem step_loop_multiply_block {V : VEnv D} (bitName : Ident) (bit : Nat)
    (base acc : MontResultValue) (yst : EvmState)
    (hinv : PowLoopInv V bitName bit base acc) :
    ∃ zLo zHi,
      ExecStmt D loopBodyFuns V yst (.block fpPowMultiplyBody)
        (setAcc V { lo := zLo, hi := zHi }) yst .normal ∧
      NativeMontMulResult acc.lo acc.hi base.lo base.hi zLo zHi := by
  obtain ⟨zLo, zHi, hassign, hrefines⟩ :=
    step_loop_multiply_assignment bitName bit base acc yst hinv
  refine ⟨zLo, zHi, ?_, hrefines⟩
  have hseq : ExecStmts D loopCondFuns V yst fpPowMultiplyBody
      (setAcc V { lo := zLo, hi := zHi }) yst .normal :=
    Step.seqCons hassign Step.seqNil
  have hseq' : ExecStmts D (hoist D fpPowMultiplyBody :: loopBodyFuns) V yst
      fpPowMultiplyBody (setAcc V { lo := zLo, hi := zHi }) yst .normal := by
    simpa [loopCondFuns, fpPowMultiplyBody, hoist] using hseq
  have hblock := Step.block (funs := loopBodyFuns) hseq'
  rw [restore_of_length_eq V _ (setAcc_length V _)] at hblock
  exact hblock

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
