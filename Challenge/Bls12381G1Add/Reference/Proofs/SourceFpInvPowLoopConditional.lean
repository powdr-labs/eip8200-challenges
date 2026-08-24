import Challenge.Bls12381G1Add.Reference.Proofs.SourceFpInvPowLoopMultiply

set_option warningAsError true

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM
private abbrev D := Challenge.YulProof.ClosedEvm.dialect

def fpPowConditionStmt (bitName : Ident) (word : Nat) : Stmt Op :=
  .cond (.builtin .and
      [.builtin .shr [.var bitName, .lit (.number word)], .lit (.number 1)])
    fpPowMultiplyBody

theorem step_loop_condition_zero {V : VEnv D} (bitName : Ident) (bit : Nat)
    (base acc : MontResultValue) (word : Nat) (yst : EvmState)
    (hinv : PowLoopInv V bitName bit base acc)
    (hzero : sourceWordBit (BitVec.ofNat 256 word) bit = 0) :
    ExecStmt D loopBodyFuns V yst (fpPowConditionStmt bitName word)
      V yst .normal := by
  exact Step.ifFalse (eval_loop_condition bitName bit base acc word yst hinv) hzero

theorem step_loop_condition_nonzero {V : VEnv D} (bitName : Ident) (bit : Nat)
    (base acc : MontResultValue) (word : Nat) (yst : EvmState)
    (hinv : PowLoopInv V bitName bit base acc)
    (hnonzero : sourceWordBit (BitVec.ofNat 256 word) bit ≠ 0) :
    ∃ zLo zHi,
      ExecStmt D loopBodyFuns V yst (fpPowConditionStmt bitName word)
        (setAcc V { lo := zLo, hi := zHi }) yst .normal ∧
      NativeMontMulResult acc.lo acc.hi base.lo base.hi zLo zHi := by
  obtain ⟨zLo, zHi, hblock, hrefines⟩ :=
    step_loop_multiply_block bitName bit base acc yst hinv
  exact ⟨zLo, zHi,
    Step.ifTrue (eval_loop_condition bitName bit base acc word yst hinv)
      hnonzero hblock,
    hrefines⟩

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
