import Challenge.Bls12381G1Add.Reference.Proofs.SourceFpInvPowLoopDecrement
import Challenge.Bls12381G1Add.Reference.Proofs.SourceFpInvMulWitness

set_option warningAsError true

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM
private abbrev D := Challenge.YulProof.ClosedEvm.dialect

theorem step_loop_square {V : VEnv D} (bitName : Ident) (bit : Nat)
    (base acc : MontResultValue) (yst : EvmState)
    (hinv : PowLoopInv V bitName bit base acc) :
    ∃ zLo zHi,
      ExecStmt D loopBodyFuns V yst
        (.assign ["\x00129", "\x00130"] (.call "\x0015"
          [.var "\x00129", .var "\x00130", .var "\x00129", .var "\x00130"]))
        (setAcc V { lo := zLo, hi := zHi }) yst .normal ∧
      NativeMontMulResult acc.lo acc.hi acc.lo acc.hi zLo zHi := by
  have hargs : EvalArgs D loopBodyFuns V yst
      [.var "\x00129", .var "\x00130", .var "\x00129", .var "\x00130"]
      (.vals [acc.lo, acc.hi, acc.lo, acc.hi] yst) :=
    Step.argsCons (Step.argsCons (Step.argsCons (Step.argsCons Step.argsNil
      (Step.var hinv.accHi)) (Step.var hinv.accLo)) (Step.var hinv.accHi))
      (Step.var hinv.accLo)
  obtain ⟨zLo, zHi, hcall, hrefines⟩ := step_montMul2_nativeResult
    (callerFuns := loopBodyFuns) (V := V)
    (args := [.var "\x00129", .var "\x00130", .var "\x00129", .var "\x00130"])
    (yst := yst) acc.lo acc.hi acc.lo acc.hi lookup_mont_loopBody hargs
  refine ⟨zLo, zHi, ?_, hrefines⟩
  have hs := Step.assignVal (vars := ["\x00129", "\x00130"]) hcall (by rfl)
  change ExecStmt D loopBodyFuns V yst _ (setAcc V { lo := zLo, hi := zHi })
    yst .normal at hs
  exact hs

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
