import Challenge.Bls12381G1Add.Reference.Proofs.SourceFpInvPowLoopSquare

set_option warningAsError true

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM
private abbrev D := Challenge.YulProof.ClosedEvm.dialect

theorem eval_loop_condition {V : VEnv D} (bitName : Ident) (bit : Nat)
    (base acc : MontResultValue) (word : Nat) (yst : EvmState)
    (hinv : PowLoopInv V bitName bit base acc) :
    EvalExpr D loopBodyFuns V yst
      (.builtin .and
        [.builtin .shr [.var bitName, .lit (.number word)],
          .lit (.number 1)])
      (.vals [sourceWordBit (BitVec.ofNat 256 word) bit] yst) := by
  have hbit : EvalExpr D loopBodyFuns V yst (.var bitName)
      (.vals [BitVec.ofNat 256 bit] yst) := Step.var hinv.bit
  have hword : EvalExpr D loopBodyFuns V yst (.lit (.number word))
      (.vals [BitVec.ofNat 256 word] yst) := Step.lit
  have hshr : EvalExpr D loopBodyFuns V yst
      (.builtin .shr [.var bitName, .lit (.number word)])
      (.vals [BitVec.ofNat 256 word >>> (BitVec.ofNat 256 bit).toNat] yst) := by
    exact Step.builtinOk
      (Step.argsCons (Step.argsCons Step.argsNil hword) hbit) rfl
  have hone : EvalExpr D loopBodyFuns V yst (.lit (.number 1))
      (.vals [1] yst) := Step.lit
  exact Step.builtinOk
    (Step.argsCons (Step.argsCons Step.argsNil hone) hshr) rfl

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
