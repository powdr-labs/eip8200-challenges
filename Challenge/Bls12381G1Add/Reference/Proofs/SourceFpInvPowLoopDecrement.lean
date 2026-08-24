import Challenge.Bls12381G1Add.Reference.Proofs.SourceFpInvPowLoopModel
import Challenge.YulProof.Interpreter

set_option warningAsError true

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
open YulSemantics YulSemantics.EVM
open Challenge.YulProof.Interpreter
private abbrev D := Challenge.YulProof.ClosedEvm.dialect

theorem step_loop_decrement' {V : VEnv D} (bitName : Ident) (bit : Nat)
    (base acc : MontResultValue) (yst : EvmState)
    (hinv : PowLoopInv V bitName (bit + 1) base acc) :
    ExecStmt D loopBodyFuns V yst
      (.assign [bitName] (.builtin .sub [.var bitName, .lit (.number 1)]))
      (setBit V bitName bit) yst .normal := by
  have hsub : BitVec.ofNat 256 (bit + 1) - 1 = BitVec.ofNat 256 bit := by
    rw [show (1 : U256) = BitVec.ofNat 256 1 by rfl,
      BitVec.ofNat_sub_ofNat_of_le (w := 256)] <;> norm_num
  have hargs : EvalArgs D loopBodyFuns V yst
      [.var bitName, .lit (.number 1)]
      (.vals [BitVec.ofNat 256 (bit + 1), 1] yst) :=
    Step.argsCons (Step.argsCons Step.argsNil Step.lit) (Step.var hinv.bit)
  have hb : EvalExpr D loopBodyFuns V yst
      (.builtin .sub [.var bitName, .lit (.number 1)])
      (.vals [BitVec.ofNat 256 (bit + 1) - 1] yst) :=
    evalBuiltin Challenge.YulProof.ClosedEvm.exec_lawful hargs (by rfl)
  rw [hsub] at hb
  have hs := Step.assignVal (vars := [bitName]) hb (by rfl)
  change ExecStmt D loopBodyFuns V yst _ (setBit V bitName bit) yst .normal at hs
  exact hs

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
