import Challenge.Bls12381G1Add.Reference.Proofs.SourceMainFiniteDoubleState
import Challenge.YulProof.ClosedEvmMemory

set_option warningAsError true

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

/-- Right-to-left relational evaluation of the four source loads for `2*y`. -/
theorem eval_mainFiniteDoubleStmt3Args (yst : EvmState) :
    EvalArgs Challenge.YulProof.ClosedEvm.dialect ([] :: mainFuns)
      (mainFiniteDoubleEnv3 yst) (mainFiniteDoubleState1 yst)
      [.builtin .mload [.lit (.number 64)],
        .builtin .mload [.lit (.number 96)],
        .builtin .mload [.lit (.number 64)],
        .builtin .mload [.lit (.number 96)]]
      (.vals [(mainFiniteDoubleYWords yst).1,
        (mainFiniteDoubleYWords yst).2,
        (mainFiniteDoubleYWords yst).1,
        (mainFiniteDoubleYWords yst).2]
        (mainFiniteDoubleDenArgsState yst)) := by
  let s0 := mainFiniteDoubleState1 yst
  let s1 := touchMemory s0 96 32
  let s2 := touchMemory s1 64 32
  let s3 := touchMemory s2 96 32
  let s4 := touchMemory s3 64 32
  have hlast : EvalArgs Challenge.YulProof.ClosedEvm.dialect ([] :: mainFuns)
      (mainFiniteDoubleEnv3 yst) s0
      [.builtin .mload [.lit (.number 96)]]
      (.vals [loadWord s0.memory 96] s1) :=
    Step.argsCons Step.argsNil
      (Challenge.YulProof.ClosedEvm.eval_mload _ _ _ 96 (by norm_num))
  have hthird : EvalArgs Challenge.YulProof.ClosedEvm.dialect ([] :: mainFuns)
      (mainFiniteDoubleEnv3 yst) s0
      [.builtin .mload [.lit (.number 64)],
        .builtin .mload [.lit (.number 96)]]
      (.vals [loadWord s1.memory 64, loadWord s0.memory 96] s2) :=
    Step.argsCons hlast
      (Challenge.YulProof.ClosedEvm.eval_mload _ _ _ 64 (by norm_num))
  have hsecond : EvalArgs Challenge.YulProof.ClosedEvm.dialect ([] :: mainFuns)
      (mainFiniteDoubleEnv3 yst) s0
      [.builtin .mload [.lit (.number 96)],
        .builtin .mload [.lit (.number 64)],
        .builtin .mload [.lit (.number 96)]]
      (.vals [loadWord s2.memory 96, loadWord s1.memory 64,
        loadWord s0.memory 96] s3) :=
    Step.argsCons hthird
      (Challenge.YulProof.ClosedEvm.eval_mload _ _ _ 96 (by norm_num))
  have hall : EvalArgs Challenge.YulProof.ClosedEvm.dialect ([] :: mainFuns)
      (mainFiniteDoubleEnv3 yst) s0
      [.builtin .mload [.lit (.number 64)],
        .builtin .mload [.lit (.number 96)],
        .builtin .mload [.lit (.number 64)],
        .builtin .mload [.lit (.number 96)]]
      (.vals [loadWord s3.memory 64, loadWord s2.memory 96,
        loadWord s1.memory 64, loadWord s0.memory 96] s4) :=
    Step.argsCons hsecond
      (Challenge.YulProof.ClosedEvm.eval_mload _ _ _ 64 (by norm_num))
  let y := mainFiniteDoubleYWords yst
  have hload64 : loadWord s0.memory 64 = y.1 := by
    dsimp only [s0]
    change loadWord (mainFiniteDoubleState1 yst).memory 64 =
      mainDecodedWord yst 64
    rw [mainFiniteDoubleState1_eq, mainFiniteDoubleXSqArgsState,
      afterFourLoads_memory]
    exact mainFiniteYZeroArgsState_loadWord yst 64 (by norm_num)
  have hload96 : loadWord s0.memory 96 = y.2 := by
    dsimp only [s0]
    change loadWord (mainFiniteDoubleState1 yst).memory 96 =
      mainDecodedWord yst 96
    rw [mainFiniteDoubleState1_eq, mainFiniteDoubleXSqArgsState,
      afterFourLoads_memory]
    exact mainFiniteYZeroArgsState_loadWord yst 96 (by norm_num)
  have hs3load64 : loadWord s3.memory 64 = y.1 := by
    rw [show s3.memory = s0.memory by
      dsimp only [s3, s2, s1]
      repeat' rw [Challenge.YulProof.ClosedEvm.touchMemory_memory]]
    exact hload64
  have hs2load96 : loadWord s2.memory 96 = y.2 := by
    rw [show s2.memory = s0.memory by
      dsimp only [s2, s1]
      repeat' rw [Challenge.YulProof.ClosedEvm.touchMemory_memory]]
    exact hload96
  have hs1load64 : loadWord s1.memory 64 = y.1 := by
    rw [show s1.memory = s0.memory by
      dsimp only [s1]
      rw [Challenge.YulProof.ClosedEvm.touchMemory_memory]]
    exact hload64
  have hs4 : s4 = mainFiniteDoubleDenArgsState yst := by
    rfl
  rw [hs3load64, hs2load96, hs1load64, hload96, hs4] at hall
  exact hall

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
