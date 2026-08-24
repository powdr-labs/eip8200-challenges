import Challenge.Bls12381G1Add.Reference.Proofs.SourceMainFiniteDoubleState
import Challenge.YulProof.ClosedEvmMemory

set_option warningAsError true

namespace Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics

open YulSemantics YulSemantics.EVM

/-- Right-to-left relational evaluation of the four source loads for `x²`. -/
theorem eval_mainFiniteDoubleStmt0Args (yst : EvmState) :
    EvalArgs Challenge.YulProof.ClosedEvm.dialect ([] :: mainFuns)
      (mainFiniteEnv yst) (mainFiniteYZeroArgsState yst)
      [.builtin .mload [.lit (.number 0)],
        .builtin .mload [.lit (.number 32)],
        .builtin .mload [.lit (.number 0)],
        .builtin .mload [.lit (.number 32)]]
      (.vals [(mainFiniteDoubleXWords yst).1,
        (mainFiniteDoubleXWords yst).2,
        (mainFiniteDoubleXWords yst).1,
        (mainFiniteDoubleXWords yst).2]
        (mainFiniteDoubleXSqArgsState yst)) := by
  let s0 := mainFiniteYZeroArgsState yst
  let s1 := touchMemory s0 32 32
  let s2 := touchMemory s1 0 32
  let s3 := touchMemory s2 32 32
  let s4 := touchMemory s3 0 32
  have hlast : EvalArgs Challenge.YulProof.ClosedEvm.dialect ([] :: mainFuns)
      (mainFiniteEnv yst) s0
      [.builtin .mload [.lit (.number 32)]]
      (.vals [loadWord s0.memory 32] s1) :=
    Step.argsCons Step.argsNil
      (Challenge.YulProof.ClosedEvm.eval_mload _ _ _ 32 (by norm_num))
  have hthird : EvalArgs Challenge.YulProof.ClosedEvm.dialect ([] :: mainFuns)
      (mainFiniteEnv yst) s0
      [.builtin .mload [.lit (.number 0)],
        .builtin .mload [.lit (.number 32)]]
      (.vals [loadWord s1.memory 0, loadWord s0.memory 32] s2) :=
    Step.argsCons hlast
      (Challenge.YulProof.ClosedEvm.eval_mload _ _ _ 0 (by norm_num))
  have hsecond : EvalArgs Challenge.YulProof.ClosedEvm.dialect ([] :: mainFuns)
      (mainFiniteEnv yst) s0
      [.builtin .mload [.lit (.number 32)],
        .builtin .mload [.lit (.number 0)],
        .builtin .mload [.lit (.number 32)]]
      (.vals [loadWord s2.memory 32, loadWord s1.memory 0,
        loadWord s0.memory 32] s3) :=
    Step.argsCons hthird
      (Challenge.YulProof.ClosedEvm.eval_mload _ _ _ 32 (by norm_num))
  have hall : EvalArgs Challenge.YulProof.ClosedEvm.dialect ([] :: mainFuns)
      (mainFiniteEnv yst) s0
      [.builtin .mload [.lit (.number 0)],
        .builtin .mload [.lit (.number 32)],
        .builtin .mload [.lit (.number 0)],
        .builtin .mload [.lit (.number 32)]]
      (.vals [loadWord s3.memory 0, loadWord s2.memory 32,
        loadWord s1.memory 0, loadWord s0.memory 32] s4) :=
    Step.argsCons hsecond
      (Challenge.YulProof.ClosedEvm.eval_mload _ _ _ 0 (by norm_num))
  have hload0 := mainFiniteYZeroArgsState_loadWord yst 0 (by norm_num)
  have hload32 := mainFiniteYZeroArgsState_loadWord yst 32 (by norm_num)
  have hs3load0 : loadWord s3.memory 0 = mainDecodedWord yst 0 := by
    rw [show s3.memory = s0.memory by
      dsimp only [s3, s2, s1]
      repeat' rw [Challenge.YulProof.ClosedEvm.touchMemory_memory]]
    exact hload0
  have hs2load32 : loadWord s2.memory 32 = mainDecodedWord yst 32 := by
    rw [show s2.memory = s0.memory by
      dsimp only [s2, s1]
      repeat' rw [Challenge.YulProof.ClosedEvm.touchMemory_memory]]
    exact hload32
  have hs1load0 : loadWord s1.memory 0 = mainDecodedWord yst 0 := by
    rw [show s1.memory = s0.memory by
      dsimp only [s1]
      rw [Challenge.YulProof.ClosedEvm.touchMemory_memory]]
    exact hload0
  have hs0load32 : loadWord s0.memory 32 = mainDecodedWord yst 32 := by
    exact hload32
  have hs4 : s4 = mainFiniteDoubleXSqArgsState yst := by
    rfl
  rw [hs3load0, hs2load32, hs1load0, hs0load32, hs4] at hall
  exact hall

end Challenge.Bls12381G1Add.Reference.Proofs.SourceSemantics
