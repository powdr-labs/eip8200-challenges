import Challenge.Sha256.Reference.Proofs.Bytecode.CompressionGasBase
import Challenge.Sha256.Reference.Proofs.Bytecode.ArithmeticGas

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Challenge.Sha256.Reference.Proofs.Bytecode.CompressionGas

open Challenge.Sha256
open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler


theorem t1_cost_potential (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) (hj : j < 64)
    (hcap : rest.length < 988)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    (Compression.gasSteps_t1 s msgOff returnDest rest j hj hcap hcode hfork
      hrun hnp).cost + MachineState.memCost
        (Compression.roundAt s msgOff returnDest rest j).activeWords.toNat =
      684 + MachineState.memCost
        (Compression.afterT1 s msgOff returnDest rest j).activeWords.toNat := by
  have hcond := blockCost_potential_of_static Compression.conditionPath 26
    (Compression.run_condition s msgOff returnDest rest j hj (by omega) hrun)
    (by simpa [Compression.roundAt, State.fork] using hfork)
    (by simp [Compression.conditionPath, CopyFree]) (by rfl)
  have hsetupW := blockCost_potential_of_static Compression.setupWPath 28
    (Compression.run_setupW s msgOff returnDest rest j (by omega) hcode hrun)
    (by simpa [Compression.afterCondition, State.fork] using hfork)
    (by simp [Compression.setupWPath, CopyFree]) (by rfl)
  have hw := CompressionGas.wAt_cost_potential (Compression.loadedE s)
    (UInt256.ofNat j) 0 (UInt256.ofNat 661)
    ([UInt256.ofNat 0xffffffff, Compression.hValue s 4, UInt256.ofNat j,
      msgOff, returnDest] ++ rest) (by simp; omega)
    (by simpa [Compression.loadedE] using hcode)
    (by simpa [Compression.loadedE, State.fork] using hfork)
    (by simpa [Compression.loadedE] using hrun)
    (by simpa [Compression.loadedE] using hnp) (by decide)
  have hsetupK := blockCost_potential_of_static Compression.setupKPath 20
    (Compression.run_setupK s msgOff returnDest rest j (by omega) hcode hrun)
    (by simpa [Compression.gotW, Compression.loadedE,
      Accessors.loadReturned, State.fork] using hfork)
    (by simp [Compression.setupKPath, CopyFree]) (by rfl)
  have hk := CompressionGas.kAt_cost_potential
    (Compression.gotW s msgOff returnDest rest j) (UInt256.ofNat j) 0
    (UInt256.ofNat 671)
    ([Compression.wValue s j, UInt256.ofNat 0xffffffff,
      Compression.hValue s 4, UInt256.ofNat j, msgOff, returnDest] ++ rest)
    (by simp; omega)
    (by simpa [Compression.gotW, Compression.loadedE,
      Accessors.loadReturned] using hcode)
    (by simpa [Compression.gotW, Compression.loadedE,
      Accessors.loadReturned, State.fork] using hfork)
    (by simpa [Compression.gotW, Compression.loadedE,
      Accessors.loadReturned] using hrun)
    (by simpa [Compression.gotW, Compression.loadedE,
      Accessors.loadReturned] using hnp) (by decide)
  have hsetupH6 := blockCost_potential_of_static Compression.setupH6Path 25
    (Compression.run_setupH6 s msgOff returnDest rest j (by omega) hcode hrun)
    (by simpa [Compression.gotK, Compression.gotW, Compression.loadedE,
      Accessors.kAtReturned, Accessors.loadReturned, State.fork] using hfork)
    (by simp [Compression.setupH6Path, CopyFree]) (by rfl)
  have hh6 := CompressionGas.hAt_cost_potential
    (Compression.gotK s msgOff returnDest rest j) (UInt256.ofNat 6) 0
    (UInt256.ofNat 686)
    ([0, UInt256.ofNat 703, Compression.kValue s j, Compression.wValue s j,
      UInt256.ofNat 0xffffffff, Compression.hValue s 4, UInt256.ofNat j,
      msgOff, returnDest] ++ rest) (by simp; omega)
    (by simpa [Compression.gotK, Compression.gotW, Compression.loadedE,
      Accessors.kAtReturned, Accessors.loadReturned] using hcode)
    (by simpa [Compression.gotK, Compression.gotW, Compression.loadedE,
      Accessors.kAtReturned, Accessors.loadReturned, State.fork] using hfork)
    (by simpa [Compression.gotK, Compression.gotW, Compression.loadedE,
      Accessors.kAtReturned, Accessors.loadReturned] using hrun)
    (by simpa [Compression.gotK, Compression.gotW, Compression.loadedE,
      Accessors.kAtReturned, Accessors.loadReturned] using hnp) (by decide)
  have hsetupH5 := blockCost_potential_of_static Compression.setupH5Path 20
    (Compression.run_setupH5 s msgOff returnDest rest j (by omega) hcode hrun)
    (by simpa [Compression.gotH6, Compression.gotK, Compression.gotW,
      Compression.loadedE, Accessors.loadReturned, Accessors.kAtReturned,
      State.fork] using hfork)
    (by simp [Compression.setupH5Path, CopyFree]) (by rfl)
  have hh5 := CompressionGas.hAt_cost_potential
    (Compression.gotH6 s msgOff returnDest rest j) (UInt256.ofNat 5) 0
    (UInt256.ofNat 697)
    ([Compression.hValue s 6, 0, UInt256.ofNat 703, Compression.kValue s j,
      Compression.wValue s j, UInt256.ofNat 0xffffffff,
      Compression.hValue s 4, UInt256.ofNat j, msgOff, returnDest] ++ rest)
    (by simp; omega)
    (by simpa [Compression.gotH6, Compression.gotK, Compression.gotW,
      Compression.loadedE, Accessors.loadReturned,
      Accessors.kAtReturned] using hcode)
    (by simpa [Compression.gotH6, Compression.gotK, Compression.gotW,
      Compression.loadedE, Accessors.loadReturned, Accessors.kAtReturned,
      State.fork] using hfork)
    (by simpa [Compression.gotH6, Compression.gotK, Compression.gotW,
      Compression.loadedE, Accessors.loadReturned,
      Accessors.kAtReturned] using hrun)
    (by simpa [Compression.gotH6, Compression.gotK, Compression.gotW,
      Compression.loadedE, Accessors.loadReturned,
      Accessors.kAtReturned] using hnp) (by decide)
  have hsetupCh := blockCost_potential_of_static Compression.setupChPath 15
    (Compression.run_setupCh s msgOff returnDest rest j (by omega) hcode hrun)
    (by simpa [Compression.gotH5, Compression.gotH6, Compression.gotK,
      Compression.gotW, Compression.loadedE, Accessors.loadReturned,
      Accessors.kAtReturned, State.fork] using hfork)
    (by simp [Compression.setupChPath, CopyFree]) (by rfl)
  have hch := ArithmeticGas.gasSteps_ch_cost_potential
    (Compression.gotH5 s msgOff returnDest rest j) (Compression.hValue s 4)
    (Compression.hValue s 5) (Compression.hValue s 6) 0 (UInt256.ofNat 703)
    ([Compression.kValue s j, Compression.wValue s j,
      UInt256.ofNat 0xffffffff, Compression.hValue s 4, UInt256.ofNat j,
      msgOff, returnDest] ++ rest) (by simp; omega)
    (by simpa [Compression.gotH5, Compression.gotH6, Compression.gotK,
      Compression.gotW, Compression.loadedE, Accessors.loadReturned,
      Accessors.kAtReturned] using hcode)
    (by simpa [Compression.gotH5, Compression.gotH6, Compression.gotK,
      Compression.gotW, Compression.loadedE, Accessors.loadReturned,
      Accessors.kAtReturned, State.fork] using hfork)
    (by simpa [Compression.gotH5, Compression.gotH6, Compression.gotK,
      Compression.gotW, Compression.loadedE, Accessors.loadReturned,
      Accessors.kAtReturned] using hrun)
    (by simpa [Compression.gotH5, Compression.gotH6, Compression.gotK,
      Compression.gotW, Compression.loadedE, Accessors.loadReturned,
      Accessors.kAtReturned] using hnp) (by decide)
  have hsetupB1 := blockCost_potential_of_static
    Compression.setupBigSigma1Path 23
    (Compression.run_setupBigSigma1 s msgOff returnDest rest j (by omega)
      hcode hrun)
    (by simpa [Compression.gotCh, Compression.gotH5, Compression.gotH6,
      Compression.gotK, Compression.gotW, Compression.loadedE,
      Functions.unaryReturned, Accessors.loadReturned,
      Accessors.kAtReturned, State.fork] using hfork)
    (by simp [Compression.setupBigSigma1Path, CopyFree]) (by rfl)
  have hb1 := ArithmeticGas.gasSteps_bigSigma1_cost_potential
    (Compression.gotCh s msgOff returnDest rest j) (Compression.hValue s 4) 0
    (UInt256.ofNat 714)
    ([Compression.chPlusK s j, Compression.wValue s j,
      UInt256.ofNat 0xffffffff, Compression.hValue s 4, UInt256.ofNat j,
      msgOff, returnDest] ++ rest) (by simp; omega)
    (by simpa [Compression.gotCh, Compression.gotH5, Compression.gotH6,
      Compression.gotK, Compression.gotW, Compression.loadedE,
      Functions.unaryReturned, Accessors.loadReturned,
      Accessors.kAtReturned] using hcode)
    (by simpa [Compression.gotCh, Compression.gotH5, Compression.gotH6,
      Compression.gotK, Compression.gotW, Compression.loadedE,
      Functions.unaryReturned, Accessors.loadReturned,
      Accessors.kAtReturned, State.fork] using hfork)
    (by simpa [Compression.gotCh, Compression.gotH5, Compression.gotH6,
      Compression.gotK, Compression.gotW, Compression.loadedE,
      Functions.unaryReturned, Accessors.loadReturned,
      Accessors.kAtReturned] using hrun)
    (by simpa [Compression.gotCh, Compression.gotH5, Compression.gotH6,
      Compression.gotK, Compression.gotW, Compression.loadedE,
      Functions.unaryReturned, Accessors.loadReturned,
      Accessors.kAtReturned] using hnp) (by decide)
  have hsetupH7 := blockCost_potential_of_static Compression.setupH7Path 20
    (Compression.run_setupH7 s msgOff returnDest rest j (by omega) hcode hrun)
    (by simpa [Compression.gotBigSigma1, Compression.gotCh,
      Compression.gotH5, Compression.gotH6, Compression.gotK,
      Compression.gotW, Compression.loadedE, Functions.unaryReturned,
      Accessors.loadReturned, Accessors.kAtReturned, State.fork] using hfork)
    (by simp [Compression.setupH7Path, CopyFree]) (by rfl)
  have hh7 := CompressionGas.hAt_cost_potential
    (Compression.gotBigSigma1 s msgOff returnDest rest j) (UInt256.ofNat 7) 0
    (UInt256.ofNat 725)
    ([Word.evmBigSigma1 (Compression.hValue s 4), Compression.chPlusK s j,
      Compression.wValue s j, UInt256.ofNat 0xffffffff,
      Compression.hValue s 4, UInt256.ofNat j, msgOff, returnDest] ++ rest)
    (by simp; omega)
    (by simpa [Compression.gotBigSigma1, Compression.gotCh,
      Compression.gotH5, Compression.gotH6, Compression.gotK,
      Compression.gotW, Compression.loadedE, Functions.unaryReturned,
      Accessors.loadReturned, Accessors.kAtReturned] using hcode)
    (by simpa [Compression.gotBigSigma1, Compression.gotCh,
      Compression.gotH5, Compression.gotH6, Compression.gotK,
      Compression.gotW, Compression.loadedE, Functions.unaryReturned,
      Accessors.loadReturned, Accessors.kAtReturned, State.fork] using hfork)
    (by simpa [Compression.gotBigSigma1, Compression.gotCh,
      Compression.gotH5, Compression.gotH6, Compression.gotK,
      Compression.gotW, Compression.loadedE, Functions.unaryReturned,
      Accessors.loadReturned, Accessors.kAtReturned] using hrun)
    (by simpa [Compression.gotBigSigma1, Compression.gotCh,
      Compression.gotH5, Compression.gotH6, Compression.gotK,
      Compression.gotW, Compression.loadedE, Functions.unaryReturned,
      Accessors.loadReturned, Accessors.kAtReturned] using hnp) (by decide)
  have hfinish := blockCost_potential_of_static Compression.finishT1Path 13
    (Compression.run_finishT1 s msgOff returnDest rest j (by omega) hrun)
    (by simpa [Compression.gotH7, Compression.gotBigSigma1,
      Compression.gotCh, Compression.gotH5, Compression.gotH6,
      Compression.gotK, Compression.gotW, Compression.loadedE,
      Functions.unaryReturned, Accessors.loadReturned,
      Accessors.kAtReturned, State.fork] using hfork)
    (by simp [Compression.finishT1Path, CopyFree]) (by rfl)
  have hawW :
      (Compression.callW s msgOff returnDest rest j).activeWords =
        (Compression.loadedE s).activeWords := by rfl
  have hawK :
      (Compression.callK s msgOff returnDest rest j).activeWords =
        (Compression.gotW s msgOff returnDest rest j).activeWords := by rfl
  have hawH6 :
      (Compression.callH6 s msgOff returnDest rest j).activeWords =
        (Compression.gotK s msgOff returnDest rest j).activeWords := by rfl
  have hawH5 :
      (Compression.callH5 s msgOff returnDest rest j).activeWords =
        (Compression.gotH6 s msgOff returnDest rest j).activeWords := by rfl
  have hawCh :
      (Compression.callCh s msgOff returnDest rest j).activeWords =
        (Compression.gotH5 s msgOff returnDest rest j).activeWords := by rfl
  have hawB1 :
      (Compression.callBigSigma1 s msgOff returnDest rest j).activeWords =
        (Compression.gotCh s msgOff returnDest rest j).activeWords := by rfl
  have hawH7 :
      (Compression.callH7 s msgOff returnDest rest j).activeWords =
        (Compression.gotBigSigma1 s msgOff returnDest rest j).activeWords := by rfl
  simp only [Compression.gasSteps_t1, Compression.gasSteps_condition,
    Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost]
  rw [hawW] at hsetupW
  rw [hawK] at hsetupK
  rw [hawH6] at hsetupH6
  rw [hawH5] at hsetupH5
  rw [hawCh] at hsetupCh
  rw [hawB1] at hsetupB1
  rw [hawH7] at hsetupH7
  change _ = 37 + MachineState.memCost
    (Compression.gotW s msgOff returnDest rest j).activeWords.toNat at hw
  change _ = 43 + MachineState.memCost
    (Compression.gotK s msgOff returnDest rest j).activeWords.toNat at hk
  change _ = 37 + MachineState.memCost
    (Compression.gotH6 s msgOff returnDest rest j).activeWords.toNat at hh6
  change _ = 37 + MachineState.memCost
    (Compression.gotH5 s msgOff returnDest rest j).activeWords.toNat at hh5
  change _ = 47 + MachineState.memCost
    (Compression.gotCh s msgOff returnDest rest j).activeWords.toNat at hch
  change _ = 256 + MachineState.memCost
    (Compression.gotBigSigma1 s msgOff returnDest rest j).activeWords.toNat at hb1
  change _ = 37 + MachineState.memCost
    (Compression.gotH7 s msgOff returnDest rest j).activeWords.toNat at hh7
  omega


end Challenge.Sha256.Reference.Proofs.Bytecode.CompressionGas
