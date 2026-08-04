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


theorem t2_cost_potential (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) (hcap : rest.length < 988)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    (Compression.gasSteps_t2 s msgOff returnDest rest j hcap hcode hfork
      hrun hnp).cost + MachineState.memCost
        (Compression.afterT1 s msgOff returnDest rest j).activeWords.toNat =
      481 + MachineState.memCost
        (Compression.afterT2 s msgOff returnDest rest j).activeWords.toNat := by
  have hsetupH2 := blockCost_potential_of_static Compression.setupT2H2Path 33
    (Compression.run_setupT2H2 s msgOff returnDest rest j (by omega)
      hcode hrun)
    (by simpa [Compression.afterT1, Compression.gotH7,
      Compression.gotBigSigma1, Compression.gotCh, Compression.gotH5,
      Compression.gotH6, Compression.gotK, Compression.gotW,
      Compression.loadedE, Functions.unaryReturned, Accessors.loadReturned,
      Accessors.kAtReturned, State.fork] using hfork)
    (by simp [Compression.setupT2H2Path, CopyFree]) (by rfl)
  have hh2 := CompressionGas.hAt_cost_potential
    (Compression.loadedA s msgOff returnDest rest j) (UInt256.ofNat 2) 0
    (UInt256.ofNat 753)
    ([0, UInt256.ofNat 770, UInt256.ofNat 0xffffffff,
      Compression.hValue s 0, Compression.t1 s j, Compression.hValue s 4,
      UInt256.ofNat j, msgOff, returnDest] ++ rest) (by simp; omega)
    (by simpa [Compression.loadedA, Compression.afterT1,
      Compression.gotH7, Compression.gotBigSigma1, Compression.gotCh,
      Compression.gotH5, Compression.gotH6, Compression.gotK,
      Compression.gotW, Compression.loadedE, Functions.unaryReturned,
      Accessors.loadReturned, Accessors.kAtReturned] using hcode)
    (by simpa [Compression.loadedA, Compression.afterT1,
      Compression.gotH7, Compression.gotBigSigma1, Compression.gotCh,
      Compression.gotH5, Compression.gotH6, Compression.gotK,
      Compression.gotW, Compression.loadedE, Functions.unaryReturned,
      Accessors.loadReturned, Accessors.kAtReturned, State.fork] using hfork)
    (by simpa [Compression.loadedA, Compression.afterT1,
      Compression.gotH7, Compression.gotBigSigma1, Compression.gotCh,
      Compression.gotH5, Compression.gotH6, Compression.gotK,
      Compression.gotW, Compression.loadedE, Functions.unaryReturned,
      Accessors.loadReturned, Accessors.kAtReturned] using hrun)
    (by simpa [Compression.loadedA, Compression.afterT1,
      Compression.gotH7, Compression.gotBigSigma1, Compression.gotCh,
      Compression.gotH5, Compression.gotH6, Compression.gotK,
      Compression.gotW, Compression.loadedE, Functions.unaryReturned,
      Accessors.loadReturned, Accessors.kAtReturned] using hnp) (by decide)
  have hsetupH1 := blockCost_potential_of_static Compression.setupT2H1Path 20
    (Compression.run_setupT2H1 s msgOff returnDest rest j (by omega)
      hcode hrun)
    (by simpa [Compression.gotT2H2, Compression.loadedA,
      Compression.afterT1, Compression.gotH7, Compression.gotBigSigma1,
      Compression.gotCh, Compression.gotH5, Compression.gotH6,
      Compression.gotK, Compression.gotW, Compression.loadedE,
      Functions.unaryReturned, Accessors.loadReturned,
      Accessors.kAtReturned, State.fork] using hfork)
    (by simp [Compression.setupT2H1Path, CopyFree]) (by rfl)
  have hh1 := CompressionGas.hAt_cost_potential
    (Compression.gotT2H2 s msgOff returnDest rest j) (UInt256.ofNat 1) 0
    (UInt256.ofNat 764)
    ([Compression.hValue s 2, 0, UInt256.ofNat 770,
      UInt256.ofNat 0xffffffff, Compression.hValue s 0, Compression.t1 s j,
      Compression.hValue s 4, UInt256.ofNat j, msgOff, returnDest] ++ rest)
    (by simp; omega)
    (by simpa [Compression.gotT2H2, Compression.loadedA,
      Compression.afterT1, Compression.gotH7, Compression.gotBigSigma1,
      Compression.gotCh, Compression.gotH5, Compression.gotH6,
      Compression.gotK, Compression.gotW, Compression.loadedE,
      Functions.unaryReturned, Accessors.loadReturned,
      Accessors.kAtReturned] using hcode)
    (by simpa [Compression.gotT2H2, Compression.loadedA,
      Compression.afterT1, Compression.gotH7, Compression.gotBigSigma1,
      Compression.gotCh, Compression.gotH5, Compression.gotH6,
      Compression.gotK, Compression.gotW, Compression.loadedE,
      Functions.unaryReturned, Accessors.loadReturned,
      Accessors.kAtReturned, State.fork] using hfork)
    (by simpa [Compression.gotT2H2, Compression.loadedA,
      Compression.afterT1, Compression.gotH7, Compression.gotBigSigma1,
      Compression.gotCh, Compression.gotH5, Compression.gotH6,
      Compression.gotK, Compression.gotW, Compression.loadedE,
      Functions.unaryReturned, Accessors.loadReturned,
      Accessors.kAtReturned] using hrun)
    (by simpa [Compression.gotT2H2, Compression.loadedA,
      Compression.afterT1, Compression.gotH7, Compression.gotBigSigma1,
      Compression.gotCh, Compression.gotH5, Compression.gotH6,
      Compression.gotK, Compression.gotW, Compression.loadedE,
      Functions.unaryReturned, Accessors.loadReturned,
      Accessors.kAtReturned] using hnp) (by decide)
  have hsetupMaj := blockCost_potential_of_static Compression.setupMajPath 15
    (Compression.run_setupMaj s msgOff returnDest rest j (by omega)
      hcode hrun)
    (by simpa [Compression.gotT2H1, Compression.gotT2H2,
      Compression.loadedA, Compression.afterT1, Compression.gotH7,
      Compression.gotBigSigma1, Compression.gotCh, Compression.gotH5,
      Compression.gotH6, Compression.gotK, Compression.gotW,
      Compression.loadedE, Functions.unaryReturned, Accessors.loadReturned,
      Accessors.kAtReturned, State.fork] using hfork)
    (by simp [Compression.setupMajPath, CopyFree]) (by rfl)
  have hmaj := ArithmeticGas.gasSteps_maj_cost_potential
    (Compression.gotT2H1 s msgOff returnDest rest j)
    (Compression.hValue s 0) (Compression.hValue s 1)
    (Compression.hValue s 2) 0 (UInt256.ofNat 770)
    ([UInt256.ofNat 0xffffffff, Compression.hValue s 0, Compression.t1 s j,
      Compression.hValue s 4, UInt256.ofNat j, msgOff, returnDest] ++ rest)
    (by simp; omega)
    (by simpa [Compression.gotT2H1, Compression.gotT2H2,
      Compression.loadedA, Compression.afterT1, Compression.gotH7,
      Compression.gotBigSigma1, Compression.gotCh, Compression.gotH5,
      Compression.gotH6, Compression.gotK, Compression.gotW,
      Compression.loadedE, Functions.unaryReturned, Accessors.loadReturned,
      Accessors.kAtReturned] using hcode)
    (by simpa [Compression.gotT2H1, Compression.gotT2H2,
      Compression.loadedA, Compression.afterT1, Compression.gotH7,
      Compression.gotBigSigma1, Compression.gotCh, Compression.gotH5,
      Compression.gotH6, Compression.gotK, Compression.gotW,
      Compression.loadedE, Functions.unaryReturned, Accessors.loadReturned,
      Accessors.kAtReturned, State.fork] using hfork)
    (by simpa [Compression.gotT2H1, Compression.gotT2H2,
      Compression.loadedA, Compression.afterT1, Compression.gotH7,
      Compression.gotBigSigma1, Compression.gotCh, Compression.gotH5,
      Compression.gotH6, Compression.gotK, Compression.gotW,
      Compression.loadedE, Functions.unaryReturned, Accessors.loadReturned,
      Accessors.kAtReturned] using hrun)
    (by simpa [Compression.gotT2H1, Compression.gotT2H2,
      Compression.loadedA, Compression.afterT1, Compression.gotH7,
      Compression.gotBigSigma1, Compression.gotCh, Compression.gotH5,
      Compression.gotH6, Compression.gotK, Compression.gotW,
      Compression.loadedE, Functions.unaryReturned, Accessors.loadReturned,
      Accessors.kAtReturned] using hnp) (by decide)
  have hsetupB0 := blockCost_potential_of_static
    Compression.setupBigSigma0Path 20
    (Compression.run_setupBigSigma0 s msgOff returnDest rest j (by omega)
      hcode hrun)
    (by simpa [Compression.gotMaj, Compression.gotT2H1,
      Compression.gotT2H2, Compression.loadedA, Compression.afterT1,
      Compression.gotH7, Compression.gotBigSigma1, Compression.gotCh,
      Compression.gotH5, Compression.gotH6, Compression.gotK,
      Compression.gotW, Compression.loadedE, Functions.unaryReturned,
      Accessors.loadReturned, Accessors.kAtReturned, State.fork] using hfork)
    (by simp [Compression.setupBigSigma0Path, CopyFree]) (by rfl)
  have hb0 := ArithmeticGas.gasSteps_bigSigma0_cost_potential
    (Compression.gotMaj s msgOff returnDest rest j) (Compression.hValue s 0) 0
    (UInt256.ofNat 780)
    ([Word.evmMaj (Compression.hValue s 0) (Compression.hValue s 1)
      (Compression.hValue s 2), UInt256.ofNat 0xffffffff,
      Compression.hValue s 0, Compression.t1 s j, Compression.hValue s 4,
      UInt256.ofNat j, msgOff, returnDest] ++ rest) (by simp; omega)
    (by simpa [Compression.gotMaj, Compression.gotT2H1,
      Compression.gotT2H2, Compression.loadedA, Compression.afterT1,
      Compression.gotH7, Compression.gotBigSigma1, Compression.gotCh,
      Compression.gotH5, Compression.gotH6, Compression.gotK,
      Compression.gotW, Compression.loadedE, Functions.unaryReturned,
      Accessors.loadReturned, Accessors.kAtReturned] using hcode)
    (by simpa [Compression.gotMaj, Compression.gotT2H1,
      Compression.gotT2H2, Compression.loadedA, Compression.afterT1,
      Compression.gotH7, Compression.gotBigSigma1, Compression.gotCh,
      Compression.gotH5, Compression.gotH6, Compression.gotK,
      Compression.gotW, Compression.loadedE, Functions.unaryReturned,
      Accessors.loadReturned, Accessors.kAtReturned, State.fork] using hfork)
    (by simpa [Compression.gotMaj, Compression.gotT2H1,
      Compression.gotT2H2, Compression.loadedA, Compression.afterT1,
      Compression.gotH7, Compression.gotBigSigma1, Compression.gotCh,
      Compression.gotH5, Compression.gotH6, Compression.gotK,
      Compression.gotW, Compression.loadedE, Functions.unaryReturned,
      Accessors.loadReturned, Accessors.kAtReturned] using hrun)
    (by simpa [Compression.gotMaj, Compression.gotT2H1,
      Compression.gotT2H2, Compression.loadedA, Compression.afterT1,
      Compression.gotH7, Compression.gotBigSigma1, Compression.gotCh,
      Compression.gotH5, Compression.gotH6, Compression.gotK,
      Compression.gotW, Compression.loadedE, Functions.unaryReturned,
      Accessors.loadReturned, Accessors.kAtReturned] using hnp) (by decide)
  have hfinish := blockCost_potential_of_static Compression.finishT2Path 7
    (Compression.run_finishT2 s msgOff returnDest rest j (by omega) hrun)
    (by simpa [Compression.gotBigSigma0, Compression.gotMaj,
      Compression.gotT2H1, Compression.gotT2H2, Compression.loadedA,
      Compression.afterT1, Compression.gotH7, Compression.gotBigSigma1,
      Compression.gotCh, Compression.gotH5, Compression.gotH6,
      Compression.gotK, Compression.gotW, Compression.loadedE,
      Functions.unaryReturned, Accessors.loadReturned,
      Accessors.kAtReturned, State.fork] using hfork)
    (by simp [Compression.finishT2Path, CopyFree]) (by rfl)
  have hawH2 :
      (Compression.callT2H2 s msgOff returnDest rest j).activeWords =
        (Compression.loadedA s msgOff returnDest rest j).activeWords := by rfl
  have hawH1 :
      (Compression.callT2H1 s msgOff returnDest rest j).activeWords =
        (Compression.gotT2H2 s msgOff returnDest rest j).activeWords := by rfl
  have hawMaj :
      (Compression.callMaj s msgOff returnDest rest j).activeWords =
        (Compression.gotT2H1 s msgOff returnDest rest j).activeWords := by rfl
  have hawB0 :
      (Compression.callBigSigma0 s msgOff returnDest rest j).activeWords =
        (Compression.gotMaj s msgOff returnDest rest j).activeWords := by rfl
  simp only [Compression.gasSteps_t2,
    Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost]
  rw [hawH2] at hsetupH2
  rw [hawH1] at hsetupH1
  rw [hawMaj] at hsetupMaj
  rw [hawB0] at hsetupB0
  change _ = 37 + MachineState.memCost
    (Compression.gotT2H2 s msgOff returnDest rest j).activeWords.toNat at hh2
  change _ = 37 + MachineState.memCost
    (Compression.gotT2H1 s msgOff returnDest rest j).activeWords.toNat at hh1
  change _ = 56 + MachineState.memCost
    (Compression.gotMaj s msgOff returnDest rest j).activeWords.toNat at hmaj
  change _ = 256 + MachineState.memCost
    (Compression.gotBigSigma0 s msgOff returnDest rest j).activeWords.toNat at hb0
  omega


end Challenge.Sha256.Reference.Proofs.Bytecode.CompressionGas
