import Challenge.Modexp.Reference.Proofs.Bytecode.BigDispatch
import Challenge.Modexp.Reference.Proofs.Bytecode.BigSetup
import Challenge.Modexp.Reference.Proofs.Bytecode.BigSerialize
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
/-! # Complete certified nonzero multi-limb MODEXP path -/

namespace Challenge.Modexp.Reference.Proofs.Bytecode.BigComplete

open EvmSemantics
open EvmSemantics.EVM

open BigExponent

def scanRest (b e m baseOff expOff modOff : Nat)
    (returnDest : UInt256) (rest : List UInt256) : List UInt256 :=
  [UInt256.ofNat b, UInt256.ofNat e, UInt256.ofNat m,
    UInt256.ofNat baseOff, UInt256.ofNat expOff, UInt256.ofNat modOff,
    returnDest] ++ rest

def baseRest (expOff modOff : Nat) (returnDest : UInt256)
    (rest : List UInt256) : List UInt256 :=
  [UInt256.ofNat expOff, UInt256.ofNat modOff, returnDest] ++ rest

def exponentRest (modOff : Nat) (returnDest : UInt256)
    (rest : List UInt256) : List UInt256 :=
  [UInt256.ofNat modOff, returnDest] ++ rest

def setupState (s : State) (b e m baseOff expOff modOff : Nat)
    (returnDest : UInt256) (rest : List UInt256) : State :=
  BigSetup.setupReturned s b e m baseOff expOff modOff returnDest rest

def limbCount (m : Nat) : Nat := Limbs.limbCount m

def modulusOr (s : State) (b e m baseOff expOff modOff : Nat)
    (returnDest : UInt256) (rest : List UInt256) : UInt256 :=
  BigModulus.scanOr
    (setupState s b e m baseOff expOff modOff returnDest rest).memory
    (limbCount m)

def baseState (s : State) (b e m baseOff expOff modOff : Nat)
    (returnDest : UInt256) (rest : List UInt256) : State :=
  let loaded := setupState s b e m baseOff expOff modOff returnDest rest
  BigBase.baseLoopEntry loaded
    (modulusOr s b e m baseOff expOff modOff returnDest rest) (limbCount m)
    (scanRest b e m baseOff expOff modOff returnDest rest)

def exponentState (s : State) (b e m baseOff expOff modOff : Nat)
    (returnDest : UInt256) (rest : List UInt256) : State :=
  let accumulator := modulusOr s b e m baseOff expOff modOff returnDest rest
  let base := baseState s b e m baseOff expOff modOff returnDest rest
  BigBaseLoop.initialAccumulator base accumulator (limbCount m) b e m baseOff
    (baseRest expOff modOff returnDest rest)

def exponentProgressState (s : State) (b e m baseOff expOff modOff : Nat)
    (returnDest : UInt256) (rest : List UInt256) : State :=
  let accumulator := modulusOr s b e m baseOff expOff modOff returnDest rest
  let entry := exponentState s b e m baseOff expOff modOff returnDest rest
  BigExponent.exponentByteProgress entry accumulator (limbCount m) b e m
    baseOff expOff (exponentRest modOff returnDest rest) e

def completedState (s : State) (b e m baseOff expOff modOff : Nat)
    (returnDest : UInt256) (rest : List UInt256) : State :=
  let accumulator := modulusOr s b e m baseOff expOff modOff returnDest rest
  let progress := exponentProgressState s b e m baseOff expOff modOff
    returnDest rest
  BigSerialize.bigReturned progress accumulator (limbCount m) b e m baseOff
    expOff (exponentRest modOff returnDest rest)

def gasSteps_startExponent (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (hcap : rest.length < 1017)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (exponentEntry s accumulatorWord count b e m baseOff expOff rest)
      (outerLoop s accumulatorWord count b e m baseOff expOff rest 0) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka startExponentPath
      (by simpa [exponentEntry, Artifact.referenceArtifact] using hcode)
      (by simpa [exponentEntry, State.fork] using hfork)
      (run_startExponent s accumulatorWord count b e m baseOff expOff rest
        hcap hrun)
      (by simpa [exponentEntry] using hrun)
      (by simpa [exponentEntry, State.fork] using hnp)

theorem gasSteps_startExponent_cost_potential (s : State)
    (accumulatorWord : UInt256) (count b e m baseOff expOff : Nat)
    (rest : List UInt256) (hcap : rest.length < 1017)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    (gasSteps_startExponent s accumulatorWord count b e m baseOff expOff rest
      hcap hcode hfork hrun hnp).cost +
        MachineState.memCost
          (exponentEntry s accumulatorWord count b e m baseOff expOff rest).activeWords.toNat =
      3 + MachineState.memCost
        (outerLoop s accumulatorWord count b e m baseOff expOff rest 0).activeWords.toNat := by
  have hmeter :=
    Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
      startExponentPath 3
        (run_startExponent s accumulatorWord count b e m baseOff expOff rest
          hcap hrun)
        (by simpa [exponentEntry, State.fork] using hfork)
        (by decide) (by decide)
  simpa [gasSteps_startExponent] using hmeter

def gasSteps_nonzero (s : State) (b e m baseOff expOff modOff : Nat)
    (returnDest : UInt256) (rest : List UInt256)
    (hmBound : m ≤ 1024) (hmodOff : modOff < 2 ^ 256)
    (hinputFit : modOff + m ≤ 2 ^ 256) (hbase : b < 2 ^ 256)
    (hbaseFit : baseOff + b < 2 ^ 256) (hexp : e < 2 ^ 256)
    (hexpFit : expOff + e < 2 ^ 256) (hcap : rest.length < 960)
    (hor : modulusOr s b e m baseOff expOff modOff returnDest rest ≠ 0)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (BigSetup.setupEntry s b e m baseOff expOff modOff returnDest rest)
      (completedState s b e m baseOff expOff modOff returnDest rest) := by
  let n := limbCount m
  let loaded := setupState s b e m baseOff expOff modOff returnDest rest
  let scanTail := scanRest b e m baseOff expOff modOff returnDest rest
  let accumulator := modulusOr s b e m baseOff expOff modOff returnDest rest
  let baseTail := baseRest expOff modOff returnDest rest
  let expTail := exponentRest modOff returnDest rest
  let base := baseState s b e m baseOff expOff modOff returnDest rest
  let expEntry := exponentState s b e m baseOff expOff modOff returnDest rest
  let expProgress := exponentProgressState s b e m baseOff expOff modOff
    returnDest rest
  have hnLe : n ≤ 32 := Limbs.limbCount_le_32 m hmBound
  have hn : n < 2 ^ 256 := by omega
  have hsetup := BigSetup.gasSteps_setup s b e m baseOff expOff modOff
    returnDest rest hmBound hmodOff hinputFit (by omega) hcode hfork hrun hnp
  have hscan := BigModulus.gasSteps_scanNonzeroTotal loaded n scanTail
    (by simp [scanTail, scanRest]; omega) hnLe hor
    (by change s.executionEnv.code = referenceBytecode; exact hcode)
    (by change s.fork = .Osaka; exact hfork)
    (by change s.halt = .Running; exact hrun)
    (by
      change Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
        s.executionEnv.codeAddr = false
      exact hnp)
  have hbaseSetup := BigBase.gasSteps_baseSetup loaded accumulator n scanTail
    (by simp [scanTail, scanRest]; omega) rfl hn
    (by change s.executionEnv.code = referenceBytecode; exact hcode)
    (by change s.fork = .Osaka; exact hfork)
    (by change s.halt = .Running; exact hrun)
    (by
      change Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
        s.executionEnv.codeAddr = false
      exact hnp)
  have hconversion := BigBaseLoop.gasSteps_baseConversion base accumulator n b e
    m baseOff baseTail (by simp [baseTail, baseRest]; omega) hn hbase hbaseFit
    (by change s.executionEnv.code = referenceBytecode; exact hcode)
    (by change s.fork = .Osaka; exact hfork)
    (by change s.halt = .Running; exact hrun)
    (by
      change Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
        s.executionEnv.codeAddr = false
      exact hnp)
  have hExpEnv : expEntry.executionEnv = s.executionEnv := by
    calc
      expEntry.executionEnv = loaded.executionEnv := by
        simp [expEntry, exponentState, BigBaseLoop.initialAccumulator,
          BigBaseLoop.baseConvertedExit, BigBase.outerExit, BigBase.outerLoop,
          BigHelpers.addReturned, base, baseState, BigBase.baseLoopEntry,
          BigBase.afterClearDouble, BigHelpers.clearReturned,
          BigModulus.scanNonzero, loaded]
      _ = s.executionEnv := by rfl
  have hExpHalt : expEntry.halt = s.halt := by
    calc
      expEntry.halt = loaded.halt := by
        simp [expEntry, exponentState, BigBaseLoop.initialAccumulator,
          BigBaseLoop.baseConvertedExit, BigBase.outerExit, BigBase.outerLoop,
          BigHelpers.addReturned, base, baseState, BigBase.baseLoopEntry,
          BigBase.afterClearDouble, BigHelpers.clearReturned,
          BigModulus.scanNonzero, loaded]
      _ = s.halt := by rfl
  have hProgressEnv : expProgress.executionEnv = s.executionEnv := by
    rw [show expProgress = BigExponent.exponentByteProgress expEntry accumulator
      n b e m baseOff expOff expTail e by rfl]
    rw [BigExponent.exponentByteProgress_executionEnv]
    exact hExpEnv
  have hProgressHalt : expProgress.halt = s.halt := by
    rw [show expProgress = BigExponent.exponentByteProgress expEntry accumulator
      n b e m baseOff expOff expTail e by rfl]
    rw [BigExponent.exponentByteProgress_halt]
    exact hExpHalt
  have hstart := gasSteps_startExponent expEntry accumulator n b e m baseOff
    expOff expTail (by simp [expTail, exponentRest]; omega)
    (by rw [hExpEnv]; exact hcode)
    (by change expEntry.executionEnv.fork = .Osaka; rw [hExpEnv]; exact hfork)
    (by rw [hExpHalt]; exact hrun)
    (by
      rw [hExpEnv]
      exact hnp)
  have hexponent := BigExponent.gasSteps_exponentLoop expEntry accumulator n b e
    m baseOff expOff expTail (by simp [expTail, exponentRest]; omega) hn hexp
    hexpFit
    (by rw [hExpEnv]; exact hcode)
    (by change expEntry.executionEnv.fork = .Osaka; rw [hExpEnv]; exact hfork)
    (by rw [hExpHalt]; exact hrun)
    (by
      rw [hExpEnv]
      exact hnp)
  have hserialize := BigSerialize.gasSteps_serializeResult expProgress accumulator
    n b e m baseOff expOff expTail (by simp [expTail, exponentRest]; omega)
    hexp (by omega)
    (by rw [hProgressEnv]; exact hcode)
    (by change expProgress.executionEnv.fork = .Osaka
        rw [hProgressEnv]
        exact hfork)
    (by rw [hProgressHalt]; exact hrun)
    (by
      rw [hProgressEnv]
      exact hnp)
  exact Challenge.EvmProof.GasSteps.cast
    (hsetup.trans (hscan.trans (hbaseSetup.trans
      (hconversion.trans (hstart.trans (hexponent.trans hserialize))))))
    rfl
    (by simp [completedState, expProgress, exponentProgressState, accumulator,
      n, expTail])

def nonzeroWork (n b e m : Nat) : Nat :=
  (343 + n * 284 + m * 190) +
  (50 + n * 74) +
  (77 + n * 71) +
  (b * (3506 + n * 7248) + (206 + n * 453)) +
  3 +
  e * (106 + 8 * (613 + n * 526 +
    2 * (n * (102 + 256 * (426 + n * 906))))) +
  (66 + m * 138)

theorem gasSteps_nonzero_cost_potential (s : State)
    (b e m baseOff expOff modOff : Nat) (returnDest : UInt256)
    (rest : List UInt256) (hmBound : m ≤ 1024)
    (hmodOff : modOff < 2 ^ 256) (hinputFit : modOff + m ≤ 2 ^ 256)
    (hbase : b < 2 ^ 256) (hbaseFit : baseOff + b < 2 ^ 256)
    (hexp : e < 2 ^ 256) (hexpFit : expOff + e < 2 ^ 256)
    (hcap : rest.length < 960)
    (hor : modulusOr s b e m baseOff expOff modOff returnDest rest ≠ 0)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    (gasSteps_nonzero s b e m baseOff expOff modOff returnDest rest hmBound
        hmodOff hinputFit hbase hbaseFit hexp hexpFit hcap hor hcode hfork hrun
        hnp).cost + MachineState.memCost s.activeWords.toNat =
      nonzeroWork (limbCount m) b e m + MachineState.memCost
        (completedState s b e m baseOff expOff modOff returnDest rest).activeWords.toNat := by
  let n := limbCount m
  let loaded := setupState s b e m baseOff expOff modOff returnDest rest
  let scanTail := scanRest b e m baseOff expOff modOff returnDest rest
  let accumulator := modulusOr s b e m baseOff expOff modOff returnDest rest
  let baseTail := baseRest expOff modOff returnDest rest
  let expTail := exponentRest modOff returnDest rest
  let base := baseState s b e m baseOff expOff modOff returnDest rest
  let expEntry := exponentState s b e m baseOff expOff modOff returnDest rest
  let expProgress := exponentProgressState s b e m baseOff expOff modOff
    returnDest rest
  have hnLe : n ≤ 32 := Limbs.limbCount_le_32 m hmBound
  have hn : n < 2 ^ 256 := by omega
  have hExpEnv : expEntry.executionEnv = s.executionEnv := by
    calc
      expEntry.executionEnv = loaded.executionEnv := by
        simp [expEntry, exponentState, BigBaseLoop.initialAccumulator,
          BigBaseLoop.baseConvertedExit, BigBase.outerExit, BigBase.outerLoop,
          BigHelpers.addReturned, base, baseState, BigBase.baseLoopEntry,
          BigBase.afterClearDouble, BigHelpers.clearReturned,
          BigModulus.scanNonzero, loaded]
      _ = s.executionEnv := by rfl
  have hExpHalt : expEntry.halt = s.halt := by
    calc
      expEntry.halt = loaded.halt := by
        simp [expEntry, exponentState, BigBaseLoop.initialAccumulator,
          BigBaseLoop.baseConvertedExit, BigBase.outerExit, BigBase.outerLoop,
          BigHelpers.addReturned, base, baseState, BigBase.baseLoopEntry,
          BigBase.afterClearDouble, BigHelpers.clearReturned,
          BigModulus.scanNonzero, loaded]
      _ = s.halt := by rfl
  have hProgressEnv : expProgress.executionEnv = s.executionEnv := by
    rw [show expProgress = BigExponent.exponentByteProgress expEntry accumulator
      n b e m baseOff expOff expTail e by rfl]
    rw [BigExponent.exponentByteProgress_executionEnv]
    exact hExpEnv
  have hProgressHalt : expProgress.halt = s.halt := by
    rw [show expProgress = BigExponent.exponentByteProgress expEntry accumulator
      n b e m baseOff expOff expTail e by rfl]
    rw [BigExponent.exponentByteProgress_halt]
    exact hExpHalt
  have seamSetup : BigSetup.setupReturned s b e m baseOff expOff modOff
      returnDest rest = loaded := by rfl
  have seamBase : BigBase.baseLoopEntry loaded accumulator n scanTail =
      BigBaseLoop.baseLoopState base accumulator n b e m baseOff baseTail 0 := by
    rfl
  have seamExpEntry : BigBaseLoop.initialAccumulator base accumulator n b e m
      baseOff baseTail = BigExponent.exponentEntry expEntry accumulator n b e m
        baseOff expOff expTail := by
    rfl
  have seamExpStart : BigExponent.outerLoop expEntry accumulator n b e m
      baseOff expOff expTail 0 = BigExponent.exponentOuterState expEntry
        accumulator n b e m baseOff expOff expTail 0 := by
    rfl
  have seamExpFinish : BigExponent.exponentOuterState expEntry accumulator n b e
      m baseOff expOff expTail e = BigExponent.outerLoop expProgress accumulator
        n b e m baseOff expOff expTail e := by
    rfl
  have seamFinal : BigSerialize.bigReturned expProgress accumulator n b e m
      baseOff expOff expTail =
        completedState s b e m baseOff expOff modOff returnDest rest := by
    rfl
  let hsetup := BigSetup.gasSteps_setup s b e m baseOff expOff modOff
    returnDest rest hmBound hmodOff hinputFit (by omega) hcode hfork hrun hnp
  let hscan := BigModulus.gasSteps_scanNonzeroTotal loaded n scanTail
    (by simp [scanTail, scanRest]; omega) hnLe hor
    (by change s.executionEnv.code = referenceBytecode; exact hcode)
    (by change s.fork = .Osaka; exact hfork)
    (by change s.halt = .Running; exact hrun)
    (by
      change Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
        s.executionEnv.codeAddr = false
      exact hnp)
  let hbaseSetup := BigBase.gasSteps_baseSetup loaded accumulator n scanTail
    (by simp [scanTail, scanRest]; omega) rfl hn
    (by change s.executionEnv.code = referenceBytecode; exact hcode)
    (by change s.fork = .Osaka; exact hfork)
    (by change s.halt = .Running; exact hrun)
    (by
      change Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
        s.executionEnv.codeAddr = false
      exact hnp)
  let hconversion := BigBaseLoop.gasSteps_baseConversion base accumulator n b e
    m baseOff baseTail (by simp [baseTail, baseRest]; omega) hn hbase hbaseFit
    (by change s.executionEnv.code = referenceBytecode; exact hcode)
    (by change s.fork = .Osaka; exact hfork)
    (by change s.halt = .Running; exact hrun)
    (by
      change Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
        s.executionEnv.codeAddr = false
      exact hnp)
  let hstart := gasSteps_startExponent expEntry accumulator n b e m baseOff
    expOff expTail (by simp [expTail, exponentRest]; omega)
    (by rw [hExpEnv]; exact hcode)
    (by change expEntry.executionEnv.fork = .Osaka; rw [hExpEnv]; exact hfork)
    (by rw [hExpHalt]; exact hrun)
    (by rw [hExpEnv]; exact hnp)
  let hexponent := BigExponent.gasSteps_exponentLoop expEntry accumulator n b e
    m baseOff expOff expTail (by simp [expTail, exponentRest]; omega) hn hexp
    hexpFit (by rw [hExpEnv]; exact hcode)
    (by change expEntry.executionEnv.fork = .Osaka; rw [hExpEnv]; exact hfork)
    (by rw [hExpHalt]; exact hrun)
    (by rw [hExpEnv]; exact hnp)
  let hserialize := BigSerialize.gasSteps_serializeResult expProgress accumulator
    n b e m baseOff expOff expTail (by simp [expTail, exponentRest]; omega)
    hexp (by omega) (by rw [hProgressEnv]; exact hcode)
    (by change expProgress.executionEnv.fork = .Osaka
        rw [hProgressEnv]
        exact hfork)
    (by rw [hProgressHalt]; exact hrun)
    (by rw [hProgressEnv]; exact hnp)
  have csetup := BigSetup.gasSteps_setup_cost_potential s b e m baseOff expOff
    modOff returnDest rest hmBound hmodOff hinputFit (by omega) hcode hfork hrun
    hnp
  have cscan := BigModulus.gasSteps_scanNonzeroTotal_cost_potential loaded n
    scanTail (by simp [scanTail, scanRest]; omega) hnLe hor
    (by change s.executionEnv.code = referenceBytecode; exact hcode)
    (by change s.fork = .Osaka; exact hfork)
    (by change s.halt = .Running; exact hrun)
    (by
      change Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
        s.executionEnv.codeAddr = false
      exact hnp)
  have cbase := BigBase.gasSteps_baseSetup_cost_potential loaded accumulator n
    scanTail (by simp [scanTail, scanRest]; omega) rfl hn
    (by change s.executionEnv.code = referenceBytecode; exact hcode)
    (by change s.fork = .Osaka; exact hfork)
    (by change s.halt = .Running; exact hrun)
    (by
      change Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
        s.executionEnv.codeAddr = false
      exact hnp)
  have cconversion := BigBaseLoop.gasSteps_baseConversion_cost_potential base
    accumulator n b e m baseOff baseTail
    (by simp [baseTail, baseRest]; omega) hn hbase hbaseFit
    (by change s.executionEnv.code = referenceBytecode; exact hcode)
    (by change s.fork = .Osaka; exact hfork)
    (by change s.halt = .Running; exact hrun)
    (by
      change Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
        s.executionEnv.codeAddr = false
      exact hnp)
  have cstart := gasSteps_startExponent_cost_potential expEntry accumulator n b
    e m baseOff expOff expTail (by simp [expTail, exponentRest]; omega)
    (by rw [hExpEnv]; exact hcode)
    (by change expEntry.executionEnv.fork = .Osaka; rw [hExpEnv]; exact hfork)
    (by rw [hExpHalt]; exact hrun) (by rw [hExpEnv]; exact hnp)
  have cexponent := BigExponent.gasSteps_exponentLoop_cost_potential expEntry
    accumulator n b e m baseOff expOff expTail
    (by simp [expTail, exponentRest]; omega) hn hexp hexpFit
    (by rw [hExpEnv]; exact hcode)
    (by change expEntry.executionEnv.fork = .Osaka; rw [hExpEnv]; exact hfork)
    (by rw [hExpHalt]; exact hrun) (by rw [hExpEnv]; exact hnp)
  have cserialize := BigSerialize.gasSteps_serializeResult_cost_potential
    expProgress accumulator n b e m baseOff expOff expTail
    (by simp [expTail, exponentRest]; omega) hexp (by omega)
    (by rw [hProgressEnv]; exact hcode)
    (by change expProgress.executionEnv.fork = .Osaka
        rw [hProgressEnv]
        exact hfork)
    (by rw [hProgressHalt]; exact hrun)
    (by rw [hProgressEnv]; exact hnp)
  have seamSetupCost := congrArg
    (fun q : State => MachineState.memCost q.activeWords.toNat) seamSetup
  have seamBaseCost := congrArg
    (fun q : State => MachineState.memCost q.activeWords.toNat) seamBase
  have seamExpEntryCost := congrArg
    (fun q : State => MachineState.memCost q.activeWords.toNat) seamExpEntry
  have seamExpStartCost := congrArg
    (fun q : State => MachineState.memCost q.activeWords.toNat) seamExpStart
  have seamExpFinishCost := congrArg
    (fun q : State => MachineState.memCost q.activeWords.toNat) seamExpFinish
  have seamFinalCost := congrArg
    (fun q : State => MachineState.memCost q.activeWords.toNat) seamFinal
  rw [seamSetupCost] at csetup
  rw [seamBaseCost] at cbase
  rw [seamExpEntryCost] at cconversion
  rw [seamExpStartCost] at cstart
  rw [seamExpFinishCost] at cexponent
  rw [seamFinalCost] at cserialize
  change (hsetup.cost + (hscan.cost + (hbaseSetup.cost +
      (hconversion.cost + (hstart.cost + (hexponent.cost + hserialize.cost)))))) +
      MachineState.memCost s.activeWords.toNat = _
  simp only [n, loaded, scanTail, accumulator, baseTail, expTail, base,
    expEntry, expProgress, hsetup, hscan, hbaseSetup, hconversion, hstart,
    hexponent, hserialize, nonzeroWork, limbCount] at csetup cscan cbase cconversion cstart cexponent cserialize ⊢
  omega

end Challenge.Modexp.Reference.Proofs.Bytecode.BigComplete
