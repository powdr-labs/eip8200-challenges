import Challenge.Ripemd160.Reference.Proofs.Bytecode.CompressionCostTrace
import Challenge.Ripemd160.Reference.Proofs.Bytecode.BooleanFunctionTrace
import Batteries.Tactic.OpenPrivate

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000

namespace Challenge.Ripemd160.Reference.Proofs.Bytecode.CompressionRoundCostTrace

open Challenge.EvmProof
open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open CompressionCostTrace

open private afterLoads roundTail xReturnedState genericFTail genericT0
  genericRot1Tail genericAfterFirstStores genericRot2Tail genericSetTail
  genericReturned bodyEntry rotlValue from
  Challenge.Ripemd160.Reference.Proofs.Bytecode.RoundTrace

def hAtWork : Nat := Meter.runLocatedBlockStaticCost TableTrace.hAtPath
def hSetWork : Nat := Meter.runLocatedBlockStaticCost TableTrace.hSetPath
def xSetWork : Nat := Meter.runLocatedBlockStaticCost TableTrace.xSetPath
def fCaseWork (j : Nat) : Nat :=
  Meter.runLocatedBlockStaticCost (BooleanFunctionTrace.casePath j)
def rotlWork : Nat := Meter.runLocatedBlockStaticCost RoundTrace.rotlPath

def roundBodyWork (j : Nat) : Nat :=
  Meter.runLocatedBlockStaticCost RoundTrace.afterXPath + fCaseWork j +
  Meter.runLocatedBlockStaticCost RoundTrace.afterFPath + rotlWork +
  Meter.runLocatedBlockStaticCost RoundTrace.afterRot1Path + rotlWork +
  Meter.runLocatedBlockStaticCost RoundTrace.afterRot2Path + wordSetWork +
  Meter.runLocatedBlockStaticCost RoundTrace.suffixPath

def roundWork (j : Nat) : Nat :=
  Meter.runLocatedBlockStaticCost RoundTrace.prefixPath + xAtWork +
    roundBodyWork j

theorem hAtWork_eq : hAtWork = 37 := by rfl
theorem hSetWork_eq : hSetWork = 42 := by rfl
theorem rotlWork_eq : rotlWork = 54 := by rfl

theorem fCaseWork_eq (j : Nat) (hj : j < 5) :
    fCaseWork j = [81, 116, 142, 168, 158][j]! := by
  interval_cases j <;> rfl

theorem roundWork_eq (j : Nat) (hj : j < 5) :
    roundWork j = [585, 620, 646, 672, 662][j]! := by
  interval_cases j <;> rfl

theorem rotl_cost_potential (s : State) (x n returnDest : UInt256)
    (rest : List UInt256) (hstack : rest.length < 1015)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hvalid : Decode.isValidJumpDest referenceBytecode returnDest.toNat = true) :
    (RoundTrace.gasSteps_rotl s x n returnDest rest hstack hcode hfork hrun
      hnp hvalid).cost + MachineState.memCost s.activeWords.toNat =
      rotlWork + MachineState.memCost
        (RoundTrace.rotlReturned s x n returnDest rest).activeWords.toNat := by
  have hraw := blockCost_potential RoundTrace.rotlPath
    (RoundTrace.rotlEntry s x n returnDest rest)
    (RoundTrace.rotlReturned s x n returnDest rest)
    (RoundTrace.run_rotl s x n returnDest rest hstack hcode hrun hvalid)
    (by simpa [RoundTrace.rotlEntry] using hfork)
    (by simp [RoundTrace.rotlPath, CopyFree])
  simpa [RoundTrace.gasSteps_rotl, RoundTrace.rotlEntry, rotlWork] using hraw

theorem hAt_cost_potential (s : State) (i returnDest : UInt256)
    (rest : List UInt256) (hstack : rest.length < 1018)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hvalid : Decode.isValidJumpDest referenceBytecode returnDest.toNat = true) :
    (TableTrace.gasSteps_hAt s i returnDest rest hstack hcode hfork hrun hnp
      hvalid).cost + MachineState.memCost s.activeWords.toNat =
      hAtWork + MachineState.memCost
        (TableTrace.atReturned s (UInt256.ofNat 0x20) i returnDest rest).activeWords.toNat := by
  have hraw := blockCost_potential TableTrace.hAtPath
    (TableTrace.atEntry s (UInt256.ofNat 0x20) i returnDest rest)
    (TableTrace.atReturned s (UInt256.ofNat 0x20) i returnDest rest)
    (TableTrace.run_hAt s i returnDest rest hstack hcode hrun hvalid)
    (by simpa [TableTrace.atEntry] using hfork)
    (by simp [TableTrace.hAtPath, CopyFree])
  simpa [TableTrace.gasSteps_hAt, TableTrace.atEntry, hAtWork] using hraw

theorem hSet_cost_potential (s : State) (i value returnDest : UInt256)
    (rest : List UInt256) (hstack : rest.length < 1016)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hvalid : Decode.isValidJumpDest referenceBytecode returnDest.toNat = true) :
    (TableTrace.gasSteps_hSet s i value returnDest rest hstack hcode hfork
      hrun hnp hvalid).cost + MachineState.memCost s.activeWords.toNat =
      hSetWork + MachineState.memCost
        (TableTrace.hSetReturned s i value returnDest rest).activeWords.toNat := by
  simpa [TableTrace.gasSteps_hSet, TableTrace.hSetEntry,
    TableTrace.hSetReturned, hSetWork, CompressionCostTrace.wordSetWork] using
    CompressionCostTrace.wordSet_cost_potential s (UInt256.ofNat 0x20) i value
      returnDest rest hstack hcode hfork hrun hnp hvalid

theorem xSet_cost_potential (s : State) (i value returnDest : UInt256)
    (rest : List UInt256) (hstack : rest.length < 1017)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hvalid : Decode.isValidJumpDest referenceBytecode returnDest.toNat = true) :
    (TableTrace.gasSteps_xSet s i value returnDest rest hstack hcode hfork
      hrun hnp hvalid).cost + MachineState.memCost s.activeWords.toNat =
      xSetWork + MachineState.memCost
        (TableTrace.xSetReturned s i value returnDest rest).activeWords.toNat := by
  have hraw := blockCost_potential TableTrace.xSetPath
    (TableTrace.xSetEntry s i value returnDest rest)
    (TableTrace.xSetReturned s i value returnDest rest)
    (TableTrace.run_xSet s i value returnDest rest hstack hcode hrun hvalid)
    (by simpa [TableTrace.xSetEntry] using hfork)
    (by simp [TableTrace.xSetPath, Schedule.xSetPath, CopyFree])
  simpa [TableTrace.gasSteps_xSet, TableTrace.xSetEntry, xSetWork] using hraw

theorem fCase_cost_potential (s : State) (j : Nat) (hj : j < 5)
    (x y z returnDest : UInt256) (rest : List UInt256)
    (hstack : rest.length < 1008)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hvalid : Decode.isValidJumpDest referenceBytecode returnDest.toNat = true) :
    (BooleanFunctionTrace.gasSteps_fCase s j hj x y z returnDest rest hstack
      hcode hfork hrun hnp hvalid).cost +
        MachineState.memCost s.activeWords.toNat =
      fCaseWork j + MachineState.memCost
        (BooleanFunctionTrace.fReturned s j x y z returnDest rest).activeWords.toNat := by
  have hraw := blockCost_potential (BooleanFunctionTrace.casePath j)
    (BooleanFunctionTrace.fEntry s j x y z returnDest rest)
    (BooleanFunctionTrace.fReturned s j x y z returnDest rest)
    (BooleanFunctionTrace.run_fCase s j hj x y z returnDest rest hstack hcode
      hrun hvalid)
    (by simpa [BooleanFunctionTrace.fEntry] using hfork)
    (by
      interval_cases j <;>
        simp [BooleanFunctionTrace.casePath, BooleanFunctionTrace.test0,
          BooleanFunctionTrace.test1, BooleanFunctionTrace.test2,
          BooleanFunctionTrace.test3, BooleanFunctionTrace.arm0,
          BooleanFunctionTrace.arm1, BooleanFunctionTrace.arm2,
          BooleanFunctionTrace.arm3, BooleanFunctionTrace.arm4,
          BooleanFunctionTrace.cleanup, CopyFree])
  simpa [BooleanFunctionTrace.gasSteps_fCase,
    BooleanFunctionTrace.fEntry, fCaseWork] using hraw

private theorem potential_trans
    (cost₁ work₁ cost₂ work₂ p₀ p₁ p₂ : Nat)
    (h₁ : cost₁ + p₀ = work₁ + p₁)
    (h₂ : cost₂ + p₁ = work₂ + p₂) :
    (cost₁ + cost₂) + p₀ = (work₁ + work₂) + p₂ := by
  omega

theorem roundBody_cost_potential (q : State) (base : UInt256)
    (j : Nat) (hj : j < 5) (wordIndex rotation k returnDest word : UInt256)
    (a b c d e : UInt256) (rest : List UInt256)
    (hstack : rest.length < 980)
    (hcode : q.executionEnv.code = referenceBytecode)
    (hfork : q.fork = .Osaka) (hrun : q.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig q.executionEnv.precompileConfig q.executionEnv.fork
      q.executionEnv.codeAddr = false)
    (hvalid : Decode.isValidJumpDest referenceBytecode returnDest.toNat = true) :
    (RoundTrace.gasSteps_roundBody q base j hj wordIndex rotation k returnDest
      word a b c d e rest hstack hcode hfork hrun hnp hvalid).cost +
        MachineState.memCost q.activeWords.toNat =
      roundBodyWork j + MachineState.memCost
        (genericReturned (genericAfterFirstStores q base e d) base j
          word rotation k returnDest a b c d e rest).activeWords.toNat := by
  let q2 := genericAfterFirstStores q base e d
  have hcode2 : q2.executionEnv.code = referenceBytecode := by
    simpa [q2, genericAfterFirstStores, TableTrace.storedWord] using hcode
  have hfork2 : q2.fork = .Osaka := by
    simpa [q2, genericAfterFirstStores, TableTrace.storedWord] using hfork
  have hrun2 : q2.halt = .Running := by
    simpa [q2, genericAfterFirstStores, TableTrace.storedWord] using hrun
  have hnp2 : Precompile.isPrecompileWithConfig q2.executionEnv.precompileConfig q2.executionEnv.fork
      q2.executionEnv.codeAddr = false := by
    simpa [q2, genericAfterFirstStores, TableTrace.storedWord] using hnp
  have h0 := blockCost_potential RoundTrace.afterXPath
    (bodyEntry q base j wordIndex rotation k returnDest word a b c d e rest)
    (BooleanFunctionTrace.fEntry q j b c d (UInt256.ofNat 0x147)
      (genericFTail base j wordIndex rotation k returnDest word a b c d e rest))
    (RoundTrace.run_afterX q base j wordIndex rotation k returnDest word
      a b c d e rest hstack hcode hrun)
    (by simpa [bodyEntry] using hfork)
    (by simp [RoundTrace.afterXPath, CopyFree])
  have h1 := fCase_cost_potential q j hj b c d (UInt256.ofNat 0x147)
    (genericFTail base j wordIndex rotation k returnDest word a b c d e rest)
    (by simp [genericFTail]; omega) hcode hfork hrun hnp
    (by
      exact Artifact.referenceArtifact.isValidJumpDest_index 243 (by rfl))
  have h2 := blockCost_potential RoundTrace.afterFPath
    (BooleanFunctionTrace.fReturned q j b c d (UInt256.ofNat 0x147)
      (genericFTail base j wordIndex rotation k returnDest word a b c d e rest))
    (RoundTrace.rotlEntry q (genericT0 j word k a b c d) rotation
      (UInt256.ofNat 0x15d)
      (genericRot1Tail base j wordIndex rotation k returnDest word
        a b c d e rest))
    (RoundTrace.run_afterF q base j wordIndex rotation k returnDest word
      a b c d e rest hstack hcode hrun)
    (by simpa [BooleanFunctionTrace.fReturned] using hfork)
    (by simp [RoundTrace.afterFPath, CopyFree])
  have h3 := rotl_cost_potential q (genericT0 j word k a b c d) rotation
    (UInt256.ofNat 0x15d)
    (genericRot1Tail base j wordIndex rotation k returnDest word
      a b c d e rest)
    (by simp [genericRot1Tail]; omega) hcode hfork hrun hnp
    (by
      exact Artifact.referenceArtifact.isValidJumpDest_index 257 (by rfl))
  have h4 := blockCost_potential RoundTrace.afterRot1Path
    (RoundTrace.rotlReturned q (genericT0 j word k a b c d) rotation
      (UInt256.ofNat 0x15d)
      (genericRot1Tail base j wordIndex rotation k returnDest word
        a b c d e rest))
    (RoundTrace.rotlEntry q2 c (UInt256.ofNat 10) (UInt256.ofNat 0x185)
      (genericRot2Tail base j wordIndex rotation k returnDest word
        a b c d e rest))
    (RoundTrace.run_afterRot1 q base j wordIndex rotation k returnDest word
      a b c d e rest hstack hcode hrun)
    (by simpa [RoundTrace.rotlReturned] using hfork)
    (by simp [RoundTrace.afterRot1Path, CopyFree])
  have h5 := rotl_cost_potential q2 c (UInt256.ofNat 10) (UInt256.ofNat 0x185)
    (genericRot2Tail base j wordIndex rotation k returnDest word
      a b c d e rest)
    (by simp [genericRot2Tail]; omega) hcode2 hfork2 hrun2 hnp2
    (by
      exact Artifact.referenceArtifact.isValidJumpDest_index 281 (by rfl))
  have h6 := blockCost_potential RoundTrace.afterRot2Path
    (RoundTrace.rotlReturned q2 c (UInt256.ofNat 10) (UInt256.ofNat 0x185)
      (genericRot2Tail base j wordIndex rotation k returnDest word
        a b c d e rest))
    (TableTrace.setEntry q2 base (UInt256.ofNat 3)
      (rotlValue c (UInt256.ofNat 10)) (UInt256.ofNat 0x18d)
      (genericSetTail base j wordIndex rotation k returnDest word
        a b c d e rest))
    (RoundTrace.run_afterRot2 q2 base j wordIndex rotation k returnDest word
      a b c d e rest hstack hcode2 hrun2)
    (by simpa [RoundTrace.rotlReturned] using hfork2)
    (by simp [RoundTrace.afterRot2Path, CopyFree])
  have h7 := wordSet_cost_potential q2 base (UInt256.ofNat 3)
    (rotlValue c (UInt256.ofNat 10)) (UInt256.ofNat 0x18d)
    (genericSetTail base j wordIndex rotation k returnDest word
      a b c d e rest)
    (by simp [genericSetTail]; omega) hcode2 hfork2 hrun2 hnp2
    (by
      exact Artifact.referenceArtifact.isValidJumpDest_index 286 (by rfl))
  have h8 := blockCost_potential RoundTrace.suffixPath
    (TableTrace.setReturned q2 base (UInt256.ofNat 3)
      (rotlValue c (UInt256.ofNat 10)) (UInt256.ofNat 0x18d)
      (genericSetTail base j wordIndex rotation k returnDest word
        a b c d e rest))
    (genericReturned q2 base j word rotation k returnDest a b c d e rest)
    (RoundTrace.run_suffix q2 base j wordIndex rotation k returnDest word
      a b c d e rest hstack hcode2 hrun2 hvalid)
    (by simpa [TableTrace.setReturned, TableTrace.storedWord] using hfork2)
    (by simp [RoundTrace.suffixPath, CopyFree])
  have h01 := potential_trans _ _ _ _ _ _ _ h0 h1
  have h012 := potential_trans _ _ _ _ _ _ _ h01 h2
  have h0123 := potential_trans _ _ _ _ _ _ _ h012 h3
  have h01234 := potential_trans _ _ _ _ _ _ _ h0123 h4
  have h012345 := potential_trans _ _ _ _ _ _ _ h01234 h5
  have h0123456 := potential_trans _ _ _ _ _ _ _ h012345 h6
  have h01234567 := potential_trans _ _ _ _ _ _ _ h0123456 h7
  have hall := potential_trans _ _ _ _ _ _ _ h01234567 h8
  simpa [RoundTrace.gasSteps_roundBody, roundBodyWork, bodyEntry, q2,
    RoundTrace.gasSteps_rotl, BooleanFunctionTrace.gasSteps_fCase,
    TableTrace.gasSteps_wordSet, GasSteps.trans_cost, Nat.add_assoc] using hall

theorem round_cost_potential (s : State) (base : UInt256)
    (j : Nat) (hj : j < 5) (wordIndex rotation k returnDest : UInt256)
    (rest : List UInt256) (hstack : rest.length < 980)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hvalid : Decode.isValidJumpDest referenceBytecode returnDest.toNat = true) :
    (RoundTrace.gasSteps_round s base j hj wordIndex rotation k returnDest rest
      hstack hcode hfork hrun hnp hvalid).cost +
        MachineState.memCost s.activeWords.toNat =
      roundWork j + MachineState.memCost
        (RoundTrace.roundReturned s base j wordIndex rotation k returnDest rest).activeWords.toNat := by
  let q0 := afterLoads s base
  let q := xReturnedState s base j wordIndex rotation k returnDest rest
  have hcode0 : q0.executionEnv.code = referenceBytecode := by
    simpa [q0, afterLoads] using hcode
  have hfork0 : q0.fork = .Osaka := by simpa [q0, afterLoads] using hfork
  have hrun0 : q0.halt = .Running := by simpa [q0, afterLoads] using hrun
  have hnp0 : Precompile.isPrecompileWithConfig q0.executionEnv.precompileConfig q0.executionEnv.fork
      q0.executionEnv.codeAddr = false := by simpa [q0, afterLoads] using hnp
  have hcodeQ : q.executionEnv.code = referenceBytecode := by
    simpa [q, xReturnedState, TableTrace.atReturned, q0, afterLoads] using hcode
  have hforkQ : q.fork = .Osaka := by
    simpa [q, xReturnedState, TableTrace.atReturned, q0, afterLoads] using hfork
  have hrunQ : q.halt = .Running := by
    simpa [q, xReturnedState, TableTrace.atReturned, q0, afterLoads] using hrun
  have hnpQ : Precompile.isPrecompileWithConfig q.executionEnv.precompileConfig q.executionEnv.fork
      q.executionEnv.codeAddr = false := by
    simpa [q, xReturnedState, TableTrace.atReturned, q0, afterLoads] using hnp
  have h0 := blockCost_potential RoundTrace.prefixPath
    (RoundTrace.roundEntry s base j wordIndex rotation k returnDest rest)
    (RoundTrace.xCallState s base j wordIndex rotation k returnDest rest)
    (RoundTrace.run_prefix s base j wordIndex rotation k returnDest rest
      hstack hcode hrun)
    (by simpa [RoundTrace.roundEntry] using hfork)
    (by simp [RoundTrace.prefixPath, CopyFree])
  have h1 := xAt_cost_potential q0 wordIndex (UInt256.ofNat 0x13a)
    (roundTail s base j wordIndex rotation k returnDest rest)
    (by simp [roundTail]; omega) hcode0 hfork0 hrun0 hnp0
    (by
      exact Artifact.referenceArtifact.isValidJumpDest_index 234 (by rfl))
  have h2 := roundBody_cost_potential q base j hj wordIndex rotation k returnDest
    (RoundTrace.roundWord s base wordIndex) (RoundTrace.loadedA s base)
    (RoundTrace.loadedB s base) (RoundTrace.loadedC s base)
    (RoundTrace.loadedD s base) (RoundTrace.loadedE s base) rest hstack
    hcodeQ hforkQ hrunQ hnpQ hvalid
  have h01 := potential_trans _ _ _ _ _ _ _ h0 h1
  have hall := potential_trans _ _ _ _ _ _ _ h01 h2
  simpa [RoundTrace.gasSteps_round, RoundTrace.roundReturned, roundWork,
    RoundTrace.roundEntry, RoundTrace.xCallState, q0, q, xReturnedState,
    RoundTrace.gasSteps_roundBody, TableTrace.gasSteps_xAt,
    GasSteps.trans_cost, Nat.add_assoc] using hall

end Challenge.Ripemd160.Reference.Proofs.Bytecode.CompressionRoundCostTrace
