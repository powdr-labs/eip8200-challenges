import Challenge.Sha256.Submissions.Sha256Fast.Proofs.MemoryCorrect
import Challenge.EvmProof.FixedPathGas

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

namespace Challenge.Sha256.Submissions.Sha256Fast.Proofs.FeedForwardCorrect

open EvmSemantics EvmSemantics.EVM EvmSemantics.Crypto
open Challenge.EvmProof Challenge.EvmProof.Stepper Challenge.EvmProof.Word
open MemoryCorrect

def foldWrite (memory : ByteArray) (work saved : UInt32) (address : Nat) :
    ByteArray :=
  MachineState.writeBytes memory
    (Data.Bytes.natToBytesPadded (ofUInt32 (work + saved)).toNat 32) address

theorem readWord_foldWrite_later (memory : ByteArray) (work saved : UInt32)
    (write read : Nat) (h : write + 32 ≤ read) :
    MachineState.readWord (foldWrite memory work saved write) read =
      MachineState.readWord memory read := by
  unfold foldWrite
  apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
  rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  exact Or.inr h

private noncomputable def feed0Trace {s t : State}
    (hcode : s.executionEnv.code = Loop.bytes) (hfork : s.fork = .Osaka)
    (hresult : runLocatedBlock DriverBlocks.feedForward0Path s = some t)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (haw : s.activeWords = t.activeWords) : GasSteps s t :=
  Challenge.EvmProof.FixedPathGas.trace DriverBlocks.feedForward0Path 21
    (by rfl) (by rfl) (by simpa [Loop.art] using hcode) hfork hresult hrun hnp haw

private noncomputable def feed1Trace {s t : State}
    (hcode : s.executionEnv.code = Loop.bytes) (hfork : s.fork = .Osaka)
    (hresult : runLocatedBlock DriverBlocks.feedForward1Path s = some t)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (haw : s.activeWords = t.activeWords) : GasSteps s t :=
  Challenge.EvmProof.FixedPathGas.trace DriverBlocks.feedForward1Path 21
    (by rfl) (by rfl) (by simpa [Loop.art] using hcode) hfork hresult hrun hnp haw

private noncomputable def feed2Trace {s t : State}
    (hcode : s.executionEnv.code = Loop.bytes) (hfork : s.fork = .Osaka)
    (hresult : runLocatedBlock DriverBlocks.feedForward2Path s = some t)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (haw : s.activeWords = t.activeWords) : GasSteps s t :=
  Challenge.EvmProof.FixedPathGas.trace DriverBlocks.feedForward2Path 21
    (by rfl) (by rfl) (by simpa [Loop.art] using hcode) hfork hresult hrun hnp haw

private noncomputable def feed3Trace {s t : State}
    (hcode : s.executionEnv.code = Loop.bytes) (hfork : s.fork = .Osaka)
    (hresult : runLocatedBlock DriverBlocks.feedForward3Path s = some t)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (haw : s.activeWords = t.activeWords) : GasSteps s t :=
  Challenge.EvmProof.FixedPathGas.trace DriverBlocks.feedForward3Path 21
    (by rfl) (by rfl) (by simpa [Loop.art] using hcode) hfork hresult hrun hnp haw

private noncomputable def feed4Trace {s t : State}
    (hcode : s.executionEnv.code = Loop.bytes) (hfork : s.fork = .Osaka)
    (hresult : runLocatedBlock DriverBlocks.feedForward4Path s = some t)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (haw : s.activeWords = t.activeWords) : GasSteps s t :=
  Challenge.EvmProof.FixedPathGas.trace DriverBlocks.feedForward4Path 21
    (by rfl) (by rfl) (by simpa [Loop.art] using hcode) hfork hresult hrun hnp haw

private noncomputable def feed5Trace {s t : State}
    (hcode : s.executionEnv.code = Loop.bytes) (hfork : s.fork = .Osaka)
    (hresult : runLocatedBlock DriverBlocks.feedForward5Path s = some t)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (haw : s.activeWords = t.activeWords) : GasSteps s t :=
  Challenge.EvmProof.FixedPathGas.trace DriverBlocks.feedForward5Path 21
    (by rfl) (by rfl) (by simpa [Loop.art] using hcode) hfork hresult hrun hnp haw

private noncomputable def feed6Trace {s t : State}
    (hcode : s.executionEnv.code = Loop.bytes) (hfork : s.fork = .Osaka)
    (hresult : runLocatedBlock DriverBlocks.feedForward6Path s = some t)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (haw : s.activeWords = t.activeWords) : GasSteps s t :=
  Challenge.EvmProof.FixedPathGas.trace DriverBlocks.feedForward6Path 21
    (by rfl) (by rfl) (by simpa [Loop.art] using hcode) hfork hresult hrun hnp haw

private noncomputable def feed7Trace {s t : State}
    (hcode : s.executionEnv.code = Loop.bytes) (hfork : s.fork = .Osaka)
    (hresult : runLocatedBlock DriverBlocks.feedForward7Path s = some t)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (haw : s.activeWords = t.activeWords) : GasSteps s t :=
  Challenge.EvmProof.FixedPathGas.trace DriverBlocks.feedForward7Path 31
    (by rfl) (by rfl) (by simpa [Loop.art] using hcode) hfork hresult hrun hnp haw

/-- The eight generated feed-forward stores implement the reference
`H + working` update and return to the driver's continuation. -/
noncomputable def gasSteps_feedForward (s : State) (x : Ref.Working) (H : Array UInt32)
    (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 999) (haw : s.activeWords = UInt256.ofNat 140)
    (hcode : s.executionEnv.code = Loop.bytes) (hfork : s.fork = .Osaka)
    (hret : Decode.isValidJumpDest Loop.bytes returnDest.toNat = true)
    (hrun : s.halt = .Running) (hpc : s.pc = UInt256.ofNat 1696)
    (hstack : s.stack =
      [ofUInt32 x.a, ofUInt32 x.b, ofUInt32 x.c, ofUInt32 x.d,
       ofUInt32 x.e, ofUInt32 x.f, ofUInt32 x.g, ofUInt32 x.h,
       UInt256.ofNat 2048, returnDest] ++ rest)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hH : HashCorrect s.memory H) :
    GasSteps s
      { s with
        pc := returnDest
        activeWords := UInt256.ofNat 140
        memory := DriverBlocks.foldedMemory s.memory
          x.a x.b x.c x.d x.e x.f x.g x.h
          H[0]! H[1]! H[2]! H[3]! H[4]! H[5]! H[6]! H[7]!
        stack := rest } := by
  let m0 := s.memory
  let m1 := foldWrite m0 x.a H[0]! 32
  let m2 := foldWrite m1 x.b H[1]! 64
  let m3 := foldWrite m2 x.c H[2]! 96
  let m4 := foldWrite m3 x.d H[3]! 128
  let m5 := foldWrite m4 x.e H[4]! 160
  let m6 := foldWrite m5 x.f H[5]! 192
  let m7 := foldWrite m6 x.g H[6]! 224
  let m8 := foldWrite m7 x.h H[7]! 256
  let s1 : State := { s with
    pc := UInt256.ofNat 1709
    activeWords := UInt256.ofNat 140
    memory := m1
    stack := [ofUInt32 x.b, ofUInt32 x.c, ofUInt32 x.d, ofUInt32 x.e,
      ofUInt32 x.f, ofUInt32 x.g, ofUInt32 x.h,
      UInt256.ofNat 2048, returnDest] ++ rest }
  let s2 : State := { s with
    pc := UInt256.ofNat 1722
    activeWords := UInt256.ofNat 140
    memory := m2
    stack := [ofUInt32 x.c, ofUInt32 x.d, ofUInt32 x.e,
      ofUInt32 x.f, ofUInt32 x.g, ofUInt32 x.h,
      UInt256.ofNat 2048, returnDest] ++ rest }
  let s3 : State := { s with
    pc := UInt256.ofNat 1735
    activeWords := UInt256.ofNat 140
    memory := m3
    stack := [ofUInt32 x.d, ofUInt32 x.e, ofUInt32 x.f,
      ofUInt32 x.g, ofUInt32 x.h, UInt256.ofNat 2048, returnDest] ++ rest }
  let s4 : State := { s with
    pc := UInt256.ofNat 1748
    activeWords := UInt256.ofNat 140
    memory := m4
    stack := [ofUInt32 x.e, ofUInt32 x.f, ofUInt32 x.g,
      ofUInt32 x.h, UInt256.ofNat 2048, returnDest] ++ rest }
  let s5 : State := { s with
    pc := UInt256.ofNat 1761
    activeWords := UInt256.ofNat 140
    memory := m5
    stack := [ofUInt32 x.f, ofUInt32 x.g, ofUInt32 x.h,
      UInt256.ofNat 2048, returnDest] ++ rest }
  let s6 : State := { s with
    pc := UInt256.ofNat 1774
    activeWords := UInt256.ofNat 140
    memory := m6
    stack := [ofUInt32 x.g, ofUInt32 x.h,
      UInt256.ofNat 2048, returnDest] ++ rest }
  let s7 : State := { s with
    pc := UInt256.ofNat 1787
    activeWords := UInt256.ofNat 140
    memory := m7
    stack := [ofUInt32 x.h, UInt256.ofNat 2048, returnDest] ++ rest }
  let s8 : State := { s with
    pc := returnDest
    activeWords := UInt256.ofNat 140
    memory := m8
    stack := rest }
  have hh (i : Nat) (hi : i < 8) :
      MachineState.readWord m0 (32 + 32 * i) = ofUInt32 H[i]! := by
    simpa [m0, hValue, hOffset, Nat.mul_comm] using hH i hi
  have hh1 : MachineState.readWord m1 64 = ofUInt32 H[1]! := by
    rw [readWord_foldWrite_later]; exact hh 1 (by omega); omega
  have hh2 : MachineState.readWord m2 96 = ofUInt32 H[2]! := by
    rw [readWord_foldWrite_later, readWord_foldWrite_later]
    · exact hh 2 (by omega)
    all_goals omega
  have hh3 : MachineState.readWord m3 128 = ofUInt32 H[3]! := by
    rw [readWord_foldWrite_later, readWord_foldWrite_later,
      readWord_foldWrite_later]
    · exact hh 3 (by omega)
    all_goals omega
  have hh4 : MachineState.readWord m4 160 = ofUInt32 H[4]! := by
    rw [readWord_foldWrite_later, readWord_foldWrite_later,
      readWord_foldWrite_later, readWord_foldWrite_later]
    · exact hh 4 (by omega)
    all_goals omega
  have hh5 : MachineState.readWord m5 192 = ofUInt32 H[5]! := by
    rw [readWord_foldWrite_later, readWord_foldWrite_later,
      readWord_foldWrite_later, readWord_foldWrite_later,
      readWord_foldWrite_later]
    · exact hh 5 (by omega)
    all_goals omega
  have hh6 : MachineState.readWord m6 224 = ofUInt32 H[6]! := by
    rw [readWord_foldWrite_later, readWord_foldWrite_later,
      readWord_foldWrite_later, readWord_foldWrite_later,
      readWord_foldWrite_later, readWord_foldWrite_later]
    · exact hh 6 (by omega)
    all_goals omega
  have hh7 : MachineState.readWord m7 256 = ofUInt32 H[7]! := by
    rw [readWord_foldWrite_later, readWord_foldWrite_later,
      readWord_foldWrite_later, readWord_foldWrite_later,
      readWord_foldWrite_later, readWord_foldWrite_later,
      readWord_foldWrite_later]
    · exact hh 7 (by omega)
    all_goals omega
  have r0 := DriverBlocks.run_feedForward0 s x.a H[0]! returnDest rest
    (by omega) haw hrun hpc hstack (hh 0 (by omega))
  have r1 := DriverBlocks.run_feedForward1 s1 x.b H[1]! returnDest rest
    (by omega) (by simp [s1]) (by simpa [s1] using hrun) rfl rfl hh1
  have r2 := DriverBlocks.run_feedForward2 s2 x.c H[2]! returnDest rest
    (by omega) (by simp [s2]) (by simpa [s2] using hrun) rfl rfl hh2
  have r3 := DriverBlocks.run_feedForward3 s3 x.d H[3]! returnDest rest
    (by omega) (by simp [s3]) (by simpa [s3] using hrun) rfl rfl hh3
  have r4 := DriverBlocks.run_feedForward4 s4 x.e H[4]! returnDest rest
    (by omega) (by simp [s4]) (by simpa [s4] using hrun) rfl rfl hh4
  have r5 := DriverBlocks.run_feedForward5 s5 x.f H[5]! returnDest rest
    (by omega) (by simp [s5]) (by simpa [s5] using hrun) rfl rfl hh5
  have r6 := DriverBlocks.run_feedForward6 s6 x.g H[6]! returnDest rest
    (by omega) (by simp [s6]) (by simpa [s6] using hrun) rfl rfl hh6
  have r7 := DriverBlocks.run_feedForward7 s7 x.h H[7]! returnDest rest
    hcap (by simp [s7]) (by simpa [s7] using hcode) hret
    (by simpa [s7] using hrun) rfl rfl hh7
  have codeAt (u : State) (hu : u.executionEnv = s.executionEnv) :
      u.executionEnv.code = Loop.bytes := by rw [hu, hcode]
  have forkAt (u : State) (hu : u.executionEnv = s.executionEnv) :
      u.fork = .Osaka := by change u.executionEnv.fork = .Osaka; rw [hu]; exact hfork
  have runAt (u : State) (hu : u.halt = s.halt) : u.halt = .Running := by
    rw [hu, hrun]
  have npAt (u : State) (hu : u.executionEnv = s.executionEnv) :
      Precompile.isPrecompileWithConfig u.executionEnv.precompileConfig
        u.executionEnv.fork u.executionEnv.codeAddr = false := by rw [hu]; exact hnp
  let g0 : GasSteps s s1 :=
    feed0Trace hcode hfork (by simpa [s1, m1, m0, foldWrite] using r0)
      hrun hnp (by simp [s1, haw])
  let g1 : GasSteps s1 s2 :=
    feed1Trace
    (codeAt s1 (by rfl)) (forkAt s1 (by rfl))
    (by simpa [s1, s2, m2, foldWrite] using r1)
    (runAt s1 (by rfl)) (npAt s1 (by rfl)) (by simp [s1, s2])
  let g2 : GasSteps s2 s3 :=
    feed2Trace
    (codeAt s2 (by rfl)) (forkAt s2 (by rfl))
    (by simpa [s2, s3, m3, foldWrite] using r2)
    (runAt s2 (by rfl)) (npAt s2 (by rfl)) (by simp [s2, s3])
  let g3 : GasSteps s3 s4 :=
    feed3Trace
    (codeAt s3 (by rfl)) (forkAt s3 (by rfl))
    (by simpa [s3, s4, m4, foldWrite] using r3)
    (runAt s3 (by rfl)) (npAt s3 (by rfl)) (by simp [s3, s4])
  let g4 : GasSteps s4 s5 :=
    feed4Trace
    (codeAt s4 (by rfl)) (forkAt s4 (by rfl))
    (by simpa [s4, s5, m5, foldWrite] using r4)
    (runAt s4 (by rfl)) (npAt s4 (by rfl)) (by simp [s4, s5])
  let g5 : GasSteps s5 s6 :=
    feed5Trace
    (codeAt s5 (by rfl)) (forkAt s5 (by rfl))
    (by simpa [s5, s6, m6, foldWrite] using r5)
    (runAt s5 (by rfl)) (npAt s5 (by rfl)) (by simp [s5, s6])
  let g6 : GasSteps s6 s7 :=
    feed6Trace
    (codeAt s6 (by rfl)) (forkAt s6 (by rfl))
    (by simpa [s6, s7, m7, foldWrite] using r6)
    (runAt s6 (by rfl)) (npAt s6 (by rfl)) (by simp [s6, s7])
  let g7 : GasSteps s7 s8 :=
    feed7Trace
    (codeAt s7 (by rfl)) (forkAt s7 (by rfl))
    (by simpa [s7, s8, m8, foldWrite] using r7)
    (runAt s7 (by rfl)) (npAt s7 (by rfl)) (by simp [s7, s8])
  have hm8 : m8 = DriverBlocks.foldedMemory s.memory
      x.a x.b x.c x.d x.e x.f x.g x.h
      H[0]! H[1]! H[2]! H[3]! H[4]! H[5]! H[6]! H[7]! := by
    rfl
  let right := GasSteps.transKnown g6 g7 21 31 rfl rfl
  let right := GasSteps.transKnown g5 right 21 52 rfl rfl
  let right := GasSteps.transKnown g4 right 21 73 rfl rfl
  let right := GasSteps.transKnown g3 right 21 94 rfl rfl
  let right := GasSteps.transKnown g2 right 21 115 rfl rfl
  let right := GasSteps.transKnown g1 right 21 136 rfl rfl
  let trace := GasSteps.transKnown g0 right 21 157 rfl rfl
  exact GasSteps.cast trace rfl (by simp [s8, hm8])

@[simp] theorem gasSteps_feedForward_cost (s : State) (x : Ref.Working)
    (H : Array UInt32) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 999) (haw : s.activeWords = UInt256.ofNat 140)
    (hcode : s.executionEnv.code = Loop.bytes) (hfork : s.fork = .Osaka)
    (hret : Decode.isValidJumpDest Loop.bytes returnDest.toNat = true)
    (hrun : s.halt = .Running) (hpc : s.pc = UInt256.ofNat 1696)
    (hstack : s.stack =
      [ofUInt32 x.a, ofUInt32 x.b, ofUInt32 x.c, ofUInt32 x.d,
       ofUInt32 x.e, ofUInt32 x.f, ofUInt32 x.g, ofUInt32 x.h,
       UInt256.ofNat 2048, returnDest] ++ rest)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hH : HashCorrect s.memory H) :
    (gasSteps_feedForward s x H returnDest rest hcap haw hcode hfork hret hrun
      hpc hstack hnp hH).cost = 178 := rfl

end Challenge.Sha256.Submissions.Sha256Fast.Proofs.FeedForwardCorrect
