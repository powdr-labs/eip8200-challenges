import Challenge.Sha256.Submissions.Sha256Fast.Proofs.MemoryCorrect
import Challenge.EvmProof.FixedPathGas

set_option warningAsError false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

namespace Challenge.Sha256.Submissions.Sha256Fast.Proofs.RoundCorrect

open EvmSemantics EvmSemantics.EVM EvmSemantics.Crypto
open Challenge.EvmProof Challenge.EvmProof.Word Challenge.EvmProof.Stepper
open Challenge.Sha256.Fast
open MemoryCorrect

noncomputable section

def phaseStack (x : Ref.Working) (phase : Nat) : List UInt256 :=
  match phase with
  | 0 => [ofUInt32 x.a, ofUInt32 x.b, ofUInt32 x.c, ofUInt32 x.d,
      ofUInt32 x.e, ofUInt32 x.f, ofUInt32 x.g, ofUInt32 x.h]
  | 1 => [ofUInt32 x.b, ofUInt32 x.c, ofUInt32 x.d, ofUInt32 x.e,
      ofUInt32 x.f, ofUInt32 x.g, ofUInt32 x.h, ofUInt32 x.a]
  | 2 => [ofUInt32 x.c, ofUInt32 x.d, ofUInt32 x.e, ofUInt32 x.f,
      ofUInt32 x.g, ofUInt32 x.h, ofUInt32 x.a, ofUInt32 x.b]
  | 3 => [ofUInt32 x.d, ofUInt32 x.e, ofUInt32 x.f, ofUInt32 x.g,
      ofUInt32 x.h, ofUInt32 x.a, ofUInt32 x.b, ofUInt32 x.c]
  | 4 => [ofUInt32 x.e, ofUInt32 x.f, ofUInt32 x.g, ofUInt32 x.h,
      ofUInt32 x.a, ofUInt32 x.b, ofUInt32 x.c, ofUInt32 x.d]
  | 5 => [ofUInt32 x.f, ofUInt32 x.g, ofUInt32 x.h, ofUInt32 x.a,
      ofUInt32 x.b, ofUInt32 x.c, ofUInt32 x.d, ofUInt32 x.e]
  | 6 => [ofUInt32 x.g, ofUInt32 x.h, ofUInt32 x.a, ofUInt32 x.b,
      ofUInt32 x.c, ofUInt32 x.d, ofUInt32 x.e, ofUInt32 x.f]
  | 7 => [ofUInt32 x.h, ofUInt32 x.a, ofUInt32 x.b, ofUInt32 x.c,
      ofUInt32 x.d, ofUInt32 x.e, ofUInt32 x.f, ofUInt32 x.g]
  | _ => [ofUInt32 x.a, ofUInt32 x.b, ofUInt32 x.c, ofUInt32 x.d,
      ofUInt32 x.e, ofUInt32 x.f, ofUInt32 x.g, ofUInt32 x.h]

def roundState (s : State) (x : Ref.Working) (phase pc : Nat)
    (q : UInt256) (tail : List UInt256) : State :=
  { s with
    pc := UInt256.ofNat pc
    activeWords := UInt256.ofNat 140
    stack := phaseStack x phase ++ q :: tail }

private theorem groupAddress (g base : Nat) (hg : g < 8)
    (hbase : base ≤ 2656) :
    (UInt256.ofNat base + UInt256.ofNat (256 * g)).toNat = base + 256 * g := by
  rw [word_toNat_add, word_toNat_ofNat, word_toNat_ofNat,
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega)]

private theorem indexedAddress (base i g : Nat) :
    base + (8 * g + i) * 32 = base + i * 32 + g * 256 := by
  omega

private theorem round0_eval (s : State) (x : Ref.Working) (k w : UInt32)
    (g : Nat) (tail : List UInt256) (hg : g < 8)
    (hcap : tail.length < 990)
    (hrun : s.halt = .Running)
    (hk : MemoryCorrect.kValue s.memory (8 * g) = ofUInt32 k)
    (hw : ScheduleCorrect.wValue s.memory (8 * g) = dbl (ofUInt32 w)) :
    runLocatedBlock Loop.pround0
        (roundState s x 0 912 (UInt256.ofNat (256 * g)) tail) =
      some (roundState s (Ref.round x k w) 1 1008
        (UInt256.ofNat (256 * g)) tail) := by
  simp only [MemoryCorrect.kValue, MemoryCorrect.kOffset,
    ScheduleCorrect.wValue, ScheduleCorrect.wOffset] at hk hw
  rw [show 2432 + 8 * g * 32 = 2432 + g * 256 by omega] at hk
  rw [show 384 + 8 * g * 32 = 384 + g * 256 by omega] at hw
  apply Loop.round0
  case hk => rw [groupAddress g 2432 hg (by omega), Nat.mul_comm 256 g]; exact hk
  case hw => rw [groupAddress g 384 hg (by omega), Nat.mul_comm 256 g]; exact hw
  all_goals try simp [roundState, phaseStack, MemoryCorrect.kValue,
    MemoryCorrect.kOffset, ScheduleCorrect.wValue, ScheduleCorrect.wOffset,
    groupAddress, hg,
    Challenge.Sha256.Reference.Proofs.Bytecode.CompressionCorrect.round,
    Loop.T1, Loop.T2] at ⊢
  all_goals
    first
    | solve | convert hk using 1 <;> omega
    | solve | convert hw using 1 <;> omega
    | exact hrun
    | exact hk
    | exact hw
    | omega
    | rfl
    | ac_rfl

private theorem round1_eval (s : State) (x : Ref.Working) (k w : UInt32)
    (g : Nat) (tail : List UInt256) (hg : g < 8)
    (hcap : tail.length < 990)
    (hrun : s.halt = .Running)
    (hk : MemoryCorrect.kValue s.memory (8 * g + 1) = ofUInt32 k)
    (hw : ScheduleCorrect.wValue s.memory (8 * g + 1) = dbl (ofUInt32 w)) :
    runLocatedBlock Loop.pround1
        (roundState s x 1 1008 (UInt256.ofNat (256 * g)) tail) =
      some (roundState s (Ref.round x k w) 2 1104
        (UInt256.ofNat (256 * g)) tail) := by
  simp only [MemoryCorrect.kValue, MemoryCorrect.kOffset,
    ScheduleCorrect.wValue, ScheduleCorrect.wOffset] at hk hw
  rw [indexedAddress 2432 1 g] at hk
  rw [indexedAddress 384 1 g] at hw
  apply Loop.round1
  case hk => rw [groupAddress g 2464 hg (by omega), Nat.mul_comm 256 g]; exact hk
  case hw => rw [groupAddress g 416 hg (by omega), Nat.mul_comm 256 g]; exact hw
  all_goals try simp [roundState, phaseStack, MemoryCorrect.kValue,
    MemoryCorrect.kOffset, ScheduleCorrect.wValue, ScheduleCorrect.wOffset,
    groupAddress, hg,
    Challenge.Sha256.Reference.Proofs.Bytecode.CompressionCorrect.round,
    Loop.T1, Loop.T2] at ⊢
  all_goals
    first
    | solve | convert hk using 1 <;> omega
    | solve | convert hw using 1 <;> omega
    | exact hrun
    | exact hk
    | exact hw
    | omega
    | rfl
    | ac_rfl

private theorem round2_eval (s : State) (x : Ref.Working) (k w : UInt32)
    (g : Nat) (tail : List UInt256) (hg : g < 8)
    (hcap : tail.length < 990)
    (hrun : s.halt = .Running)
    (hk : MemoryCorrect.kValue s.memory (8 * g + 2) = ofUInt32 k)
    (hw : ScheduleCorrect.wValue s.memory (8 * g + 2) = dbl (ofUInt32 w)) :
    runLocatedBlock Loop.pround2
        (roundState s x 2 1104 (UInt256.ofNat (256 * g)) tail) =
      some (roundState s (Ref.round x k w) 3 1200
        (UInt256.ofNat (256 * g)) tail) := by
  simp only [MemoryCorrect.kValue, MemoryCorrect.kOffset,
    ScheduleCorrect.wValue, ScheduleCorrect.wOffset] at hk hw
  rw [indexedAddress 2432 2 g] at hk
  rw [indexedAddress 384 2 g] at hw
  apply Loop.round2
  case hk => rw [groupAddress g 2496 hg (by omega), Nat.mul_comm 256 g]; exact hk
  case hw => rw [groupAddress g 448 hg (by omega), Nat.mul_comm 256 g]; exact hw
  all_goals try simp [roundState, phaseStack, MemoryCorrect.kValue,
    MemoryCorrect.kOffset, ScheduleCorrect.wValue, ScheduleCorrect.wOffset,
    groupAddress, hg,
    Challenge.Sha256.Reference.Proofs.Bytecode.CompressionCorrect.round,
    Loop.T1, Loop.T2] at ⊢
  all_goals
    first
    | solve | convert hk using 1 <;> omega
    | solve | convert hw using 1 <;> omega
    | exact hrun
    | exact hk
    | exact hw
    | omega
    | rfl
    | ac_rfl

private theorem round3_eval (s : State) (x : Ref.Working) (k w : UInt32)
    (g : Nat) (tail : List UInt256) (hg : g < 8)
    (hcap : tail.length < 990)
    (hrun : s.halt = .Running)
    (hk : MemoryCorrect.kValue s.memory (8 * g + 3) = ofUInt32 k)
    (hw : ScheduleCorrect.wValue s.memory (8 * g + 3) = dbl (ofUInt32 w)) :
    runLocatedBlock Loop.pround3
        (roundState s x 3 1200 (UInt256.ofNat (256 * g)) tail) =
      some (roundState s (Ref.round x k w) 4 1296
        (UInt256.ofNat (256 * g)) tail) := by
  simp only [MemoryCorrect.kValue, MemoryCorrect.kOffset,
    ScheduleCorrect.wValue, ScheduleCorrect.wOffset] at hk hw
  rw [indexedAddress 2432 3 g] at hk
  rw [indexedAddress 384 3 g] at hw
  apply Loop.round3
  case hk => rw [groupAddress g 2528 hg (by omega), Nat.mul_comm 256 g]; exact hk
  case hw => rw [groupAddress g 480 hg (by omega), Nat.mul_comm 256 g]; exact hw
  all_goals try simp [roundState, phaseStack, MemoryCorrect.kValue,
    MemoryCorrect.kOffset, ScheduleCorrect.wValue, ScheduleCorrect.wOffset,
    groupAddress, hg,
    Challenge.Sha256.Reference.Proofs.Bytecode.CompressionCorrect.round,
    Loop.T1, Loop.T2] at ⊢
  all_goals
    first
    | solve | convert hk using 1 <;> omega
    | solve | convert hw using 1 <;> omega
    | exact hrun
    | exact hk
    | exact hw
    | omega
    | rfl
    | ac_rfl

private theorem round4_eval (s : State) (x : Ref.Working) (k w : UInt32)
    (g : Nat) (tail : List UInt256) (hg : g < 8)
    (hcap : tail.length < 990)
    (hrun : s.halt = .Running)
    (hk : MemoryCorrect.kValue s.memory (8 * g + 4) = ofUInt32 k)
    (hw : ScheduleCorrect.wValue s.memory (8 * g + 4) = dbl (ofUInt32 w)) :
    runLocatedBlock Loop.pround4
        (roundState s x 4 1296 (UInt256.ofNat (256 * g)) tail) =
      some (roundState s (Ref.round x k w) 5 1392
        (UInt256.ofNat (256 * g)) tail) := by
  simp only [MemoryCorrect.kValue, MemoryCorrect.kOffset,
    ScheduleCorrect.wValue, ScheduleCorrect.wOffset] at hk hw
  rw [indexedAddress 2432 4 g] at hk
  rw [indexedAddress 384 4 g] at hw
  apply Loop.round4
  case hk => rw [groupAddress g 2560 hg (by omega), Nat.mul_comm 256 g]; exact hk
  case hw => rw [groupAddress g 512 hg (by omega), Nat.mul_comm 256 g]; exact hw
  all_goals try simp [roundState, phaseStack, MemoryCorrect.kValue,
    MemoryCorrect.kOffset, ScheduleCorrect.wValue, ScheduleCorrect.wOffset,
    groupAddress, hg,
    Challenge.Sha256.Reference.Proofs.Bytecode.CompressionCorrect.round,
    Loop.T1, Loop.T2] at ⊢
  all_goals
    first
    | solve | convert hk using 1 <;> omega
    | solve | convert hw using 1 <;> omega
    | exact hrun
    | exact hk
    | exact hw
    | omega
    | rfl
    | ac_rfl

private theorem round5_eval (s : State) (x : Ref.Working) (k w : UInt32)
    (g : Nat) (tail : List UInt256) (hg : g < 8)
    (hcap : tail.length < 990)
    (hrun : s.halt = .Running)
    (hk : MemoryCorrect.kValue s.memory (8 * g + 5) = ofUInt32 k)
    (hw : ScheduleCorrect.wValue s.memory (8 * g + 5) = dbl (ofUInt32 w)) :
    runLocatedBlock Loop.pround5
        (roundState s x 5 1392 (UInt256.ofNat (256 * g)) tail) =
      some (roundState s (Ref.round x k w) 6 1488
        (UInt256.ofNat (256 * g)) tail) := by
  simp only [MemoryCorrect.kValue, MemoryCorrect.kOffset,
    ScheduleCorrect.wValue, ScheduleCorrect.wOffset] at hk hw
  rw [indexedAddress 2432 5 g] at hk
  rw [indexedAddress 384 5 g] at hw
  apply Loop.round5
  case hk => rw [groupAddress g 2592 hg (by omega), Nat.mul_comm 256 g]; exact hk
  case hw => rw [groupAddress g 544 hg (by omega), Nat.mul_comm 256 g]; exact hw
  all_goals try simp [roundState, phaseStack, MemoryCorrect.kValue,
    MemoryCorrect.kOffset, ScheduleCorrect.wValue, ScheduleCorrect.wOffset,
    groupAddress, hg,
    Challenge.Sha256.Reference.Proofs.Bytecode.CompressionCorrect.round,
    Loop.T1, Loop.T2] at ⊢
  all_goals
    first
    | solve | convert hk using 1 <;> omega
    | solve | convert hw using 1 <;> omega
    | exact hrun
    | exact hk
    | exact hw
    | omega
    | rfl
    | ac_rfl

private theorem round6_eval (s : State) (x : Ref.Working) (k w : UInt32)
    (g : Nat) (tail : List UInt256) (hg : g < 8)
    (hcap : tail.length < 990)
    (hrun : s.halt = .Running)
    (hk : MemoryCorrect.kValue s.memory (8 * g + 6) = ofUInt32 k)
    (hw : ScheduleCorrect.wValue s.memory (8 * g + 6) = dbl (ofUInt32 w)) :
    runLocatedBlock Loop.pround6
        (roundState s x 6 1488 (UInt256.ofNat (256 * g)) tail) =
      some (roundState s (Ref.round x k w) 7 1584
        (UInt256.ofNat (256 * g)) tail) := by
  simp only [MemoryCorrect.kValue, MemoryCorrect.kOffset,
    ScheduleCorrect.wValue, ScheduleCorrect.wOffset] at hk hw
  rw [indexedAddress 2432 6 g] at hk
  rw [indexedAddress 384 6 g] at hw
  apply Loop.round6
  case hk => rw [groupAddress g 2624 hg (by omega), Nat.mul_comm 256 g]; exact hk
  case hw => rw [groupAddress g 576 hg (by omega), Nat.mul_comm 256 g]; exact hw
  all_goals try simp [roundState, phaseStack, MemoryCorrect.kValue,
    MemoryCorrect.kOffset, ScheduleCorrect.wValue, ScheduleCorrect.wOffset,
    groupAddress, hg,
    Challenge.Sha256.Reference.Proofs.Bytecode.CompressionCorrect.round,
    Loop.T1, Loop.T2] at ⊢
  all_goals
    first
    | solve | convert hk using 1 <;> omega
    | solve | convert hw using 1 <;> omega
    | exact hrun
    | exact hk
    | exact hw
    | omega
    | rfl
    | ac_rfl

private theorem round7_eval (s : State) (x : Ref.Working) (k w : UInt32)
    (g : Nat) (tail : List UInt256) (hg : g < 8)
    (hcap : tail.length < 990)
    (hrun : s.halt = .Running)
    (hk : MemoryCorrect.kValue s.memory (8 * g + 7) = ofUInt32 k)
    (hw : ScheduleCorrect.wValue s.memory (8 * g + 7) = dbl (ofUInt32 w)) :
    runLocatedBlock Loop.pround7
        (roundState s x 7 1584 (UInt256.ofNat (256 * g)) tail) =
      some (roundState s (Ref.round x k w) 8 1680
        (UInt256.ofNat (256 * g)) tail) := by
  simp only [MemoryCorrect.kValue, MemoryCorrect.kOffset,
    ScheduleCorrect.wValue, ScheduleCorrect.wOffset] at hk hw
  rw [indexedAddress 2432 7 g] at hk
  rw [indexedAddress 384 7 g] at hw
  apply Loop.round7
  case hk => rw [groupAddress g 2656 hg (by omega), Nat.mul_comm 256 g]; exact hk
  case hw => rw [groupAddress g 608 hg (by omega), Nat.mul_comm 256 g]; exact hw
  all_goals try simp [roundState, phaseStack, MemoryCorrect.kValue,
    MemoryCorrect.kOffset, ScheduleCorrect.wValue, ScheduleCorrect.wOffset,
    groupAddress, hg,
    Challenge.Sha256.Reference.Proofs.Bytecode.CompressionCorrect.round,
    Loop.T1, Loop.T2] at ⊢
  all_goals
    first
    | solve | convert hk using 1 <;> omega
    | solve | convert hw using 1 <;> omega
    | exact hrun
    | exact hk
    | exact hw
    | omega
    | rfl
    | ac_rfl

/-- Apply `count` reference rounds beginning at schedule index `base`. -/
def roundsFrom (x : Ref.Working) (padded : ByteArray) (blockOff base : Nat) :
    Nat → Ref.Working
  | 0 => x
  | count + 1 =>
      Ref.round (roundsFrom x padded blockOff base count)
        Sha256.K[base + count]!
        (ScheduleCorrect.scheduleWord padded blockOff (base + count))

theorem roundsFrom_rounds (initial : Ref.Working) (padded : ByteArray)
    (blockOff base count : Nat) :
    roundsFrom (Ref.rounds initial padded blockOff base)
        padded blockOff base count =
      Ref.rounds initial padded blockOff (base + count) := by
  induction count with
  | zero => simp [roundsFrom]
  | succ count ih =>
      rw [roundsFrom, ih]
      change Challenge.Sha256.Reference.Proofs.Bytecode.CompressionCorrect.round
          (Challenge.Sha256.Reference.Proofs.Bytecode.CompressionCorrect.rounds
            initial padded blockOff (base + count))
          Sha256.K[base + count]!
          (ScheduleCorrect.scheduleWord padded blockOff (base + count)) =
        Challenge.Sha256.Reference.Proofs.Bytecode.CompressionCorrect.rounds
          initial padded blockOff ((base + count) + 1)
      rw [Challenge.Sha256.Reference.Proofs.Bytecode.CompressionCorrect.rounds]

private noncomputable def round0Trace {s t : State}
    (hcode : s.executionEnv.code = Loop.bytes) (hfork : s.fork = .Osaka)
    (hresult : runLocatedBlock Loop.pround0 s = some t)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (haw : s.activeWords = t.activeWords) : GasSteps s t :=
  Challenge.EvmProof.FixedPathGas.trace Loop.pround0 206 (by rfl) (by rfl)
    (by simpa [Loop.art] using hcode) hfork hresult hrun hnp haw

private noncomputable def round1Trace {s t : State}
    (hcode : s.executionEnv.code = Loop.bytes) (hfork : s.fork = .Osaka)
    (hresult : runLocatedBlock Loop.pround1 s = some t)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (haw : s.activeWords = t.activeWords) : GasSteps s t :=
  Challenge.EvmProof.FixedPathGas.trace Loop.pround1 206 (by rfl) (by rfl)
    (by simpa [Loop.art] using hcode) hfork hresult hrun hnp haw

private noncomputable def round2Trace {s t : State}
    (hcode : s.executionEnv.code = Loop.bytes) (hfork : s.fork = .Osaka)
    (hresult : runLocatedBlock Loop.pround2 s = some t)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (haw : s.activeWords = t.activeWords) : GasSteps s t :=
  Challenge.EvmProof.FixedPathGas.trace Loop.pround2 206 (by rfl) (by rfl)
    (by simpa [Loop.art] using hcode) hfork hresult hrun hnp haw

private noncomputable def round3Trace {s t : State}
    (hcode : s.executionEnv.code = Loop.bytes) (hfork : s.fork = .Osaka)
    (hresult : runLocatedBlock Loop.pround3 s = some t)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (haw : s.activeWords = t.activeWords) : GasSteps s t :=
  Challenge.EvmProof.FixedPathGas.trace Loop.pround3 206 (by rfl) (by rfl)
    (by simpa [Loop.art] using hcode) hfork hresult hrun hnp haw

private noncomputable def round4Trace {s t : State}
    (hcode : s.executionEnv.code = Loop.bytes) (hfork : s.fork = .Osaka)
    (hresult : runLocatedBlock Loop.pround4 s = some t)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (haw : s.activeWords = t.activeWords) : GasSteps s t :=
  Challenge.EvmProof.FixedPathGas.trace Loop.pround4 206 (by rfl) (by rfl)
    (by simpa [Loop.art] using hcode) hfork hresult hrun hnp haw

private noncomputable def round5Trace {s t : State}
    (hcode : s.executionEnv.code = Loop.bytes) (hfork : s.fork = .Osaka)
    (hresult : runLocatedBlock Loop.pround5 s = some t)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (haw : s.activeWords = t.activeWords) : GasSteps s t :=
  Challenge.EvmProof.FixedPathGas.trace Loop.pround5 206 (by rfl) (by rfl)
    (by simpa [Loop.art] using hcode) hfork hresult hrun hnp haw

private noncomputable def round6Trace {s t : State}
    (hcode : s.executionEnv.code = Loop.bytes) (hfork : s.fork = .Osaka)
    (hresult : runLocatedBlock Loop.pround6 s = some t)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (haw : s.activeWords = t.activeWords) : GasSteps s t :=
  Challenge.EvmProof.FixedPathGas.trace Loop.pround6 206 (by rfl) (by rfl)
    (by simpa [Loop.art] using hcode) hfork hresult hrun hnp haw

private noncomputable def round7Trace {s t : State}
    (hcode : s.executionEnv.code = Loop.bytes) (hfork : s.fork = .Osaka)
    (hresult : runLocatedBlock Loop.pround7 s = some t)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (haw : s.activeWords = t.activeWords) : GasSteps s t :=
  Challenge.EvmProof.FixedPathGas.trace Loop.pround7 206 (by rfl) (by rfl)
    (by simpa [Loop.art] using hcode) hfork hresult hrun hnp haw

/-- One complete eight-round straight-line group, before its loop-control
tail.  This is the reusable unit for the 64-round proof. -/
def gasSteps_groupRounds (s : State) (x : Ref.Working)
    (padded : ByteArray) (blockOff g : Nat) (tail : List UInt256)
    (hg : g < 8) (hcap : tail.length < 990)
    (hcode : s.executionEnv.code = Loop.bytes) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hK : ConstantsCorrect s.memory)
    (hW : ScheduleCorrect.WCorrect s.memory padded blockOff 64) :
    GasSteps
      (roundState s x 0 912 (UInt256.ofNat (256 * g)) tail)
      (roundState s (roundsFrom x padded blockOff (8 * g) 8) 8 1680
        (UInt256.ofNat (256 * g)) tail) := by
  let x0 := x
  let x1 := roundsFrom x padded blockOff (8 * g) 1
  let x2 := roundsFrom x padded blockOff (8 * g) 2
  let x3 := roundsFrom x padded blockOff (8 * g) 3
  let x4 := roundsFrom x padded blockOff (8 * g) 4
  let x5 := roundsFrom x padded blockOff (8 * g) 5
  let x6 := roundsFrom x padded blockOff (8 * g) 6
  let x7 := roundsFrom x padded blockOff (8 * g) 7
  let x8 := roundsFrom x padded blockOff (8 * g) 8
  let q := UInt256.ofNat (256 * g)
  have step0 : runLocatedBlock Loop.pround0 (roundState s x0 0 912 q tail) =
      some (roundState s x1 1 1008 q tail) := by
    simpa [x0, x1, q, roundsFrom] using round0_eval s x
      Sha256.K[8 * g]!
      (ScheduleCorrect.scheduleWord padded blockOff (8 * g)) g tail hg hcap
      hrun
      (hK (8 * g) (by omega)) (hW (8 * g) (by omega))
  have step1 : runLocatedBlock Loop.pround1 (roundState s x1 1 1008 q tail) =
      some (roundState s x2 2 1104 q tail) := by
    simpa [x1, x2, q, roundsFrom] using round1_eval s x1
      Sha256.K[8 * g + 1]!
      (ScheduleCorrect.scheduleWord padded blockOff (8 * g + 1)) g tail hg hcap
      hrun
      (hK (8 * g + 1) (by omega)) (hW (8 * g + 1) (by omega))
  have step2 : runLocatedBlock Loop.pround2 (roundState s x2 2 1104 q tail) =
      some (roundState s x3 3 1200 q tail) := by
    simpa [x2, x3, q, roundsFrom] using round2_eval s x2
      Sha256.K[8 * g + 2]!
      (ScheduleCorrect.scheduleWord padded blockOff (8 * g + 2)) g tail hg hcap
      hrun
      (hK (8 * g + 2) (by omega)) (hW (8 * g + 2) (by omega))
  have step3 : runLocatedBlock Loop.pround3 (roundState s x3 3 1200 q tail) =
      some (roundState s x4 4 1296 q tail) := by
    simpa [x3, x4, q, roundsFrom] using round3_eval s x3
      Sha256.K[8 * g + 3]!
      (ScheduleCorrect.scheduleWord padded blockOff (8 * g + 3)) g tail hg hcap
      hrun
      (hK (8 * g + 3) (by omega)) (hW (8 * g + 3) (by omega))
  have step4 : runLocatedBlock Loop.pround4 (roundState s x4 4 1296 q tail) =
      some (roundState s x5 5 1392 q tail) := by
    simpa [x4, x5, q, roundsFrom] using round4_eval s x4
      Sha256.K[8 * g + 4]!
      (ScheduleCorrect.scheduleWord padded blockOff (8 * g + 4)) g tail hg hcap
      hrun
      (hK (8 * g + 4) (by omega)) (hW (8 * g + 4) (by omega))
  have step5 : runLocatedBlock Loop.pround5 (roundState s x5 5 1392 q tail) =
      some (roundState s x6 6 1488 q tail) := by
    simpa [x5, x6, q, roundsFrom] using round5_eval s x5
      Sha256.K[8 * g + 5]!
      (ScheduleCorrect.scheduleWord padded blockOff (8 * g + 5)) g tail hg hcap
      hrun
      (hK (8 * g + 5) (by omega)) (hW (8 * g + 5) (by omega))
  have step6 : runLocatedBlock Loop.pround6 (roundState s x6 6 1488 q tail) =
      some (roundState s x7 7 1584 q tail) := by
    simpa [x6, x7, q, roundsFrom] using round6_eval s x6
      Sha256.K[8 * g + 6]!
      (ScheduleCorrect.scheduleWord padded blockOff (8 * g + 6)) g tail hg hcap
      hrun
      (hK (8 * g + 6) (by omega)) (hW (8 * g + 6) (by omega))
  have step7 : runLocatedBlock Loop.pround7 (roundState s x7 7 1584 q tail) =
      some (roundState s x8 8 1680 q tail) := by
    simpa [x7, x8, q, roundsFrom] using round7_eval s x7
      Sha256.K[8 * g + 7]!
      (ScheduleCorrect.scheduleWord padded blockOff (8 * g + 7)) g tail hg hcap
      hrun
      (hK (8 * g + 7) (by omega)) (hW (8 * g + 7) (by omega))
  have codeAt (y : Ref.Working) (phase pc : Nat) :
      (roundState s y phase pc q tail).executionEnv.code = Loop.bytes := by
    simpa [roundState] using hcode
  have forkAt (y : Ref.Working) (phase pc : Nat) :
      (roundState s y phase pc q tail).fork = .Osaka := by
    simpa [roundState] using hfork
  have runAt (y : Ref.Working) (phase pc : Nat) :
      (roundState s y phase pc q tail).halt = .Running := by
    simpa [roundState] using hrun
  have npAt (y : Ref.Working) (phase pc : Nat) :
      Precompile.isPrecompileWithConfig
        (roundState s y phase pc q tail).executionEnv.precompileConfig
        (roundState s y phase pc q tail).executionEnv.fork
        (roundState s y phase pc q tail).executionEnv.codeAddr = false := by
    simpa [roundState] using hnp
  let g0 := round0Trace (codeAt x0 0 912) (forkAt x0 0 912) step0
    (runAt x0 0 912) (npAt x0 0 912) rfl
  let g1 := round1Trace (codeAt x1 1 1008) (forkAt x1 1 1008) step1
    (runAt x1 1 1008) (npAt x1 1 1008) rfl
  let g2 := round2Trace (codeAt x2 2 1104) (forkAt x2 2 1104) step2
    (runAt x2 2 1104) (npAt x2 2 1104) rfl
  let g3 := round3Trace (codeAt x3 3 1200) (forkAt x3 3 1200) step3
    (runAt x3 3 1200) (npAt x3 3 1200) rfl
  let g4 := round4Trace (codeAt x4 4 1296) (forkAt x4 4 1296) step4
    (runAt x4 4 1296) (npAt x4 4 1296) rfl
  let g5 := round5Trace (codeAt x5 5 1392) (forkAt x5 5 1392) step5
    (runAt x5 5 1392) (npAt x5 5 1392) rfl
  let g6 := round6Trace (codeAt x6 6 1488) (forkAt x6 6 1488) step6
    (runAt x6 6 1488) (npAt x6 6 1488) rfl
  let g7 := round7Trace (codeAt x7 7 1584) (forkAt x7 7 1584) step7
    (runAt x7 7 1584) (npAt x7 7 1584) rfl
  let right := GasSteps.transKnown g6 g7 206 206 rfl rfl
  let right := GasSteps.transKnown g5 right 206 412 rfl rfl
  let right := GasSteps.transKnown g4 right 206 618 rfl rfl
  let right := GasSteps.transKnown g3 right 206 824 rfl rfl
  let right := GasSteps.transKnown g2 right 206 1030 rfl rfl
  let right := GasSteps.transKnown g1 right 206 1236 rfl rfl
  let trace := GasSteps.transKnown g0 right 206 1442 rfl rfl
  simpa [x0, x8, q] using trace

@[simp] theorem gasSteps_groupRounds_cost (s : State) (x : Ref.Working)
    (padded : ByteArray) (blockOff g : Nat) (tail : List UInt256)
    (hg : g < 8) (hcap : tail.length < 990)
    (hcode : s.executionEnv.code = Loop.bytes) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hK : ConstantsCorrect s.memory)
    (hW : ScheduleCorrect.WCorrect s.memory padded blockOff 64) :
    (gasSteps_groupRounds s x padded blockOff g tail hg hcap hcode hfork hrun
      hnp hK hW).cost = 1648 := by
  rfl

def groupEntry (s : State) (initial : Ref.Working) (padded : ByteArray)
    (blockOff g : Nat) (tail : List UInt256) : State :=
  roundState s (Ref.rounds initial padded blockOff (8 * g)) 0 912
    (UInt256.ofNat (256 * g)) tail

def foldEntry (s : State) (initial : Ref.Working) (padded : ByteArray)
    (blockOff : Nat) (tail : List UInt256) : State :=
  roundState s (Ref.rounds initial padded blockOff 64) 8 1696
    (UInt256.ofNat 2048) tail

private theorem nextPointer (g : Nat) (hg : g < 8) :
    UInt256.ofNat 256 + UInt256.ofNat (256 * g) =
      UInt256.ofNat (256 * (g + 1)) := by
  rw [Challenge.EvmProof.Word.ofNat_add_ofNat (by omega)]
  congr 1
  omega

private theorem ctrl_true (g : Nat) (hg : g < 7) :
    UInt256.isTrue
      (UInt256.lt (UInt256.ofNat 256 + UInt256.ofNat (256 * g))
        (UInt256.ofNat 2048)) := by
  rw [nextPointer g (by omega)]
  have hlt : 256 * (g + 1) < 2048 := by omega
  have hmod : 256 * (g + 1) % 2 ^ 256 = 256 * (g + 1) :=
    Nat.mod_eq_of_lt (by omega)
  simp only [UInt256.lt, UInt256.isTrue, word_toNat_ofNat]
  rw [hmod]
  simp [hlt]

private theorem ctrl_false :
    UInt256.isTrue
      (UInt256.lt (UInt256.ofNat 256 + UInt256.ofNat (256 * 7))
        (UInt256.ofNat 2048)) = false := by
  decide

private noncomputable def ctrlTrace {s t : State}
    (hcode : s.executionEnv.code = Loop.bytes) (hfork : s.fork = .Osaka)
    (hresult : runLocatedBlock Loop.pctrl s = some t)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (haw : s.activeWords = t.activeWords) : GasSteps s t :=
  Challenge.EvmProof.FixedPathGas.trace Loop.pctrl 36 (by rfl) (by rfl)
    (by simpa [Loop.art] using hcode) hfork hresult hrun hnp haw

private noncomputable def roundsHeadTrace {s t : State}
    (hcode : s.executionEnv.code = Loop.bytes) (hfork : s.fork = .Osaka)
    (hresult : runLocatedBlock Loop.Body.roundsHeadPath s = some t)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (haw : s.activeWords = t.activeWords) : GasSteps s t :=
  Challenge.EvmProof.FixedPathGas.trace Loop.Body.roundsHeadPath 1
    (by rfl) (by rfl) (by simpa [Loop.art] using hcode) hfork hresult hrun hnp haw

def gasSteps_groupContinue (s : State) (initial : Ref.Working)
    (padded : ByteArray) (blockOff g : Nat) (tail : List UInt256)
    (hg : g < 7) (hcap : tail.length < 990)
    (hcode : s.executionEnv.code = Loop.bytes) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hK : ConstantsCorrect s.memory)
    (hW : ScheduleCorrect.WCorrect s.memory padded blockOff 64) :
    GasSteps (groupEntry s initial padded blockOff g tail)
      (groupEntry s initial padded blockOff (g + 1) tail) := by
  let x := Ref.rounds initial padded blockOff (8 * g)
  let x' := roundsFrom x padded blockOff (8 * g) 8
  let q := UInt256.ofNat (256 * g)
  let afterRounds := roundState s x' 8 1680 q tail
  let gr : GasSteps (groupEntry s initial padded blockOff g tail) afterRounds := by
    simpa [groupEntry, afterRounds, x, x', q] using
      gasSteps_groupRounds s x padded blockOff g tail (by omega) hcap
        hcode hfork hrun hnp hK hW
  have hcRun : runLocatedBlock Loop.pctrl afterRounds =
      some { afterRounds with
        pc := UInt256.ofNat 911
        stack := phaseStack x' 8 ++
          (UInt256.ofNat 256 + q) :: tail } := by
    have h := Loop.ctrl_continue afterRounds x'.a x'.b x'.c x'.d
      x'.e x'.f x'.g x'.h q tail (by omega)
      (by simpa [afterRounds, roundState] using hrun) rfl
      (ctrl_true g hg)
      (by simpa [afterRounds, roundState, Loop.bytes] using hcode) rfl rfl
    simpa [afterRounds, roundState, phaseStack] using h
  have codeAfter : afterRounds.executionEnv.code = Loop.bytes := by
    simpa [afterRounds, roundState] using hcode
  have forkAfter : afterRounds.fork = .Osaka := by
    simpa [afterRounds, roundState] using hfork
  have runAfter : afterRounds.halt = .Running := by
    simpa [afterRounds, roundState] using hrun
  have npAfter : Precompile.isPrecompileWithConfig
      afterRounds.executionEnv.precompileConfig afterRounds.executionEnv.fork
      afterRounds.executionEnv.codeAddr = false := by
    simpa [afterRounds, roundState] using hnp
  let afterCtrl : State := { afterRounds with
    pc := UInt256.ofNat 911
    stack := phaseStack x' 8 ++ (UInt256.ofNat 256 + q) :: tail }
  let gc : GasSteps afterRounds afterCtrl :=
    ctrlTrace codeAfter forkAfter (by simpa [afterCtrl] using hcRun)
    runAfter npAfter rfl
  have hhRun : runLocatedBlock Loop.Body.roundsHeadPath afterCtrl =
      some (groupEntry s initial padded blockOff (g + 1) tail) := by
    have h := Loop.Body.run_roundsHead afterCtrl
      (phaseStack x' 8 ++ (UInt256.ofNat 256 + q) :: tail)
      (by simp [phaseStack]; omega)
      (by simpa [afterCtrl, afterRounds, roundState] using hrun) rfl rfl
    have hx : x' = Ref.rounds initial padded blockOff (8 * (g + 1)) := by
      dsimp [x', x]
      rw [roundsFrom_rounds]
      congr 4 <;> omega
    simpa [afterCtrl, afterRounds, groupEntry, roundState, phaseStack,
      hx, q, nextPointer g (by omega)] using h
  have codeCtrl : afterCtrl.executionEnv.code = Loop.bytes := by
    simpa [afterCtrl, afterRounds, roundState] using hcode
  have forkCtrl : afterCtrl.fork = .Osaka := by
    simpa [afterCtrl, afterRounds, roundState] using hfork
  have runCtrl : afterCtrl.halt = .Running := by
    simpa [afterCtrl, afterRounds, roundState] using hrun
  have npCtrl : Precompile.isPrecompileWithConfig
      afterCtrl.executionEnv.precompileConfig afterCtrl.executionEnv.fork
      afterCtrl.executionEnv.codeAddr = false := by
    simpa [afterCtrl, afterRounds, roundState] using hnp
  let gh := roundsHeadTrace codeCtrl forkCtrl hhRun runCtrl npCtrl rfl
  have hgr : gr.cost = 1648 := by
    simpa [gr] using gasSteps_groupRounds_cost s x padded blockOff g tail
      (by omega) hcap hcode hfork hrun hnp hK hW
  exact GasSteps.transKnown gr
    (GasSteps.transKnown gc gh 36 1 rfl rfl) 1648 37 hgr rfl

@[simp] theorem gasSteps_groupContinue_cost (s : State) (initial : Ref.Working)
    (padded : ByteArray) (blockOff g : Nat) (tail : List UInt256)
    (hg : g < 7) (hcap : tail.length < 990)
    (hcode : s.executionEnv.code = Loop.bytes) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hK : ConstantsCorrect s.memory)
    (hW : ScheduleCorrect.WCorrect s.memory padded blockOff 64) :
    (gasSteps_groupContinue s initial padded blockOff g tail hg hcap hcode
      hfork hrun hnp hK hW).cost = 1685 := rfl

def gasSteps_groupExit (s : State) (initial : Ref.Working)
    (padded : ByteArray) (blockOff : Nat) (tail : List UInt256)
    (hcap : tail.length < 990)
    (hcode : s.executionEnv.code = Loop.bytes) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hK : ConstantsCorrect s.memory)
    (hW : ScheduleCorrect.WCorrect s.memory padded blockOff 64) :
    GasSteps (groupEntry s initial padded blockOff 7 tail)
      (foldEntry s initial padded blockOff tail) := by
  let x := Ref.rounds initial padded blockOff 56
  let x' := roundsFrom x padded blockOff 56 8
  let q := UInt256.ofNat 1792
  let afterRounds := roundState s x' 8 1680 q tail
  let gr : GasSteps (groupEntry s initial padded blockOff 7 tail) afterRounds := by
    simpa [groupEntry, afterRounds, x, x', q] using
      gasSteps_groupRounds s x padded blockOff 7 tail (by omega) hcap
        hcode hfork hrun hnp hK hW
  have hcRun : runLocatedBlock Loop.pctrl afterRounds =
      some (foldEntry s initial padded blockOff tail) := by
    have h := Loop.ctrl_exit afterRounds x'.a x'.b x'.c x'.d
      x'.e x'.f x'.g x'.h q tail (by omega)
      (by simpa [afterRounds, roundState] using hrun) rfl ctrl_false
      (by simpa [afterRounds, roundState, Loop.bytes] using hcode) rfl rfl
    have hx : x' = Ref.rounds initial padded blockOff 64 := by
      dsimp [x', x]
      simpa using roundsFrom_rounds initial padded blockOff 56 8
    simpa [afterRounds, foldEntry, roundState, phaseStack, hx, q] using h
  let gc : GasSteps afterRounds (foldEntry s initial padded blockOff tail) := ctrlTrace
    (by simpa [afterRounds, roundState, Loop.art] using hcode)
    (by simpa [afterRounds, roundState] using hfork) hcRun
    (by simpa [afterRounds, roundState] using hrun)
    (by simpa [afterRounds, roundState] using hnp) rfl
  have hgr : gr.cost = 1648 := by
    simpa [gr] using gasSteps_groupRounds_cost s x padded blockOff 7 tail
      (by omega) hcap hcode hfork hrun hnp hK hW
  exact GasSteps.transKnown gr gc 1648 36 hgr rfl

@[simp] theorem gasSteps_groupExit_cost (s : State) (initial : Ref.Working)
    (padded : ByteArray) (blockOff : Nat) (tail : List UInt256)
    (hcap : tail.length < 990)
    (hcode : s.executionEnv.code = Loop.bytes) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hK : ConstantsCorrect s.memory)
    (hW : ScheduleCorrect.WCorrect s.memory padded blockOff 64) :
    (gasSteps_groupExit s initial padded blockOff tail hcap hcode hfork hrun
      hnp hK hW).cost = 1684 := rfl

def gasSteps_rounds (s : State) (initial : Ref.Working)
    (padded : ByteArray) (blockOff : Nat) (tail : List UInt256)
    (hcap : tail.length < 990)
    (hcode : s.executionEnv.code = Loop.bytes) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hK : ConstantsCorrect s.memory)
    (hW : ScheduleCorrect.WCorrect s.memory padded blockOff 64) :
    GasSteps (groupEntry s initial padded blockOff 0 tail)
      (foldEntry s initial padded blockOff tail) :=
  let firstSeven := GasSteps.iterateBoundedKnown 7 1685 (fun g hg =>
    gasSteps_groupContinue s initial padded blockOff g tail hg hcap
      hcode hfork hrun hnp hK hW
    ) (fun g hg => gasSteps_groupContinue_cost s initial padded blockOff g
      tail hg hcap hcode hfork hrun hnp hK hW)
  GasSteps.transKnown firstSeven
    (gasSteps_groupExit s initial padded blockOff tail hcap
      hcode hfork hrun hnp hK hW)
    (7 * 1685) 1684 rfl
    (gasSteps_groupExit_cost s initial padded blockOff tail hcap
      hcode hfork hrun hnp hK hW)

@[simp] theorem gasSteps_rounds_cost (s : State) (initial : Ref.Working)
    (padded : ByteArray) (blockOff : Nat) (tail : List UInt256)
    (hcap : tail.length < 990)
    (hcode : s.executionEnv.code = Loop.bytes) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hK : ConstantsCorrect s.memory)
    (hW : ScheduleCorrect.WCorrect s.memory padded blockOff 64) :
    (gasSteps_rounds s initial padded blockOff tail hcap hcode hfork hrun hnp
      hK hW).cost = 13479 := rfl

end

end Challenge.Sha256.Submissions.Sha256Fast.Proofs.RoundCorrect
