import Challenge.Sha256.Submissions.Sha256Fast.Proofs.ScheduleCorrect
import Challenge.Sha256.Submissions.Sha256Fast.Proofs.SchedulePathGas

set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

namespace Challenge.Sha256.Submissions.Sha256Fast.Proofs.ScheduleTrace

open EvmSemantics EvmSemantics.EVM
open Challenge.EvmProof Challenge.EvmProof.Stepper Challenge.EvmProof.Word

def entry (s : State) (returnDest : UInt256) (rest : List UInt256)
    (g : Nat) : State :=
  { s with
    pc := UInt256.ofNat 295
    activeWords := UInt256.ofNat 140
    memory := ScheduleCorrect.writeSchedule s.memory s.memory 288 (16 + 8 * g)
    stack := UInt256.ofNat (256 * g) :: returnDest :: rest }

def computed (s : State) (returnDest : UInt256) (rest : List UInt256)
    (g : Nat) : State :=
  { s with
    pc := UInt256.ofNat 883
    activeWords := UInt256.ofNat 140
    memory := ScheduleCorrect.writeSchedule s.memory s.memory 288 (24 + 8 * g)
    stack := [UInt256.ofNat 294,
      UInt256.lt (UInt256.ofNat 256 + UInt256.ofNat (256 * g))
        (UInt256.ofNat 1536),
      UInt256.ofNat 256 + UInt256.ofNat (256 * g), returnDest] ++ rest }

def backEdge (s : State) (returnDest : UInt256) (rest : List UInt256)
    (g : Nat) : State :=
  { s with
    pc := UInt256.ofNat 294
    activeWords := UInt256.ofNat 140
    memory := ScheduleCorrect.writeSchedule s.memory s.memory 288 (24 + 8 * g)
    stack := (UInt256.ofNat 256 + UInt256.ofNat (256 * g)) ::
      returnDest :: rest }

def exitState (s : State) (returnDest : UInt256)
    (rest : List UInt256) : State :=
  { s with
    pc := UInt256.ofNat 884
    activeWords := UInt256.ofNat 140
    memory := ScheduleCorrect.writeSchedule s.memory s.memory 288 64
    stack := UInt256.ofNat 1536 :: returnDest :: rest }

private theorem addPointer (g : Nat) (hg : g < 6) :
    UInt256.ofNat 256 + UInt256.ofNat (256 * g) =
      UInt256.ofNat (256 * (g + 1)) := by
  rw [Challenge.EvmProof.Word.ofNat_add_ofNat (by omega)]
  congr 1
  omega

private theorem branch_true (g : Nat) (hg : g < 5) :
    UInt256.isTrue
      (UInt256.lt (UInt256.ofNat 256 + UInt256.ofNat (256 * g))
        (UInt256.ofNat 1536)) := by
  rw [addPointer g (by omega)]
  have hlt : 256 * (g + 1) < 1536 := by omega
  have hmod : 256 * (g + 1) % 2 ^ 256 = 256 * (g + 1) :=
    Nat.mod_eq_of_lt (by omega)
  simp only [UInt256.lt, UInt256.isTrue, word_toNat_ofNat]
  rw [hmod]
  simp [hlt]

private theorem branch_false :
    UInt256.isTrue
      (UInt256.lt (UInt256.ofNat 256 + UInt256.ofNat (256 * 5))
        (UInt256.ofNat 1536)) = false := by
  decide

theorem run_compute (s : State) (returnDest : UInt256)
    (rest : List UInt256) (g : Nat) (hg : g < 6)
    (hcap : rest.length < 999) (hrun : s.halt = .Running) :
    runLocatedBlock Loop.psched_compute (entry s returnDest rest g) =
      some (computed s returnDest rest g) := by
  have h := ScheduleCorrect.run_scheduleGroup
    (entry s returnDest rest g) s.memory 288 g returnDest rest hg hcap
    rfl hrun rfl rfl (by
      simpa [entry] using ScheduleCorrect.writeSchedule_correct
        s.memory s.memory 288 (16 + 8 * g))
  have heq : 16 + 8 * g + 8 = 24 + 8 * g := by omega
  simpa [entry, computed, ScheduleCorrect.writeSchedule_add_eight, heq] using h

theorem run_backEdge (s : State) (returnDest : UInt256)
    (rest : List UInt256) (g : Nat) (hg : g < 5)
    (hcap : rest.length < 999) (hcode : s.executionEnv.code = Loop.bytes)
    (hrun : s.halt = .Running) :
    runLocatedBlock Loop.psched_branch (computed s returnDest rest g) =
      some (backEdge s returnDest rest g) := by
  apply Loop.sched_branch_continue
  · simpa only [List.length_cons] using
      (show rest.length + 1 < 1000 by omega)
  · simpa [computed] using hcode
  · simpa [computed] using hrun
  · rfl
  · exact branch_true g hg
  · simp [computed, addPointer g (by omega)]

theorem run_head (s : State) (returnDest : UInt256)
    (rest : List UInt256) (g : Nat) (hg : g < 5)
    (hcap : rest.length < 999) (hrun : s.halt = .Running) :
    runLocatedBlock Loop.Body.scheduleHeadPath
        (backEdge s returnDest rest g) =
      some (entry s returnDest rest (g + 1)) := by
  have h := Loop.Body.run_scheduleHead (backEdge s returnDest rest g)
    (UInt256.ofNat 256 + UInt256.ofNat (256 * g)) (returnDest :: rest)
    (by simp; omega) hrun rfl rfl
  have heq : 24 + 8 * g = 16 + 8 * (g + 1) := by omega
  simpa [backEdge, entry, addPointer g (by omega), heq] using h

theorem run_exit (s : State) (returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 999)
    (hrun : s.halt = .Running) :
    runLocatedBlock Loop.psched_branch (computed s returnDest rest 5) =
      some (exitState s returnDest rest) := by
  have h := Loop.sched_branch_exit (computed s returnDest rest 5)
    (UInt256.ofNat (256 * 5)) (returnDest :: rest) (by simp; omega)
    hrun rfl branch_false rfl
  simpa [computed, exitState, addPointer 5 (by omega)] using h

noncomputable def gasSteps_compute (s : State) (returnDest : UInt256)
    (rest : List UInt256) (g : Nat) (hg : g < 6)
    (hcap : rest.length < 999) (hcode : s.executionEnv.code = Loop.bytes)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (entry s returnDest rest g) (computed s returnDest rest g) :=
  SchedulePathGas.computeTrace
    (by simpa [entry] using hcode) (by simpa [entry] using hfork)
    (run_compute s returnDest rest g hg hcap hrun)
    (by simpa [entry] using hrun) (by simpa [entry] using hnp) rfl

@[simp] theorem gasSteps_compute_cost (s : State) (returnDest : UInt256)
    (rest : List UInt256) (g : Nat) (hg : g < 6)
    (hcap : rest.length < 999) (hcode : s.executionEnv.code = Loop.bytes)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    (gasSteps_compute s returnDest rest g hg hcap hcode hfork hrun hnp).cost =
      1162 := rfl

noncomputable def gasSteps_branchContinue (s : State) (returnDest : UInt256)
    (rest : List UInt256) (g : Nat) (hg : g < 5)
    (hcap : rest.length < 999) (hcode : s.executionEnv.code = Loop.bytes)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (computed s returnDest rest g) (backEdge s returnDest rest g) :=
  SchedulePathGas.branchTrace
    (by simpa [computed] using hcode) (by simpa [computed] using hfork)
    (run_backEdge s returnDest rest g hg hcap hcode hrun)
    (by simpa [computed] using hrun) (by simpa [computed] using hnp) rfl

noncomputable def gasSteps_head (s : State) (returnDest : UInt256)
    (rest : List UInt256) (g : Nat) (hg : g < 5)
    (hcap : rest.length < 999) (hcode : s.executionEnv.code = Loop.bytes)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (backEdge s returnDest rest g) (entry s returnDest rest (g + 1)) :=
  SchedulePathGas.headTrace
    (by simpa [backEdge] using hcode) (by simpa [backEdge] using hfork)
    (run_head s returnDest rest g hg hcap hrun)
    (by simpa [backEdge] using hrun) (by simpa [backEdge] using hnp) rfl

noncomputable def gasSteps_branchExit (s : State) (returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 999)
    (hcode : s.executionEnv.code = Loop.bytes) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (computed s returnDest rest 5) (exitState s returnDest rest) :=
  SchedulePathGas.branchTrace
    (by simpa [computed] using hcode) (by simpa [computed] using hfork)
    (run_exit s returnDest rest hcap hrun)
    (by simpa [computed] using hrun) (by simpa [computed] using hnp) rfl

noncomputable def gasSteps_continue (s : State) (returnDest : UInt256)
    (rest : List UInt256) (g : Nat) (hg : g < 5)
    (hcap : rest.length < 999) (hcode : s.executionEnv.code = Loop.bytes)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (entry s returnDest rest g) (entry s returnDest rest (g + 1)) :=
  GasSteps.transKnown
    (gasSteps_compute s returnDest rest g (by omega)
      hcap hcode hfork hrun hnp)
    (GasSteps.transKnown
      (gasSteps_branchContinue s returnDest rest g hg
        hcap hcode hfork hrun hnp)
      (gasSteps_head s returnDest rest g hg hcap hcode hfork hrun hnp)
      10 1 rfl rfl)
    1162 11 rfl rfl

@[simp] theorem gasSteps_continue_cost (s : State) (returnDest : UInt256)
    (rest : List UInt256) (g : Nat) (hg : g < 5)
    (hcap : rest.length < 999) (hcode : s.executionEnv.code = Loop.bytes)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    (gasSteps_continue s returnDest rest g hg hcap hcode hfork hrun hnp).cost =
      1173 := rfl

noncomputable def gasSteps_exit (s : State) (returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 999)
    (hcode : s.executionEnv.code = Loop.bytes) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (entry s returnDest rest 5) (exitState s returnDest rest) :=
  GasSteps.transKnown
    (gasSteps_compute s returnDest rest 5 (by omega)
      hcap hcode hfork hrun hnp)
    (gasSteps_branchExit s returnDest rest hcap hcode hfork hrun hnp)
    1162 10 rfl rfl

@[simp] theorem gasSteps_exit_cost (s : State) (returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 999)
    (hcode : s.executionEnv.code = Loop.bytes) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    (gasSteps_exit s returnDest rest hcap hcode hfork hrun hnp).cost = 1172 := rfl

noncomputable def gasSteps_schedule (s : State) (returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 999)
    (hcode : s.executionEnv.code = Loop.bytes) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (entry s returnDest rest 0) (exitState s returnDest rest) :=
  let firstFive := GasSteps.iterateBoundedKnown 5 1173 (fun g hg =>
    gasSteps_continue s returnDest rest g hg hcap hcode hfork hrun hnp
    ) (fun g hg => gasSteps_continue_cost s returnDest rest g hg
      hcap hcode hfork hrun hnp)
  GasSteps.transKnown firstFive
    (gasSteps_exit s returnDest rest hcap hcode hfork hrun hnp)
    (5 * 1173) 1172 rfl
    (gasSteps_exit_cost s returnDest rest hcap hcode hfork hrun hnp)

@[simp] theorem gasSteps_schedule_cost (s : State) (returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 999)
    (hcode : s.executionEnv.code = Loop.bytes) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    (gasSteps_schedule s returnDest rest hcap hcode hfork hrun hnp).cost = 7037 := rfl

end Challenge.Sha256.Submissions.Sha256Fast.Proofs.ScheduleTrace
