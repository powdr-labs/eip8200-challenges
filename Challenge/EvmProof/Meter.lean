import Challenge.EvmProof.Stepper
import Mathlib.Order.Monotone.Basic
import Challenge.EvmProof.Word

set_option warningAsError true

/-!
# Executable non-memory gas metering

Memory-expansion gas is a potential difference.  This module removes that
difference from single-instruction costs and exposes a block-level quantity
that telescopes across arbitrary successful symbolic paths.
-/

namespace Challenge.EvmProof.Meter

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler

theorem memCost_monotone : Monotone MachineState.memCost := by
  intro a b hab
  unfold MachineState.memCost
  exact Nat.add_le_add (Nat.mul_le_mul_left 3 hab)
    (Nat.div_le_div_right (Nat.pow_le_pow_left hab 2))

private theorem activeWordsAfter_ge (curr offset size : Nat) :
    curr ≤ MachineState.activeWordsAfter curr offset size := by
  rw [MachineState.activeWordsAfter]
  split
  · rfl
  · exact Nat.le_max_left _ _

private theorem activeWordsAfter_lt (curr off size : UInt256) :
    MachineState.activeWordsAfter curr.toNat off.toNat size.toNat < 2 ^ 256 := by
  have hcurr : curr.toNat < 2 ^ 256 := curr.val.isLt
  have hoff : off.toNat < 2 ^ 256 := off.val.isLt
  have hsize : size.toNat < 2 ^ 256 := size.val.isLt
  rw [MachineState.activeWordsAfter]
  split
  · exact hcurr
  · rw [Nat.max_lt]
    constructor
    · exact hcurr
    · have hdiv : (off.toNat + size.toNat - 1) / 32 < 2 ^ 256 := by
        rw [Nat.div_lt_iff_lt_mul (by omega)]
        omega
      omega

@[simp] theorem memExpansionDelta_add (curr off size : UInt256) :
    MachineState.memExpansionDelta curr.toNat off.toNat size.toNat +
        MachineState.memCost curr.toNat =
      MachineState.memCost
        (UInt256.ofNat
          (MachineState.activeWordsAfter curr.toNat off.toNat size.toNat)).toNat := by
  have hle : MachineState.memCost curr.toNat ≤
      MachineState.memCost
        (MachineState.activeWordsAfter curr.toNat off.toNat size.toNat) :=
    memCost_monotone (activeWordsAfter_ge _ _ _)
  rw [Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt (activeWordsAfter_lt curr off size)]
  unfold MachineState.memExpansionDelta
  omega

private theorem activeWordsAfter2_lt (curr off₁ size₁ off₂ size₂ : UInt256) :
    MachineState.activeWordsAfter
        (MachineState.activeWordsAfter curr.toNat off₁.toNat size₁.toNat)
        off₂.toNat size₂.toNat < 2 ^ 256 := by
  let mid : UInt256 := UInt256.ofNat
    (MachineState.activeWordsAfter curr.toNat off₁.toNat size₁.toNat)
  have hmid : mid.toNat =
      MachineState.activeWordsAfter curr.toNat off₁.toNat size₁.toNat := by
    rw [show mid.toNat =
        MachineState.activeWordsAfter curr.toNat off₁.toNat size₁.toNat % 2 ^ 256 by
      exact Challenge.EvmProof.Word.word_toNat_ofNat _]
    exact Nat.mod_eq_of_lt (activeWordsAfter_lt curr off₁ size₁)
  simpa [hmid] using activeWordsAfter_lt mid off₂ size₂

@[simp] theorem memExpansionDelta2_add
    (curr off₁ size₁ off₂ size₂ : UInt256) :
    MachineState.memExpansionDelta2 curr.toNat
        off₁.toNat size₁.toNat off₂.toNat size₂.toNat +
        MachineState.memCost curr.toNat =
      MachineState.memCost
        (UInt256.ofNat
          (MachineState.activeWordsAfter
            (MachineState.activeWordsAfter curr.toNat off₁.toNat size₁.toNat)
            off₂.toNat size₂.toNat)).toNat := by
  have hle₁ : curr.toNat ≤
      MachineState.activeWordsAfter curr.toNat off₁.toNat size₁.toNat :=
    activeWordsAfter_ge _ _ _
  have hle₂ : MachineState.activeWordsAfter curr.toNat off₁.toNat size₁.toNat ≤
      MachineState.activeWordsAfter
        (MachineState.activeWordsAfter curr.toNat off₁.toNat size₁.toNat)
        off₂.toNat size₂.toNat := activeWordsAfter_ge _ _ _
  have hmem : MachineState.memCost curr.toNat ≤
      MachineState.memCost
        (MachineState.activeWordsAfter
          (MachineState.activeWordsAfter curr.toNat off₁.toNat size₁.toNat)
          off₂.toNat size₂.toNat) := memCost_monotone (hle₁.trans hle₂)
  rw [Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt (activeWordsAfter2_lt curr off₁ size₁ off₂ size₂)]
  unfold MachineState.memExpansionDelta2
  omega

private theorem oneRangeBasePotential (base : Nat) (curr off size : UInt256) :
    (base + MachineState.memExpansionDelta curr.toNat off.toNat size.toNat) +
        MachineState.memCost curr.toNat =
      base + MachineState.memCost
        (UInt256.ofNat
          (MachineState.activeWordsAfter curr.toNat off.toNat size.toNat)).toNat := by
  have h := memExpansionDelta_add curr off size
  omega

private theorem oneRange32Potential (base : Nat) (curr off : UInt256) :
    (base + MachineState.memExpansionDelta curr.toNat off.toNat 32) +
        MachineState.memCost curr.toNat =
      base + MachineState.memCost
        (UInt256.ofNat
          (MachineState.activeWordsAfter curr.toNat off.toNat 32)).toNat := by
  simpa [Challenge.EvmProof.Word.word_toNat_ofNat] using
    oneRangeBasePotential base curr off (UInt256.ofNat 32)

private theorem oneRange1Potential (base : Nat) (curr off : UInt256) :
    (base + MachineState.memExpansionDelta curr.toNat off.toNat 1) +
        MachineState.memCost curr.toNat =
      base + MachineState.memCost
        (UInt256.ofNat
          (MachineState.activeWordsAfter curr.toNat off.toNat 1)).toNat := by
  simpa [Challenge.EvmProof.Word.word_toNat_ofNat] using
    oneRangeBasePotential base curr off (UInt256.ofNat 1)

private theorem oneRangeCopyPotential (base extra : Nat)
    (curr off size : UInt256) :
    (base + MachineState.memExpansionDelta curr.toNat off.toNat size.toNat + extra) +
        MachineState.memCost curr.toNat =
      (base + extra) + MachineState.memCost
        (UInt256.ofNat
          (MachineState.activeWordsAfter curr.toNat off.toNat size.toNat)).toNat := by
  have h := memExpansionDelta_add curr off size
  omega

private theorem twoRangeCopyPotential (base extra : Nat)
    (curr off₁ size₁ off₂ size₂ : UInt256) :
    (base + MachineState.memExpansionDelta2 curr.toNat
        off₁.toNat size₁.toNat off₂.toNat size₂.toNat + extra) +
        MachineState.memCost curr.toNat =
      (base + extra) + MachineState.memCost
        (UInt256.ofNat
          (MachineState.activeWordsAfter
            (MachineState.activeWordsAfter curr.toNat off₁.toNat size₁.toNat)
            off₂.toNat size₂.toNat)).toNat := by
  have h := memExpansionDelta2_add curr off₁ size₁ off₂ size₂
  omega

/-- Instruction work with the memory-expansion potential removed. Copy-word
charges remain because they are genuine size-dependent work. -/
def instrCostWithoutMemory : Instr → State → Nat
  | .push width _, s => Gas.baseCost s.fork (.Push ⟨width⟩)
  | .op .CALLDATACOPY, s => match s.stack with
      | _ :: _ :: size :: _ =>
          Gas.baseCost s.fork .CALLDATACOPY + Gas.copyWordCost size
      | _ => Gas.baseCost s.fork .CALLDATACOPY
  | .op .MLOAD, s => Gas.baseCost s.fork .MLOAD
  | .op .MSTORE, s => Gas.baseCost s.fork .MSTORE
  | .op .MSTORE8, s => Gas.baseCost s.fork .MSTORE8
  | .op .MCOPY, s => match s.stack with
      | _ :: _ :: size :: _ =>
          Gas.baseCost s.fork .MCOPY + Gas.copyWordCost size
      | _ => Gas.baseCost s.fork .MCOPY
  | .op .RETURN, s => Gas.baseCost s.fork .RETURN
  | .op op, s => Gas.baseCost s.fork op

theorem runInstr_cost_potential {instruction : Instr} {s t : State}
    (hresult : Stepper.runInstr instruction s = some t) :
    Stepper.instrCost instruction s + MachineState.memCost s.activeWords.toNat =
      instrCostWithoutMemory instruction s +
        MachineState.memCost t.activeWords.toNat := by
  unfold Stepper.runInstr at hresult
  split at hresult
  · split at hresult
    all_goals
      repeat' first | split at hresult | simp_all
    all_goals subst t
    all_goals simp_all [Stepper.instrCost, instrCostWithoutMemory, Gas.totalCost,
      Gas.calldatacopyTotal, Gas.mloadTotal, Gas.mstoreTotal,
      Gas.mstore8Total, Gas.mcopyTotal, Gas.returnTotal,
      State.activeWordsAfterUInt256, State.activeWordsAfterUInt256_2,
      oneRangeBasePotential, oneRange32Potential, oneRange1Potential,
      oneRangeCopyPotential, twoRangeCopyPotential]
  · simp_all

theorem runLocated_cost_potential
    {artifact : Challenge.EvmProof.ProgramArtifact} {fork : Fork}
    {located : Stepper.Located artifact fork} {s t : State}
    (hresult : Stepper.runLocated located s = some t) :
    Stepper.instrCost located.instruction s +
        MachineState.memCost s.activeWords.toNat =
      instrCostWithoutMemory located.instruction s +
        MachineState.memCost t.activeWords.toNat := by
  unfold Stepper.runLocated at hresult
  split at hresult
  · exact runInstr_cost_potential hresult
  · simp_all

/-- Execute the same path as `runLocatedBlockCost`, summing only charges that
are not memory expansion. -/
def runLocatedBlockCostWithoutMemory
    {artifact : Challenge.EvmProof.ProgramArtifact} {fork : Fork} :
    List (Stepper.Located artifact fork) → State → Nat
  | [], _ => 0
  | located :: rest, s =>
      instrCostWithoutMemory located.instruction s +
        match rest with
        | [] => 0
        | _ :: _ =>
            match Stepper.runLocated located s with
            | some next =>
                match next.halt with
                | .Running => runLocatedBlockCostWithoutMemory rest next
                | _ => 0
            | none => 0

/-- State-independent instruction cost used by memory-only paths. Copy
instructions are intentionally excluded by the hypothesis of
`runLocatedBlockCostWithoutMemory_eq_static`. -/
def instrStaticCost (fork : Fork) : Instr → Nat
  | .push width _ => Gas.baseCost fork (.Push ⟨width⟩)
  | .op op => Gas.baseCost fork op

/-- Instructions whose non-memory charge is state-independent.  The two copy
opcodes are excluded because their per-word charge depends on the runtime
copy length; ordinary loads, stores, and returns are included because their
memory expansion is already separated by `instrCostWithoutMemory`. -/
def CopyFree : Instr → Bool
  | .op .CALLDATACOPY => false
  | .op .MCOPY => false
  | _ => true

theorem instrCostWithoutMemory_eq_static_of_copyFree
    (instruction : Instr) (s : State) (fork : Fork)
    (hfork : s.fork = fork) (hfree : CopyFree instruction) :
    instrCostWithoutMemory instruction s = instrStaticCost fork instruction := by
  cases instruction with
  | push width value => simp [instrCostWithoutMemory, instrStaticCost, hfork]
  | op op =>
      cases op with
      | StopArith op => cases op <;> simp [instrCostWithoutMemory, instrStaticCost, hfork]
      | CompBit op => cases op <;> simp [instrCostWithoutMemory, instrStaticCost, hfork]
      | Keccak op => cases op; simp [instrCostWithoutMemory, instrStaticCost, hfork]
      | Env op => cases op <;> simp [CopyFree, instrCostWithoutMemory,
          instrStaticCost, hfork] at hfree ⊢
      | Block op => cases op <;> simp [instrCostWithoutMemory, instrStaticCost, hfork]
      | StackMemFlow op => cases op <;> simp [CopyFree, instrCostWithoutMemory,
          instrStaticCost, hfork] at hfree ⊢
      | Push op => cases op; simp [instrCostWithoutMemory, instrStaticCost, hfork]
      | Dup op => cases op; simp [instrCostWithoutMemory, instrStaticCost, hfork]
      | Swap op => cases op; simp [instrCostWithoutMemory, instrStaticCost, hfork]
      | DupN op => cases op; simp [instrCostWithoutMemory, instrStaticCost, hfork]
      | SwapN op => cases op; simp [instrCostWithoutMemory, instrStaticCost, hfork]
      | Exchange op => cases op; simp [instrCostWithoutMemory, instrStaticCost, hfork]
      | Log op => cases op; simp [instrCostWithoutMemory, instrStaticCost, hfork]
      | System op => cases op <;> simp [instrCostWithoutMemory, instrStaticCost, hfork]

def runLocatedBlockStaticCost
    {artifact : Challenge.EvmProof.ProgramArtifact} {fork : Fork}
    (path : List (Stepper.Located artifact fork)) : Nat :=
  (path.map (fun located => instrStaticCost fork located.instruction)).sum

/-- On a successful path whose non-memory instruction charges are static,
the executable work meter is just the sum of those static charges. The
hypothesis is deliberately stated extensionally so concrete paths discharge
it by simplification without a separate opcode whitelist. -/
theorem runLocatedBlockCostWithoutMemory_eq_static
    {artifact : Challenge.EvmProof.ProgramArtifact} {fork : Fork}
    (path : List (Stepper.Located artifact fork)) {s t : State}
    (hresult : Stepper.runLocatedBlock path s = some t)
    (hfork : s.fork = fork)
    (hstatic : ∀ located, located ∈ path → ∀ q,
      q.fork = fork →
        instrCostWithoutMemory located.instruction q =
          instrStaticCost fork located.instruction) :
    runLocatedBlockCostWithoutMemory path s =
      runLocatedBlockStaticCost path := by
  induction path generalizing s t with
  | nil =>
      simp [runLocatedBlockCostWithoutMemory, runLocatedBlockStaticCost]
  | cons located rest ih =>
      cases rest with
      | nil =>
          simp [runLocatedBlockCostWithoutMemory, runLocatedBlockStaticCost,
            hstatic located (by simp) s hfork]
      | cons nextLocated tail =>
          cases hnext : Stepper.runLocated located s with
          | none =>
              simp [Stepper.runLocatedBlock, hnext] at hresult
          | some next =>
              cases hrun : next.halt with
              | Running =>
                  simp [Stepper.runLocatedBlock, hnext, hrun] at hresult
                  have hnextFork : next.fork = fork := by
                    have henv := Stepper.runLocated_executionEnv hnext
                    simpa [State.fork, henv] using hfork
                  have htailStatic : ∀ member,
                      member ∈ nextLocated :: tail → ∀ q,
                      q.fork = fork →
                        instrCostWithoutMemory member.instruction q =
                          instrStaticCost fork member.instruction := by
                    intro member hmem q hqfork
                    exact hstatic member (by simp [hmem]) q hqfork
                  have htail := ih hresult hnextFork htailStatic
                  have hwork :
                      runLocatedBlockCostWithoutMemory
                          (located :: nextLocated :: tail) s =
                        instrCostWithoutMemory located.instruction s +
                          runLocatedBlockCostWithoutMemory
                            (nextLocated :: tail) next := by
                    simp [runLocatedBlockCostWithoutMemory, hnext, hrun]
                  have hsum :
                      runLocatedBlockStaticCost
                          (located :: nextLocated :: tail) =
                        instrStaticCost fork located.instruction +
                          runLocatedBlockStaticCost
                            (nextLocated :: tail) := by
                    simp [runLocatedBlockStaticCost]
                  rw [hwork, hsum, htail,
                    hstatic located (by simp) s hfork]
              | Success =>
                  simp [Stepper.runLocatedBlock, hnext, hrun] at hresult
              | Returned =>
                  simp [Stepper.runLocatedBlock, hnext, hrun] at hresult
              | Reverted =>
                  simp [Stepper.runLocatedBlock, hnext, hrun] at hresult
              | Exception error =>
                  simp [Stepper.runLocatedBlock, hnext, hrun] at hresult

/-- Memory expansion telescopes across every successful located basic block. -/
theorem runLocatedBlock_cost_potential
    {artifact : Challenge.EvmProof.ProgramArtifact} {fork : Fork}
    (path : List (Stepper.Located artifact fork)) {s t : State}
    (hresult : Stepper.runLocatedBlock path s = some t) :
    Stepper.runLocatedBlockCost path s +
        MachineState.memCost s.activeWords.toNat =
      runLocatedBlockCostWithoutMemory path s +
        MachineState.memCost t.activeWords.toNat := by
  induction path generalizing s t with
  | nil =>
      simp [Stepper.runLocatedBlock] at hresult
      subst t
      simp [Stepper.runLocatedBlockCost, runLocatedBlockCostWithoutMemory]
  | cons located rest ih =>
      cases rest with
      | nil =>
          cases hnext : Stepper.runLocated located s with
          | none =>
              simp [Stepper.runLocatedBlock, hnext] at hresult
          | some next =>
              simp [Stepper.runLocatedBlock, hnext] at hresult
              subst t
              simpa [Stepper.runLocatedBlockCost,
                runLocatedBlockCostWithoutMemory] using
                runLocated_cost_potential hnext
      | cons nextLocated tail =>
          cases hnext : Stepper.runLocated located s with
          | none =>
              simp [Stepper.runLocatedBlock, hnext] at hresult
          | some next =>
              cases hrun : next.halt with
              | Running =>
                  simp [Stepper.runLocatedBlock, hnext, hrun] at hresult
                  have hhead := runLocated_cost_potential hnext
                  have htail := ih hresult
                  have hcost :
                      Stepper.runLocatedBlockCost
                          (located :: nextLocated :: tail) s =
                        Stepper.instrCost located.instruction s +
                          Stepper.runLocatedBlockCost
                            (nextLocated :: tail) next := by
                    simp [Stepper.runLocatedBlockCost, hnext, hrun]
                  have hwork :
                      runLocatedBlockCostWithoutMemory
                          (located :: nextLocated :: tail) s =
                        instrCostWithoutMemory located.instruction s +
                          runLocatedBlockCostWithoutMemory
                            (nextLocated :: tail) next := by
                    simp [runLocatedBlockCostWithoutMemory, hnext, hrun]
                  rw [hcost, hwork]
                  omega
              | Success =>
                  simp [Stepper.runLocatedBlock, hnext, hrun] at hresult
              | Returned =>
                  simp [Stepper.runLocatedBlock, hnext, hrun] at hresult
              | Reverted =>
                  simp [Stepper.runLocatedBlock, hnext, hrun] at hresult
              | Exception error =>
                  simp [Stepper.runLocatedBlock, hnext, hrun] at hresult

/-- Successful memory-only blocks charge their static opcode sum plus the
change in memory potential. -/
theorem runLocatedBlock_cost_static_potential
    {artifact : Challenge.EvmProof.ProgramArtifact} {fork : Fork}
    (path : List (Stepper.Located artifact fork)) {s t : State}
    (hresult : Stepper.runLocatedBlock path s = some t)
    (hfork : s.fork = fork)
    (hstatic : ∀ located, located ∈ path → ∀ q,
      q.fork = fork →
        instrCostWithoutMemory located.instruction q =
          instrStaticCost fork located.instruction) :
    Stepper.runLocatedBlockCost path s +
        MachineState.memCost s.activeWords.toNat =
      runLocatedBlockStaticCost path +
        MachineState.memCost t.activeWords.toNat := by
  rw [runLocatedBlock_cost_potential path hresult]
  rw [runLocatedBlockCostWithoutMemory_eq_static path hresult hfork hstatic]

/-- Convenient specialization of `runLocatedBlock_cost_static_potential` for
concrete paths containing no length-dependent copy instruction. -/
theorem runLocatedBlock_cost_potential_of_copyFree
    {artifact : Challenge.EvmProof.ProgramArtifact} {fork : Fork}
    (path : List (Stepper.Located artifact fork)) {s t : State} (work : Nat)
    (hresult : Stepper.runLocatedBlock path s = some t)
    (hfork : s.fork = fork)
    (hfree : ∀ located ∈ path, CopyFree located.instruction)
    (hcost : runLocatedBlockStaticCost path = work) :
    Stepper.runLocatedBlockCost path s +
        MachineState.memCost s.activeWords.toNat =
      work + MachineState.memCost t.activeWords.toNat := by
  rw [← hcost]
  apply runLocatedBlock_cost_static_potential path hresult hfork
  intro located hmem q hq
  exact instrCostWithoutMemory_eq_static_of_copyFree
    located.instruction q fork hq (hfree located hmem)

theorem gasSteps_trans_cost_potential {s t u : State}
    (first : GasSteps s t) (second : GasSteps t u) (firstWork secondWork : Nat)
    (hfirst : first.cost + MachineState.memCost s.activeWords.toNat =
      firstWork + MachineState.memCost t.activeWords.toNat)
    (hsecond : second.cost + MachineState.memCost t.activeWords.toNat =
      secondWork + MachineState.memCost u.activeWords.toNat) :
    (first.trans second).cost + MachineState.memCost s.activeWords.toNat =
      (firstWork + secondWork) +
        MachineState.memCost u.activeWords.toNat := by
  simp only [GasSteps.trans_cost]
  omega

/-- Additive form of bounded-loop potential telescoping. Unlike a formula
with natural subtraction, this requires no separate monotonicity proof. -/
theorem iterateBounded_cost_potential_add {I : Nat → State}
    (count work : Nat)
    (body : ∀ i, i < count → GasSteps (I i) (I (i + 1)))
    (hbody : ∀ i (hi : i < count),
      (body i hi).cost + MachineState.memCost (I i).activeWords.toNat =
        work + MachineState.memCost (I (i + 1)).activeWords.toNat) :
    (GasSteps.iterateBounded count body).cost +
        MachineState.memCost (I 0).activeWords.toNat =
      count * work + MachineState.memCost (I count).activeWords.toNat := by
  induction count with
  | zero =>
      rw [GasSteps.iterateBounded_zero_cost]
      simp
  | succ count ih =>
      rw [GasSteps.iterateBounded_succ_cost]
      have hprefix := ih
        (body := fun i hi => body i (Nat.lt_succ_of_lt hi))
        (hbody := fun i hi => hbody i (Nat.lt_succ_of_lt hi))
      have hlast := hbody count (Nat.lt_succ_self count)
      simp only [Nat.succ_mul]
      omega

end Challenge.EvmProof.Meter
