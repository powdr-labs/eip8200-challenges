import Sha256Fast.Word
import Sha256Fast.Attr
import Challenge.EvmProof.Stepper
import Challenge.EvmProof.Memory
set_option warningAsError true

namespace Challenge.Sha256.Fast

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.EvmProof
open Challenge.EvmProof.Stepper
open Challenge.EvmProof.Word

/-! ## 8. Discharging a straight-line block

Two frictions show up when reducing `runLocatedBlock` over a symbolic state,
and both are handled once here rather than per block.

*Stack caps.*  Every `runInstr` guards on `stack.length < 1024`.  `simp`
normalises those to `rest.length ≤ N` for a literal `N` that depends on how
many temporaries are live, so supplying `rest.length < 1000` alone does not
discharge them.  `stackCap` is a conditional rewrite that turns *any* such
literal comparison into `True`, with simp's own discharger settling `1000 ≤ N`.

*Operand forms.*  A pushed constant lands on top of the stack, so the mask
appears as `land 0xffffffff v`; and the stepper emits `UInt256.land`/`.xor`
rather than the `&&&`/`^^^` notation.  The simp lemmas above are keyed on the
forms that actually occur. -/

theorem stackCap {α : Type _} {l : List α} {n : Nat}
    (h : l.length < 1000) (hn : 1000 ≤ n) : (l.length ≤ n) = True :=
  eq_true (by omega)

@[simp] theorem land_maskLit (v : W256) :
    UInt256.land (UInt256.ofNat 4294967295) v = ofUInt32 (toUInt32 v) :=
  maskC_eq v

/-! The unfolding set for straight-line EVM block reduction.  A submission
tags its own generated `path`, artifact, instruction list and byte literal
with `@[evmStep]`; everything generic is registered just below.
The attribute itself is declared in `Sha256Fast.Attr` because Lean requires a
simp attribute to be introduced in a module earlier than its first use. -/

attribute [evmStep]
  Challenge.EvmProof.Stepper.runLocatedBlock
  Challenge.EvmProof.Stepper.runLocated
  Challenge.EvmProof.Stepper.runInstr
  Challenge.EvmProof.ProgramArtifact.instructionPC
  YulEvmCompiler.assembleBytes
  YulEvmCompiler.Instr.bytes
  List.exchange
  EvmSemantics.Crypto.Sha256.bigSigma0
  EvmSemantics.Crypto.Sha256.bigSigma1
  EvmSemantics.Crypto.Sha256.smallSigma0
  EvmSemantics.Crypto.Sha256.smallSigma1

/-! The machine reduction also needs list computation: stack indexing for
`DUP`, length for the capacity guards, and prefix/flatMap for `instructionPC`.
Supplying these explicitly is what lets stage 1 run as `simp only`, which is
far faster than letting the whole default simp set loose on a term the size of
a 63-instruction symbolic trace. -/

attribute [evmStep]
  List.length_append List.length_cons List.length_nil
  List.cons_append List.nil_append
  List.getElem?_cons_zero List.getElem?_cons_succ
  List.take_succ_cons List.take_zero
  List.flatMap_cons List.flatMap_nil
  List.append_assoc
  ite_true ite_false Option.map_some Option.map_none
  Option.bind_some Option.bind_none Option.pure_def
  Option.bind_eq_bind
  List.set_cons_zero List.set_cons_succ List.set_nil

/-! Program-counter and memory-watermark normalisation.  The stepper advances
`pc` by `.succ` and `+ ofNat w`, so after a block it is an unreduced chain;
folding it to a literal is what makes a block's end state *nameable*, and
hence composable with the next block. -/

attribute [evmStep]
  Challenge.EvmProof.Word.succ_ofNat
  Challenge.EvmProof.Word.ofNat_add_ofNat
  EvmSemantics.EVM.State.activeWordsAfterUInt256

/-! Memory: `MSTORE` emits `writeBytes _ (natToBytesPadded v.toNat 32) off`,
which is exactly the shape `readWord_writeWord` consumes, so reading back a
slot the block just wrote reduces automatically.  The disjoint case carries a
side condition that is literal arithmetic for the artifact's fixed W and H
offsets, so simp's discharger settles it. -/

attribute [evmStep]
  Challenge.EvmProof.Memory.readWord_writeWord
  Challenge.EvmProof.Memory.readWord_writeBytes_disjoint

/-- Disjoint read-over-write for *pointer-relative* addresses, as they occur
inside a loop body: both addresses are `ofNat k + u` for literal `k` and a
shared symbolic pointer `u`.  The generic
`readWord_writeBytes_disjoint` cannot fire there because its side condition
is arithmetic over the symbolic `u`; here the side conditions are a literal
comparison on the two offsets plus a pointer bound that sits in the caller's
context, both of which simp's discharger settles.  The `3168 + 1280 + 32 ≤
4480` headroom matches the artifact's memory extent. -/
@[evmStep] theorem readWord_writeWord_disjoint_rel (bs : ByteArray)
    (v : UInt256) (a b : Nat) (u : W256) (hu : u.toNat ≤ 1280)
    (ha : a ≤ 3168) (hb : b ≤ 3168)
    (hab : a + 32 ≤ b ∨ b + 32 ≤ a) :
    MachineState.readWord
      (MachineState.writeBytes bs (Data.Bytes.natToBytesPadded v.toNat 32)
        (UInt256.ofNat b + u).toNat)
      (UInt256.ofNat a + u).toNat =
    MachineState.readWord bs (UInt256.ofNat a + u).toNat := by
  apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
  have hsize : (Data.Bytes.natToBytesPadded v.toNat 32).size = 32 := by
    simp [Data.Bytes.natToBytesPadded, ByteArray.size]
  have hna : (UInt256.ofNat a + u).toNat = a + u.toNat := by
    rw [word_toNat_add, word_toNat_ofNat,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have hnb : (UInt256.ofNat b + u).toNat = b + u.toNat := by
    rw [word_toNat_add, word_toNat_ofNat,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  rw [hsize, hna, hnb]
  omega

/-! ## Pinning the memory watermark

When a loop body addresses memory off a stack pointer, every address is a
symbolic term and `activeWordsAfter` stays an unreduced `max` that grows with
each `MLOAD` — which is what makes such a block roughly ten times more
expensive to reduce than one using literal offsets.  The artifact keeps its
memory footprint constant (the driver's K-table initialisation touches the
highest address there is), so the watermark is a *literal* throughout the body.
Supplying the address bound lets simp collapse it at each access rather than
nesting. -/

@[evmStep] theorem activeWordsAfter_pin {off : Nat} (h : off + 32 ≤ 4480) :
    EvmSemantics.MachineState.activeWordsAfter 140 off 32 = 140 := by
  unfold EvmSemantics.MachineState.activeWordsAfter
  split
  · omega
  · show Nat.max 140 ((off + 32 - 1) / 32 + 1) = 140
    exact Nat.max_eq_left (by omega)

/-! ## Branch conditions

`JUMPI` guards on `UInt256.isTrue c`, i.e. `c.toNat ≠ 0`, and a loop test
built from `LT` produces `(UInt256.lt a b).isTrue`.  These two lemmas turn
that into the arithmetic comparison the caller already has, and they are what
every `LT`-guarded loop in a submission will need. -/

@[evmStep] theorem lt_isTrue {a b : W256} (h : a.toNat < b.toNat) :
    UInt256.isTrue (UInt256.lt a b) = True := by
  simp only [UInt256.lt, if_pos h, UInt256.isTrue, eq_iff_iff, iff_true]
  simp [word_toNat_ofNat]

@[evmStep] theorem lt_isFalse {a b : W256} (h : b.toNat ≤ a.toNat) :
    UInt256.isTrue (UInt256.lt a b) = False := by
  simp only [UInt256.lt, if_neg (by omega : ¬ a.toNat < b.toNat), UInt256.isTrue,
    eq_iff_iff, iff_false, not_not]
  simp [word_toNat_ofNat]

/-! ## Composing blocks

`runLocatedBlock` special-cases its last instruction (it does not require the
machine to still be running afterwards), so concatenation is not quite a monadic
bind.  This is the lemma that lets a body be proved one block at a time and then
chained: the intermediate state must be `Running`, which every non-terminal
block of a straight-line body is. -/

theorem runLocatedBlock_append {artifact : ProgramArtifact} {fork : Fork}
    (p q : List (Located artifact fork)) {s m t : State}
    (hp : runLocatedBlock p s = some m) (hm : m.halt = .Running)
    (hq : runLocatedBlock q m = some t) :
    runLocatedBlock (p ++ q) s = some t := by
  induction p generalizing s with
  | nil =>
      simp only [runLocatedBlock, Option.some.injEq] at hp
      subst hp
      simpa using hq
  | cons a p' ih =>
      rw [List.cons_append]
      cases hnext : runLocated a s with
      | none => simp [runLocatedBlock, hnext] at hp
      | some next =>
        cases p' with
        | nil =>
            simp only [runLocatedBlock, hnext, Option.some.injEq] at hp
            subst hp
            cases q with
            | nil =>
                simp only [runLocatedBlock, Option.some.injEq] at hq
                subst hq
                simp [runLocatedBlock, hnext]
            | cons b q' =>
                simp only [List.nil_append, runLocatedBlock, hnext, hm]
                exact hq
        | cons b p'' =>
            simp only [runLocatedBlock, hnext] at hp
            cases hrun : next.halt with
            | Running =>
                simp only [hrun] at hp
                simp only [runLocatedBlock, hnext, hrun]
                have := ih hp
                rwa [List.cons_append] at this
            | Success => simp [hrun] at hp
            | Returned => simp [hrun] at hp
            | Reverted => simp [hrun] at hp
            | Exception e => simp [hrun] at hp

/-- Reduce a straight-line `runLocatedBlock` over a symbolic state.  Given the
frame's stack bound (`h : rest.length < 1000`) as an argument, the stack-cap
guards are discharged too. -/
syntax "evm_block" (ppSpace colGt term)? : tactic
macro_rules
  | `(tactic| evm_block) =>
    `(tactic| simp +arith +decide (maxSteps := 4000000) [*, evmStep])
  | `(tactic| evm_block $h) =>
    `(tactic| simp +arith +decide (maxSteps := 4000000)
        [*, evmStep, stackCap $h])

end Challenge.Sha256.Fast
