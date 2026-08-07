# Tactics and proof techniques introduced

This is the reusable part of the work: nothing here is specific to a
particular SHA-256 artifact, and most of it applies to any direct-bytecode
proof against `Challenge/EvmProof/`.

---

## 1. `bit_blast32` — axiom-free 32-bit bitwise identities

```lean
macro "bit_blast32" : tactic =>
  `(tactic|
    (apply UInt32.toBitVec_inj.mp
     ext i
     have hall : (UInt32.toBitVec 4294967295)[i] = true := by revert i; decide
     simp only [UInt32.toBitVec_xor, UInt32.toBitVec_and, UInt32.toBitVec_or,
       BitVec.getElem_xor, BitVec.getElem_and, BitVec.getElem_or, hall]
     grind))
```

Closes `Ch`, `Maj` and any similar identity in well under a second.

**Why not `bv_decide`.** It closes these goals faster, but `#print axioms`
shows it adds `<thm>._native.bv_decide.ax_N` to the transitive footprint, and
the challenge admits only `propext`, `Classical.choice`, `Quot.sound`.
`native_decide` is out for the same reason, and plain `decide` is hopeless
(2^96 cases for a ternary identity). **Check the axiom footprint of any new
tactic before building on it** — this cost a rewrite when discovered late.

**Why `grind` rather than `generalize`/`revert`/`decide`.** After bit
extensionality the goal is a Boolean identity in the `i`-th bits. `grind`
splits on the `Bool` atoms itself, so the tactic needs no knowledge of how many
variables the identity mentions. The hand-rolled alternative has to name each
bit and breaks whenever the arity changes.

The `hall` step is needed because SHA's `Ch` uses `x ^^^ 0xffffffff` for
complement, and the all-ones literal does not reduce under `getElem` on its
own. `revert i; decide` works because `Nat.decidableBallLT` makes
`∀ i < 32, P i` decidable.

---

## 2. `evm_block` — reduce a straight-line block, and the `evmStep` simp set

```lean
register_simp_attr evmStep          -- must live in its own module

syntax "evm_block" (ppSpace colGt term)? : tactic
macro_rules
  | `(tactic| evm_block $h) =>
    `(tactic| simp +arith +decide (maxSteps := 4000000)
        [*, evmStep, stackCap $h])
```

A submission tags its own generated `path`, artifact, instruction list and byte
literal `@[evmStep]`; everything generic is tagged once in `Block.lean`.

**The set has to be complete or the reduction stalls silently.** Besides the
stepper definitions (`runLocatedBlock`, `runLocated`, `runInstr`,
`instructionPC`, `assembleBytes`, `Instr.bytes`, `List.exchange`) it needs:

| lemmas | why |
|---|---|
| `List.length_*`, `List.cons_append`, `List.nil_append`, `List.append_assoc` | the stack-capacity guards |
| `List.getElem?_cons_zero/succ` | `DUP` |
| `List.take_succ_cons`, `List.take_zero`, `List.flatMap_cons/nil` | `instructionPC` |
| `List.set_cons_zero/succ`, `Option.bind_some/none`, `Option.bind_eq_bind`, `Option.pure_def` | `SWAP`, which goes through `List.exchange`, a `do`-block |
| `ite_true`, `ite_false`, `Option.map_some/none` | collapsing the guards so the `match`es reduce |
| `Word.succ_ofNat`, `Word.ofNat_add_ofNat`, `activeWordsAfterUInt256` | folding `pc` and the memory watermark to literals — note `MachineState.activeWordsAfter` must **not** be here, see §7 |
| `Memory.readWord_writeWord`, `Memory.readWord_writeBytes_disjoint` | reading back what the block wrote; other slots undisturbed |

Miss any one and the reduction stops part-way leaving a large opaque term. The
symptom is always the same, so **`trace_state` immediately after the tactic is
the first debugging move**, and the residual term names the missing lemma.

**Anti-result worth recording.** The obvious optimization — stage 1 `simp only`
for the machine, stage 2 `simp` for the arithmetic — is *slower* (7 s vs 6 s)
once `evmStep` is complete. The win came from giving one `simp` the right
lemmas, not from staging it. Net effect of completing the set: 32 s → 6 s per
63-instruction block.

---

## 3. `stackCap` — one conditional rewrite for every capacity guard

```lean
theorem stackCap {α : Type _} {l : List α} {n : Nat}
    (h : l.length < 1000) (hn : 1000 ≤ n) : (l.length ≤ n) = True
```

Every `runInstr` guards on `stack.length < 1024`. `simp` normalises those to
`rest.length ≤ N` for a literal `N` that depends on how many temporaries are
live at that instruction, so a single `rest.length < 1000` hypothesis does not
discharge them and enumerating two dozen `have`s is both ugly and fragile.
This one conditional rewrite covers all of them, with simp's own discharger
settling `1000 ≤ N`.

---

## 4. `runLocatedBlock_append` — composing blocks

```lean
theorem runLocatedBlock_append (p q : List (Located artifact fork)) {s m t : State}
    (hp : runLocatedBlock p s = some m) (hm : m.halt = .Running)
    (hq : runLocatedBlock q m = some t) :
    runLocatedBlock (p ++ q) s = some t
```

`runLocatedBlock` special-cases its *final* instruction — it does not require
the machine to still be `Running` afterwards — so concatenation is not a
monadic bind and this fix-up is needed. Axioms: `[propext, Quot.sound]`.

---

## 5. The `toUInt32` homomorphism *is* lazy masking

The single most useful idea in the development. The artifact deliberately
leaves garbage above bit 31 in every intermediate, because `ADD` carries only
upward and a later `& 0xffffffff` erases it. Formally that is exactly the
statement that the low-32-bit projection commutes with `+`, `&&&`, `|||`,
`^^^` and absorbs the mask. As `@[simp]` lemmas, a round's raw EVM expression
collapses to the SHA expression *automatically*, and **no intermediate masking
obligation is ever generated**. The gas optimization pays for itself twice.

`Challenge/EvmProof/Word.lean` already had `mask32_add_left/right`,
`mask32_xor`, `evm_rotr32`; this work adds `toUInt32_land`, `toUInt32_mask32`,
`toUInt32_xor'`, `toUInt32_land'`, `toUInt32_dbl`, `toUInt32_ofNat`,
`land_maskLit`, `dbl_fold`.

---

## 6. Rotation by doubling, as two lemmas with disjoint side conditions

```lean
@[simp] toUInt32_shiftRight_dbl      (0 < n) (n < 32)  : … = rotr32 w n
@[simp] toUInt32_shiftRight_dbl_high (32 ≤ n) (n < 64) : … = shr32 w (n - 32)
```

Same left-hand side, disjoint side conditions, so simp discharges the
condition and picks the right one. This is what lets `σ0`/`σ1` read their two
rotations *and* their plain shift off the same doubled word with no case
analysis in the caller. Preferring this to an `if`-valued right-hand side keeps
the lemmas usable by `simp`.

Underneath is one Nat fact, `nat_dbl_shiftRight`, which reuses Lean core's
`Nat.shiftLeft_add_eq_or_of_lt` for the disjoint-or-is-add step.

---

## 7. Pinning the memory watermark — worth an order of magnitude

The single most valuable performance fact in the development.

When a block addresses memory at *literal* offsets, `activeWordsAfter` folds to
a literal and costs nothing. When a loop body addresses memory off a *stack
pointer*, every address is symbolic (`ofNat 384 + q`), the watermark stays an
unreduced `max` over `q`, and it nests again at every `MLOAD` — so simp drags
a growing symbolic term through the whole block. Measured on one round block:
**>25 min (killed) unpinned, 1 min 37 s pinned.**

The fix has three parts, and all three are needed:

```lean
-- 1. a collapse lemma
@[evmStep] theorem activeWordsAfter_pin {off : Nat} (h : off + 32 ≤ 4480) :
    MachineState.activeWordsAfter 140 off 32 = 140 := by
  unfold EvmSemantics.MachineState.activeWordsAfter
  split
  · omega
  · show Nat.max 140 ((off + 32 - 1) / 32 + 1) = 140
    exact Nat.max_eq_left (by omega)

-- 2. the address bound as a generated hypothesis, in the *exact* syntactic
--    form the guard takes, so simp's discharger can use it directly
(hbw : (UInt256.ofNat 384 + q).toNat + 32 ≤ 4480)

-- 3. REMOVE `MachineState.activeWordsAfter` from the unfolding set, or the
--    definition unfolds before the lemma can match
```

The premise — that the artifact's memory footprint is constant, so the
watermark is a literal throughout — is a property of the *implementation*
(here, the driver's K-table initialisation touches the highest address there
is). Verify it empirically before assuming it; a one-line instrumented run of
the interpreter over every test input is enough.

Note the shape of the win: after pinning, the watermark component of the end
state is closed by `ac_rfl` alone, with the `omega` fallbacks never executing.
The lemma does the work *inside* the block reduction instead of leaving
arithmetic for the caller — which is the general reason to prefer a collapse
lemma over a post-hoc arithmetic tactic.

## 8. Practical traps

**Key lemmas — and block *statements* — on the stepper's operand order, not
the mathematical convention.** The stepper emits `UInt256.land`/`UInt256.xor`,
not the `&&&`/`^^^` notation, and `PUSH k; OP` puts the constant *first*.
Lemmas keyed on the tidy form silently fail to fire — silently being the
problem. The same applies to the *conclusion* of a block lemma: writing a loop
counter update as `q + ofNat 256` when the code computes `ofNat 256 + q` leaves
a stray commutativity goal after an otherwise complete reduction. Read the
operand order off the residual goal and match it; the fix costs nothing and
`word_add_comm` should not be needed at all.

**State block lemmas over opaque input words.** Threading the previous round's
definitions into the next round's goal makes round `t`'s term nest `t` deep and
blows simp's step budget by about round 4. Quantify over fresh `S0..S7` and let
the chain instantiate at `apply`-time; every block proof then stays the same
size regardless of depth.

**Name the whole end state, or blocks will not compose.** A conclusion that
mentions only the stack cannot feed `runLocatedBlock_append`. This became
possible only once `pc` and the memory watermark fold to literals.

**Update at least one shared-state field, or the record will not compare.**
Stating `activeWords := s.activeWords` leaves `{ s with … }` holding an opaque
`s.toSharedState` on the right while the computed left side is an explicit
record, and simp cannot compare them fieldwise. Pin the watermark to the
literal it actually has.

**Never `decide` a jump destination over the whole artifact.**
`Decide.isValidJumpDest bytes 911 = true := by decide` forces evaluation of
`assemble instrs` across the entire instruction list and then a full
jump-destination scan. On a 1,475-instruction artifact this took 107 s on one
run and had not finished after 490 s on another — pathological and, worse,
highly variable. Use the artifact helper instead, which only needs the prefix:

```lean
have h := ProgramArtifact.isValidJumpDest_index art 534 (by rfl)
simpa [art] using h
```

The same caution applies to any `decide` whose subject is the whole artifact
rather than one instruction.

**`{ s with … }` is layout-sensitive** — put `s with` on its own line.

**A reverse rewrite can blow up `whnf`.** `← Nat.shiftLeft_eq` took 45 s and
then timed out at a million heartbeats. State Nat lemmas in `* 2^k` form and
apply `Nat.shiftLeft_eq` forward on a local hypothesis. Found by bisecting the
rewrite chain, which is the right move for a `whnf` timeout because the error
points at the theorem, not the offending rewrite.

**Define the bytecode *as* `assemble instructions`** so `assembly_eq := rfl`.
Proving it against an explicit byte literal by `ByteArray.ext` plus per-byte
`decide` is superlinear and had not finished after 15 minutes at 9,595 bytes.
CI still checks the hex independently by evaluating `bytesToHex`, which is
compiled code and fast.
