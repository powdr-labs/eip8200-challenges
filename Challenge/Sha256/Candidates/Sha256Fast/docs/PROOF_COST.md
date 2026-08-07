# Proof cost: what is measured, what is extrapolated, what to re-check

**For the reviewer.** The question "which artifact should carry the proof?" is
answered by measurement here, not by taste. This file records the numbers, the
one place the model broke, and the fix — including a claim that was overstated
and has been corrected.

## Measured: chained blocks against a fully-unrolled artifact

Whole file, warm imports (~2 s of which is imports). All zero errors.

| rounds | block theorems | artifact instructions | time |
|---:|---:|---:|---:|
| 2 | 2 | 126 | ~16 s |
| 4 | 4 | 252 | 38 s |
| 8 | 8 | 504 | 197 s |

Fits `cost ≈ (#block theorems) × (artifact size)`, and the superlinearity in
artifact size has a cause: `ProgramArtifact.instructionPC i` unfolds to
`(assembleBytes (instructions.take i)).length`, and `instructions[i]` indexes a
flat literal list — both `O(i)`, evaluated once per instruction.

## Measured: the cost is not mostly cacheable

Kernel re-check via `leanchecker`:

| module | kernel re-check |
|---|---:|
| `Sha256Fast.Word` | 2.8 s |
| `Sha256Fast.Block` | 3.6 s |
| four round theorems + artifact | 48.5 s |

The round theorems account for ~45 s of kernel time against ~38 s for the whole
elaborate-and-check pass. Elaboration is cached in the `.olean`; **kernel
re-verification is what an auditor re-running `leanchecker` pays again**, and it
is at least the same order.

*Caveat, stated because it limits the claim:* these two numbers are not cleanly
separable with the tools used — `leanchecker` coming out *higher* than the full
pass means it is on a different, less-optimised path. Read the ratio as
"neither dominates", not as a precise split.

## Where the model broke, and the correction

Extrapolating gave fully unrolled ≈ 9 h (112 theorems × 6,148 instructions)
versus loop-of-8 ≈ 19 min (16 × 1,475), which is what motivated the loop.

**The first loop block lemma then ran 25 minutes without completing.** The
model was missing a term. A controlled experiment isolated it — same block,
pointer replaced by a literal:

| loop-of-8 block lemma | result |
|---|---|
| symbolic group pointer `q` | > 25 min, killed |
| pointer pinned to `q = 0` | 2 min 9 s, reduction succeeded |

Cause: the loop bodies address `W` and `K` off a *stack pointer*, so every
address is a symbolic term (`ofNat 384 + q`). Address folding does not fire and
the memory watermark stays an unreduced `max` over `q` that nests at every
`MLOAD`, so simp drags growing symbolic terms through all 96 instructions.

## The fix, validated

Supply the address bound as a generated hypothesis per block, in the exact
syntactic form the guard takes, add a collapse lemma, and *remove*
`MachineState.activeWordsAfter` from `evmStep` so the lemma matches instead of
the definition unfolding:

```lean
@[evmStep] theorem activeWordsAfter_pin {off : Nat} (h : off + 32 ≤ 4480) :
    MachineState.activeWordsAfter 140 off 32 = 140
```

| loop-of-8 block lemma | result |
|---|---|
| symbolic pointer, watermark unpinned | > 25 min, killed |
| symbolic pointer, watermark pinned | **1 min 37 s, zero errors** |

At least 15×, and the watermark component is closed by `ac_rfl` alone — the
`omega` fallbacks never execute — so the lemma collapses the `max` inside
`evm_block` rather than leaving arithmetic for the caller.

The hypothesis is sound because the driver's K-table initialisation pins
`activeWords` to exactly 140 words for the entire run; this was verified
empirically on every input before being assumed. It is discharged once, in the
driver.

**Generalisable lesson:** when a loop body addresses memory off a stack
pointer, the memory watermark is what blows up, and pinning it to a literal is
worth an order of magnitude. This is the single most valuable performance fact
in the development.

## Measured: the whole eight-round loop body

| what | result |
|---|---|
| all 8 loop round blocks, one file | **10 min 15 s, zero errors** |

~75 s per block once the shared artifact cost is amortised, consistent with the
1 min 37 s single-block figure. Adding the 8 schedule blocks (37 instructions
each, against 63 for a round) and the driver puts a full compression body in
the region of **~20 minutes** — which is what the original model predicted
before the watermark problem, and is now measured rather than extrapolated for
the round half.

## Measured: the loop control block

| what | result |
|---|---|
| rounds-loop control tail (backward `JUMPI`) | **1 min 6 s, zero errors** |

This was the last structural unknown in the loop machinery. Three findings came
out of it, all now in `TECHNIQUES.md`: `JUMPI` guards need `lt_isTrue`/
`lt_isFalse` for an `LT`-built condition; a block lemma's *conclusion* must use
the stepper's operand order (`ofNat 256 + q`, not `q + ofNat 256`) or a stray
commutativity goal survives an otherwise complete reduction; and a jump
destination must never be `decide`d over the whole artifact — that ran 107 s
once and had not finished at 490 s on a retry, against 66 s and deterministic
via `ProgramArtifact.isValidJumpDest_index`.

## Measured: the complete block-lemma set for a compression body

| block set | time | errors |
|---|---:|---:|
| 8 round blocks | 10 m 15 s | 0 |
| 8 schedule blocks | 2 m 38 s | 0 |
| loop control block | 1 m 6 s | 0 |
| **total** | **~14 min** | **0** |

Schedule blocks are cheaper than round blocks because they are 37 instructions
against 68. This is the whole per-body block-lemma cost, measured rather than
extrapolated, and it sits inside the ~20 min the model predicted.

## Open measurement: the iteration lemma is disproportionately expensive

> **File names.** `Loop8.lean` and `Iter.lean` below are development files; the
> block lemmas of the former are what ship as `proofs/Rounds8.lean`, and the
> latter was superseded by `proofs/IterSteps.lean`, which imports `Rounds8.olean`
> instead of re-elaborating the blocks. That split was the *response* to the
> measurement in this section. It has not resolved it: `IterSteps.lean` has
> still never been elaborated to completion here, and neither has
> `SchedIter.lean`. Both attempts ended in resource exhaustion rather than in an
> error, so this section remains open, and it is the single most useful thing a
> reviewer with a large machine could close.

`Iter.lean` composes the eight round blocks plus the control tail with eight
nested `runLocatedBlock_append`. The parts cost ~11 min (10 m 15 s for the
round blocks, 1 m 6 s for the control), so ~15-20 min would be the naive
expectation for the whole file. It was **still compiling at 47 min** when this
was written.

Either the composition itself is superlinear in the number of chained blocks —
plausible, since each `runLocatedBlock_append` carries the full intermediate
state through the next application — or the re-emitted blocks are more
expensive in this file's context than they were in `Loop8.lean`.

**This matters for item 3.** If chaining nine blocks costs materially more than
proving them, then lifting eight such iterations with `iterateBounded` needs
the cost measured before committing to the approach, not after. The first
number to get is simply the wall-clock for `Iter.lean` to complete, and then
the same for a two-block and four-block chain to see how it scales.

Note the earlier precedent: the block-lemma cost model was fitted on the
unrolled variant and then broke on the loop variant because of symbolic
addressing. A second cost surprise at the composition layer would fit that
pattern, and the lesson is the same — measure the shape you are actually going
to use.

## Where that leaves the two artifacts

- **Loop-of-8** (`fast_loop.hex`, 7.25×, 1,475 instructions): ~16 block
  theorems at ~1.6 min each. This is the proof target.
- **Fully unrolled** (`fast.hex`, 8.46×, 6,148 instructions): 112 block
  theorems, extrapolated ~9 h. Included as the measured-gas ceiling, not
  proof-carrying.

## What a reviewer should re-check

1. The ~9 h unrolled figure is an extrapolation from 8 rounds to 64. It has
   never been run to completion.
2. The loop figure is measured for all 8 round blocks in one file (10 min
   15 s). The 8 schedule blocks and the driver have not yet been added to that
   file, so the ~20 min body figure still contains one extrapolated step.
3. Neither artifact has a completed `Correct` proof. Machine-checked and
   axiom-clean so far: the 32-bit layer, `runLocatedBlock_append`, and all
   sixteen block lemmas plus loop control. Written but **not** yet elaborated to
   completion anywhere: the two iteration files. Not written: the driver, the
   loop invariant, and the spec bridge. The README's "Proof status" section is
   authoritative and keeps those three categories apart.

Both artifacts are correct *by testing* — 19 scored vectors in the pinned
semantics plus 306 fuzzed lengths — and both gas figures come from
`Challenge/Sha256/Scorer.lean`. Testing is not proof, and nothing here should
be read as claiming otherwise.
