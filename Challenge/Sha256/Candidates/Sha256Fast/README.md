# Sha256Fast — an optimized SHA-256 for EIP-8200 (work in progress)

> **Status: not a submission.** The bytecode is final, scored, and reproducible
> from source. The correctness proof is partial. This directory is deliberately
> *outside* `Submissions/`, so nothing here asks CI to certify an unfinished
> result — see [Proof status](#proof-status), which separates what a machine has
> checked from what has only been written.

Two artifacts are included. `bytecode.hex` is the proof target; `unrolled.hex`
is the same algorithm with the compression loop fully unrolled, included
because it is measurably faster and because the gap between them is itself the
result that shaped the whole approach.

| | reference | evmification | `bytecode.hex` (loop-of-8) | `unrolled.hex` |
|---|---:|---:|---:|---:|
| 19-vector suite | 10,179,119 | 7,290,263 | **1,404,867** | 1,202,692 |
| vs reference | 1.00× | 1.40× | **7.25×** | 8.46× |
| marginal gas per 64-byte block | ~156,000 | ~112,000 | **21,229** | 18,351 |
| bytes / instructions | 1,524 | — | 2,622 / 1,475 | 9,595 / 6,148 |
| memory used | grows with input | grows with input | **4,480 bytes, always** | 2,432 bytes, always |
| `Correct` proof | bundled | — | **partial** | not attempted |

The marginal figure is the cost of one more 64-byte block, taken from the
256-byte → 1000-byte deltas (5 blocks → 16 blocks). For both artifacts here it
is *exactly* constant — 11 × 21,229 = 233,519 and 11 × 18,351 = 201,861, to the
gas unit. For the reference it is not constant, because its memory grows with
the message and it pays an expansion term that these artifacts do not have at
all.

Both artifacts pass all 19 scored vectors under the pinned Lean semantics, and
both pass 306 fuzzed input lengths against Python's `hashlib`.

---

## Before you run anything: resource warning

**Everything Lean in this repository is memory-hungry, starting with the
repository itself.** On a 62 GB machine, a plain `lake build` fanned out to five
concurrent `lean` workers holding 2.7, 3.4, 3.9, 4.8 and 6.2 GB simultaneously —
over 20 GB for the *repository's own* reference proofs, before any file of this
candidate is touched. A machine with less RAM than that, or one running anything
else substantial, will be OOM-killed rather than told it ran out of memory. Cap
the parallelism:

```sh
lake build -j2 sha256challenge      # instead of a bare `lake build`
```

This candidate's own proof files then add their own requirements, listed
per-file under [Proof status](#proof-status). Two of them have never been run to
completion on the development machine, which is stated there rather than papered
over.

**If you want to check this work without any of that**, use the Python tier
below. It needs no Lean, no toolchain, and finishes in about two minutes.

---

## Reproduce

Three independent tiers, cheapest first. Each is strictly stronger evidence
than the one before it, and each is worth running on its own.

### Tier 1 — Python only, ~2 minutes, no Lean

```sh
cd Challenge/Sha256/Candidates/Sha256Fast/generators
python3 validate_ref.py     # calibrate: the mini-EVM's gas model against
                            # the reference's published gas
python3 run2.py sha256gen4  # loop-of-8: regenerate, 19 vectors + 306 fuzzed lengths
python3 run2.py sha256gen3  # unrolled:  regenerate, 19 vectors + 306 fuzzed lengths
```

`validate_ref.py` is the reason the other two are trustworthy: it runs the
bundled reference artifact in the same Python mini-EVM and reproduces the gas
this repository publishes for it, `delta=0` on every vector. A gas model that
reproduces someone else's numbers exactly is one you can quote your own numbers
from.

`run2.py` regenerates the artifact from its generator, so it also checks that
the committed `.hex` really is what the committed source emits — the hex files
are outputs, not hand-maintained data.

Expected tail of each run:

```
ALL OK                                                  # validate_ref.py
TOTAL   gas=  1404867 ref= 10179119   7.25x             # sha256gen4
fuzz clean | vectors correct
TOTAL   gas=  1202692 ref= 10179119   8.46x             # sha256gen3
fuzz clean | vectors correct
```

### Tier 2 — the repository's own scorer, pinned Lean semantics

This replaces the Python mini-EVM with this repository's executable EVM
semantics, which is the authority for the leaderboard.

```sh
lake build -j2 sha256challenge      # see the resource warning above
lake exe sha256challenge --hex=Challenge/Sha256/Candidates/Sha256Fast/bytecode.hex
lake exe sha256challenge --hex=Challenge/Sha256/Candidates/Sha256Fast/unrolled.hex
```

### Tier 3 — the proof development

```sh
Challenge/Sha256/Candidates/Sha256Fast/verify.sh          # checked tier only
Challenge/Sha256/Candidates/Sha256Fast/verify.sh --heavy  # adds the two unfinished files
```

`verify.sh` with no arguments runs only the part that has been observed to pass,
and gates it on the axiom footprint. `--heavy` additionally attempts the two
files that have not completed here; read the header of `verify.sh` for the
resource caps before running it.

---

## What makes it fast

**Rotation by doubling.** For a 32-bit `x`, the 64-bit value `X = x·(2³²+1)`
holds two copies of `x` side by side. Then `X >> n` is `rotr(x, n)` in the low
32 bits for `n < 32`, and *exactly* `x >> (n−32)` for `32 ≤ n < 64`. So every
term of every Σ and σ — rotations and plain shifts alike — becomes one right
shift of one value, and a three-way Σ is one `MUL` plus three chained `SHR`s
instead of three `SHR`/`SHL`/`OR`/`AND` groups. This is the single largest win.

**Lazy masking.** Bits above position 31 are garbage that a later
`& 0xffffffff` discards, and `ADD` carries only upward, so no Σ, σ, `Ch`, `Maj`,
or partial sum is ever masked. The only two masks per round are on the new `a`
and the new `e`, which must be exactly 32 bits because they feed a doubling in
the next round.

**Eight fixed stack slots with rotating roles.** A round overwrites exactly the
two variables that die in it — `h`, consumed by `T1`, and `d`, consumed by the
new `e` — and then the *roles* shift by one. There is no per-round stack
shuffling, and the slot↔variable map returns to the identity after eight
rounds, which is also what makes an eight-round loop body well-formed.

**Constant memory.** Blocks are pulled one at a time out of calldata with
`CALLDATACOPY`, which zero-extends past the end of the input for free, so FIPS
padding needs no message buffer at all. Memory is a fixed 4,480 bytes for every
input, which removes the quadratic memory-expansion term from the gas picture
entirely — that is why the marginal per-block cost above is exactly constant,
and it matters even more for the proved-bound leaderboard, which orders by the
worst case at `CALLDATASIZE = 2⁶⁴−1`.

The full derivation, including where the two baselines spend their gas, is in
[`docs/FINDINGS.md`](docs/FINDINGS.md).

---

## Methodology: how the work was structured

The organising decision was to treat *proof cost as an engineering quantity* —
something to measure, model, and design against, exactly like gas. Everything
below follows from that.

### 1. Generate everything from one model

Nothing here was written by hand twice. A single Python description of the
machine emits the EVM bytecode (`generators/sha256gen4.py`,
`generators/sha256gen3.py`), predicts its gas (`generators/evm.py`), *and* emits
the Lean proof obligations for the blocks it just emitted
(`generators/emit_rounds.py`, `emit_loop.py`, `emit_iter.py`,
`emit_sched_iter.py`). The artifact and the statements proved about it cannot
drift apart, because one program produces both. The unroll factor is a generator
parameter, which is what made the central design question answerable by
experiment instead of taste.

### 2. Falsify cheaply before proving expensively

Three tiers with three orders of magnitude between them:

| tier | tool | cost | catches |
|---|---|---|---|
| 1 | Python mini-EVM, 19 vectors + 306 fuzzed lengths | seconds | logic and padding errors |
| 2 | this repository's pinned Lean scorer | minutes | disagreement with the real semantics |
| 3 | Lean proof | hours | everything the vectors do not exercise |

The mini-EVM is only credible because it is *calibrated*: it reproduces the
reference implementation's published gas exactly (`validate_ref.py`), so a gas
number from tier 1 survives contact with tier 2. Nothing was given proof effort
until it had survived the tiers below.

### 3. One tactic, many shapes

The proof rests on a single reduction — `evm_block`, a well-equipped `simp` that
takes a whole straight-line basic block of EVM bytecode to a statement about the
end state — plus one composition lemma, `runLocatedBlock_append`. Three
non-obvious things had to be true for that to work at all:

- **The bytecode must be *defined as* `assemble instructions`,** so that
  agreement with the byte artifact is `rfl`. Proving it against an explicit byte
  literal is super-linear and did not finish in 15 minutes at 9,595 bytes.
- **The simp set has to be complete,** including all the List/Option/`ite`
  computation lemmas; missing any one stalls the reduction mid-block with a
  large opaque term rather than failing. Tuning this took a block from 32 s to
  6 s.
- **Block lemmas must quantify over opaque input words.** Threading round `t`'s
  definitions into round `t+1`'s goal makes the term nest `t` deep and exhausts
  simp around round 4. Quantifying over fresh `S0..S7` and instantiating at
  `apply`-time keeps every block proof the same size regardless of depth.

The eight-fold symmetry of the algorithm then does the rest: because the
slot↔variable map is the identity after eight rounds, **sixteen block lemmas
cover all sixty-four rounds and all forty-eight schedule steps.**

### 4. The same idea pays twice

Lazy masking is the largest source of *gas* savings, and it is also what makes
the proof small: "the bits above 31 are garbage" is formally the statement that
`toUInt32` is a homomorphism, which is what lets a round's raw EVM expression
collapse into the specification's own `T1`/`T2` vocabulary with no masking
obligations ever generated. The optimization and its proof are the same
observation stated twice.

### 5. Measure the cost model, and publish where it broke

The choice between the two artifacts was made by measurement, not preference.
Chained round blocks were timed at 2, 4 and 8 rounds (16 s, 38 s, 197 s),
fitting cost ≈ (number of block theorems) × (artifact size) with a superlinear
term whose cause is identifiable in the toolkit: `instructionPC i` and
`instructions[i]` are each `O(i)` and evaluated once per instruction. That model
said: unrolled ≈ 9 hours, loop ≈ minutes. **Take the 15% gas loss for the
finishable proof.**

Then the model broke. The first loop block lemma ran 25 minutes without
completing, because the loop addresses `W` and `K` off a *stack pointer*, so
every address is symbolic and the memory watermark stays an unreduced `max` that
nests at every `MLOAD`. Pinning the watermark to a literal — sound, because the
driver holds `activeWords` at exactly 140 words for the entire run — took the
same block to 1 m 37 s. That is a ~15× effect the model had no term for, and
[`docs/PROOF_COST.md`](docs/PROOF_COST.md) records it as a correction rather
than quietly restating the conclusion. One further cost question, at the
composition layer, is still open and is flagged there as open.

### 6. Axiom hygiene as a constraint from day one, not an audit at the end

This challenge admits only `propext`, `Classical.choice`, and `Quot.sound`. The
obvious tool for 32-bit bitwise identities, `bv_decide`, silently adds a
`._native.bv_decide.ax_N` axiom to the transitive footprint; `native_decide` adds
`Lean.ofReduceBool`. Both are therefore unusable *no matter how convenient*, and
the working rule became: `#print axioms` a new tactic before building anything on
it. The replacement is `bit_blast32` in `proofs/Sha256Fast/Word.lean` — bit
extensionality through `UInt32.toBitVec`, then `grind` on the resulting Boolean
goal — which closes `Ch`, `Maj` and their relatives in well under a second. The
footprint is checked mechanically by `verify.sh`, not asserted here.

### 7. Split the files so the expensive part is paid once

`Rounds8.lean` elaborates the sixteen block lemmas and produces a 447 MB
`.olean` in about 15 minutes. `IterSteps.lean` imports that artifact rather than
re-elaborating it, so composition work recompiles against a finished object.
This is also why the two remaining files are the resource problem: they sit
downstream of a very large import.

---

## Proof status

The decomposition follows the one suggested in
[`SUBMITTING.md`](../../SUBMITTING.md): straight-line blocks via the executable
stepper, composed with `runLocatedBlock_append`, aiming at `DirectProof` and
then `correct_of_directProof`.

### Machine-checked here, axiom-clean

`propext`, `Classical.choice`, `Quot.sound` and nothing else. Re-checkable with
`verify.sh`; the timings are from this development machine.

| layer | file | contents | observed cost |
|---|---|---|---|
| 32-bit words | `proofs/Sha256Fast/Word.lean` | `toUInt32` as a homomorphism — lazy masking stated formally; `bit_blast32` | seconds |
| block machinery | `proofs/Sha256Fast/Block.lean` | the `evm_block` simp set, `stackCap`, `runLocatedBlock_append`, watermark pinning, pointer-relative read-over-write | seconds |
| block lemmas | `proofs/Rounds8.lean` | the 8 round shapes and 8 schedule shapes of the loop body, plus loop control | **15 m 29 s**, 0 errors, 447 MB `.olean` |

### Written and sorry-free, but **not yet machine-checked**

These two files contain no `sorry` and no `axiom`, and their statements are the
intended ones — but **neither has ever been elaborated to completion on the
development machine**, so nothing here should be counted as proved. Both attempts
ended in resource exhaustion, not in an error.

| file | statement | status |
|---|---|---|
| `proofs/IterSteps.lean` | `iter_continue` — one full eight-round loop iteration, blocks chained | started, has not completed; no `.olean` produced |
| `proofs/SchedIter.lean` | `sched_iter_continue` — one full eight-step schedule iteration, proved as a single block (the per-step lemmas do not compose: steps are memory-coupled through `W`) | started, has not completed; no `.olean` produced |

Consequently `AxCheck.lean` and `AxCheckSched.lean`, which `#print axioms` these
two results, have never produced output either — **the axiom footprint of the
iteration layer is unverified**, and the table above deliberately does not
include it.

A related measurement in [`docs/PROOF_COST.md`](docs/PROOF_COST.md) is the best
current evidence about why: an earlier, monolithic version of the composition was
still running at 47 minutes, which is disproportionate to the ~11 minutes its
constituent blocks cost. Whether composition is superlinear in the number of
chained blocks is the open question flagged there, and it is the one thing a
reviewer with a larger machine could settle quickly.

### Not written

In dependency order:

1. lifting the two iteration lemmas over their loops with `iterateBounded`
   (`Challenge/EvmProof/Gas.lean`);
2. `W[0..15]` extraction and the `H` load/update blocks — mechanical, the
   emitters exist;
3. the block-subroutine call/return seam;
4. the driver: prologue, block loop, the `rem < 56` tail split, digest epilogue;
5. the semantic bridge to `Crypto.Sha256.hash` — the real remaining work,
   decomposed and difficulty-graded in
   [`docs/SPEC_BRIDGE_PLAN.md`](docs/SPEC_BRIDGE_PLAN.md). Its crux is that
   `CALLDATACOPY`'s zero-extension implements the specification's zero padding;
   that argument is also the one thing the vectors cannot adequately test, since
   they exercise only a few values of `rem`;
6. `DirectProof` → `Correct`, and moving this directory into
   `Submissions/Sha256Fast/`.

Testing is not proof, and nothing in this directory claims otherwise.

---

## Layout

```
bytecode.hex          loop-of-8 artifact, the proof target (one line, no 0x)
unrolled.hex          fully unrolled artifact, measured-gas ceiling
verify.sh             re-checks the proof development; --heavy adds the
                      two files that have not completed here
proofs/               the Lean development (checked by verify.sh, not by CI —
                      see the resource warning)
generators/           Python: artifact generators, proof-obligation emitters,
                      mini-EVM, vector and fuzz harnesses
docs/                 FINDINGS (gas derivation), PROOF_COST (measurements and
                      one corrected model), SPEC_BRIDGE_PLAN (remaining work),
                      TECHNIQUES (the traps, each with the experiment behind it)
```

Provenance: the artifacts are emitted by `generators/sha256gen4.py` (loop) and
`generators/sha256gen3.py` (unrolled); the Lean block-lemma files are emitted by
the `generators/emit_*.py` scripts and then hand-finished. Nothing was compiled
from Yul or Solidity.

## Where help is most useful

1. **Elaborate `IterSteps.lean` and `SchedIter.lean` on a larger machine** and
   report the wall-clock and peak RSS. That converts the second table above into
   the first one and settles the open composition-cost question.
2. **Review [`docs/SPEC_BRIDGE_PLAN.md`](docs/SPEC_BRIDGE_PLAN.md)**, in
   particular lemma B1, the padding correspondence. It is the part where an
   error would be invisible to every test in this directory.
3. **Tell us where a work-in-progress candidate should live.** This directory
   sits outside `Submissions/` on purpose, because the submission checker
   rightly requires a finished `correct` theorem there. If the repository would
   rather host unfinished candidates somewhere else, or not at all, say so and
   it moves.
