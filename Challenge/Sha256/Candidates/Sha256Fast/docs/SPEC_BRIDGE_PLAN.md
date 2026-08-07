# The spec bridge: exact shape of the remaining work

Everything else in this development is generated or mechanical. This is not,
so it is worth specifying precisely before writing it.

## What has to be proved

`Challenge.Sha256.Correct bytecode` unfolds to: from `initialState`, for every
realizable calldata and every sufficiently large gas, execution halts returning
`Crypto.Sha256.hash calldata`. Via `ProofSupport.Bytecode.correct_of_directProof`
that reduces to `DirectProof`, and via `GasSteps.toEventuallyEvaluates` to a
single `GasSteps` from the initial state to a `.returned` state.

The block-level machinery already produces `GasSteps` fragments. What is
missing is the *semantic* identification of what those fragments compute with
what `hash` computes.

## The structural gift

`hash` and the artifact's driver have the same shape, which is not an accident
— the artifact was written this way:

| `hash` | artifact |
|---|---|
| `nFull := bs.size / 64`, absorb each | loop 1 over full calldata blocks |
| build `tail` (1 or 2 blocks) | the `rem < 56` split |
| absorb tail blocks | the same block subroutine |
| `writeBE32` ×8 | the digest epilogue |

So the driver-level argument is a case split matching the spec's own, not a
re-derivation.

## The three lemmas that carry it

### B1. Padding correspondence

Define the padded stream as a function, mirroring the spec's `tail`
construction:

```lean
def padded (bs : ByteArray) : ByteArray   -- bs ++ 0x80 ++ zeros ++ len₆₄
def numBlocks (n : Nat) : Nat := (n + 72) / 64
```

**Claim.** For every block index `i < numBlocks bs.size`, the 64 bytes the
artifact places at `SCR` before its `i`-th call to the block subroutine equal
`(padded bs).extract (64*i) (64*i + 64)`.

Three cases, matching the artifact's three code paths:

* `i < bs.size / 64` — pure `CALLDATACOPY`, no patch. Equal because
  `CALLDATACOPY` copies calldata verbatim and `padded` agrees with `bs` there.
* `i = bs.size / 64` — `CALLDATACOPY` (which zero-extends past `calldatasize`,
  giving the spec's zero padding for free) plus `MSTORE8` of `0x80` at
  `rem`, plus the length write when `rem < 56`.
* `i = bs.size / 64 + 1`, only when `rem ≥ 56` — two zero `MSTORE`s and the
  length write.

**This is the crux.** The zero-extension of `CALLDATACOPY` is doing the spec's
"pad zeros until 56 mod 64" for free, and that equivalence is the single fact
most worth stating carefully. Everything else in B1 is arithmetic on `rem`.

### B2. One block equals `compressBlock`

**Claim.** If memory holds `H` at `HB` and the 64 message bytes at `SCR`, then
after the block subroutine, memory holds `compressBlock H blk 0` at `HB`.

Decomposes into:

* **Schedule.** The W array (stored *doubled*, so the invariant is
  `readWord (WB + 32t) = dbl (ofUInt32 W[t])`) agrees with the spec's `W`
  after all 48 steps. Uses `sched0..7` and the schedule loop invariant.
  Base case `W[0..15]` needs the `readBE32` correspondence with the artifact's
  `shr 224 (mload (SCR + 4j))`.
* **Rounds.** The eight working slots after 64 rounds agree with the spec's
  `a..h`. Uses `round0..7` and the rounds loop invariant. The per-round step is
  already an exact match: the block lemmas conclude in terms of
  `T1 E F G H Kc Wt = H + bigSigma1 E + Ch E F G + Kc + Wt`, which is the
  spec's `T1` verbatim.
* **Folding.** `H[i] := H[i] + working[i]` — the artifact's final eight
  `MLOAD/ADD/AND/MSTORE` groups against the spec's `#[H[0]! + a, …]`.

### B3. Digest output

**Claim.** The epilogue's `or`-of-shifts at `OUT` equals
`writeBE32` applied eight times. Pure `Word` reasoning; the smallest of the
three.

## Assembly

```
B1 + B2  ⟹  after the block loop, H = the spec's H
     B3  ⟹  the returned 32 bytes = hash bs
   then  ⟹  DirectProof ⟹ Correct
```

## Honest assessment of difficulty

B2's *round* half is close to free — the block lemmas were deliberately stated
in the spec's own `T1`/`T2` vocabulary, so the loop invariant is an induction
over an equality that already holds pointwise.

B2's *schedule* half and B3 are moderate: real but routine `Word`-level work.

**B1 is the genuine work**, and within it the `CALLDATACOPY` zero-extension
argument is the part with no precedent elsewhere in this development. It is
also the part where an error would be invisible to testing on the 19 vectors,
because they exercise only a handful of `rem` values — which is precisely the
argument for proving it rather than trusting the fuzzing.

## Why the artifact was shaped to make this tractable

Two choices in the implementation exist for the proof's benefit, and are worth
flagging to a reviewer as deliberate:

* **Constant memory / per-block `CALLDATACOPY`** removes the message buffer
  entirely, so B1 never has to reason about a growing memory region — and it
  is what makes the gas bound memory-free at the same time.
* **The `rem < 56` split mirrors the spec's `while tail.size % 64 ≠ 56`**, so
  the case analysis is shared rather than translated.
