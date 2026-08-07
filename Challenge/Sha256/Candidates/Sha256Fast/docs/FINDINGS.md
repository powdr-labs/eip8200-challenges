# SHA-256 for EIP-8200: where the gas goes and how to get it back

> **What this document is.** The gas derivation, written while the artifacts
> were being designed. The gas numbers in it are current and reproducible
> (`generators/run2.py`). Its *proof-cost* estimates are the original ones and
> two of them were later falsified by measurement — read
> [`PROOF_COST.md`](PROOF_COST.md) for the corrected figures, and the README
> for what is actually proved today. Where this file names `fast.hex` and
> `fast_loop.hex`, the shipped artifacts are `unrolled.hex` and `bytecode.hex`
> respectively.

## Two artifacts

| | reference | evmification | `fast.hex` | `fast_loop.hex` |
|---|---:|---:|---:|---:|
| 19-vector suite | 10,179,119 | 7,290,263 | 1,202,692 | 1,404,867 |
| vs reference | 1.00x | 1.40x | **8.46x** | **7.25x** |
| gas per block | ~156,000 | ~112,000 | 18,351 | 21,229 |
| bytes / instructions | 1,524 | — | 9,595 / 6,148 | 2,622 / 1,475 |
| est. proof elaboration | — | — | ~9 h | ~19 min *(withdrawn)* |

Both are confirmed by the pinned Lean scorer and pass 306 fuzzed lengths.
`fast_loop.hex` is the submission candidate: the 15% gas it gives up buys a
proof that is actually finishable, because it needs ~16 block theorems over a
1,475-instruction artifact rather than 112 over 6,148 — and the cost is
(theorems x artifact size), so that is a ~29x reduction.

The "~19 min" cell is struck through because the cost model behind it was
missing a term for symbolic pointer arithmetic, which the loop variant
introduces and the unrolled variant does not. The conclusion — put the proof
on the loop artifact — survived; the number did not. See
[`PROOF_COST.md`](PROOF_COST.md), "Where the model broke".

## Result

A hand-generated artifact (`fast.hex`, 9,595 bytes) that returns the correct
digest on all 19 scored vectors and on 306 fuzzed lengths:

| | reference | evmification | this |
|---|---:|---:|---:|
| 19-vector suite | 10,179,119 | 7,290,263 | **1,202,692** |
| per 64-byte block | 155,996 | ~112,000 | **18,351** |
| vs SHA-256 precompile | 4199× | 3008× | **496×** |
| memory used | grows with input | grows with input | **2,432 bytes, always** |
| code size | 1,524 | — | 9,595 |

8.46× cheaper than the bundled reference, 6.06× cheaper than eth-act/evmification.

Measured in a mini-EVM that reproduces all 19 published reference gas numbers
exactly (`validate_ref.py`), so the gas model agrees with the pinned semantics
on the artifact that repository already publishes.

## Why the existing implementations are slow

Neither baseline is doing anything algorithmically wrong; they both pay
interpretation overhead the EVM charges for literally.

*Reference (`reference.yul`)* — every algorithm word is a 32-byte memory slot,
every accessor (`wAt`, `hSet`, `kAt`, `rotr`) is a real Yul function, so a
round costs ~1,200 gas: six `rotr` calls at ~40 gas of call overhead each,
plus `mul(j, 32)` address arithmetic on every access. This is deliberate — the
file says it is written for provability.

*evmification (`Sha256.sol`)* — keeps `a..h` in stack locals, but `getK(i)` is
a 64-case Yul `switch`, i.e. a linear chain of `EQ`/`JUMPI`. That alone is
~200 gas of average lookup cost per round, 12,800 per block, before anything
else. `rotr32` is still a function.

## The four ideas that matter

**1. Rotation by doubling.**  For 32-bit `x` let `X = x * (2^32 + 1)` — two
copies of `x` side by side. Then for `0 ≤ n < 32`, `X >> n` has `rotr(x, n)`
in its low 32 bits; and for `32 ≤ n < 64`, `X >> n` is *exactly* `x >> (n-32)`.
So every term of every Sigma — rotations and the plain right shifts in σ0/σ1
alike — is a right shift of one value:

```
Σ0(a) = X>>2  ^ X>>13 ^ X>>22        σ0(x) = X>>7  ^ X>>18 ^ X>>35
Σ1(e) = X>>6  ^ X>>11 ^ X>>25        σ1(x) = X>>17 ^ X>>19 ^ X>>42
```

One `MUL` (5 gas) replaces the three `SHL`/`OR`/`AND` groups. With the three
shifts *chained* (`X>>6`, then `>>5`, then `>>14`) a Sigma is 41 gas against
~90 for the naive form. This is the single biggest win and it has no analogue
in the zkgolf/R1CS setting, where rotations were already free relabels.

**2. Lazy masking.**  Bits at position ≥ 32 are garbage that a later
`& 0xffffffff` discards, and ADD only carries *upward*, so garbage in an
addend never reaches the low 32 bits of the sum. No Sigma, σ, Ch, Maj, or
partial sum is ever masked. The only two masks per round are on the new `a`
and new `e`, which must be exactly 32 bits because they feed a doubling next
round. (Ch and Maj stay clean for free: every AND has one clean operand.)

**3. Eight fixed stack slots, rotating roles.**  `a..h` live at eight fixed
stack depths. A round overwrites exactly the two variables that die in it —
`h` (consumed by T1) and `d` (consumed by the new `e`) — and then the *roles*
shift by one. So there is no per-round stack shuffling at all, and the
slot↔variable map is the identity again after eight rounds. Reads are `DUPn`,
writes are `SWAPn; POP`. Max depth reached is 13, comfortably inside `DUP16`.

**4. Constant memory.**  Blocks are pulled one at a time out of calldata with
`CALLDATACOPY`, which zero-extends past the end for free — so the FIPS padding
needs no message buffer: copy the block, `MSTORE8` the `0x80` where it belongs,
`MSTORE` the bit length at `SCR+56`. Memory is 2,432 bytes for *every* input.

Plus: `ch = g ^ (e & (f^g))` and `maj = (a&b) ^ (c & (a^b))` (7 and 9 ops),
W stored pre-doubled so σ skips its MUL, and full unrolling of the 64 rounds
and 48 schedule steps so every W offset and round constant is an immediate.

## Where the gas goes now

Per 64-byte block, 18,351 gas:

| phase | per block | share |
|---|---:|---:|
| 64 compression rounds | 12,224 | 66.5% |
| 48 message-schedule steps | 5,434 | 29.6% |
| W[0..15] from the block | 419 | 2.3% |
| H update + state load | 224 | 1.3% |
| driver / loop / call | 83 | 0.5% |

A round is 191 gas = 63 opcodes: Σ0+Σ1 82, Ch+Maj 48, and 61 for the five
adds, two masks, two slot writes and the W load. Each piece is at or within a
few gas of the floor for its shape, so the remaining headroom in this design
is small — maybe 5%.

## The symbolic gas bound

Gas is exactly

```
528 + 18351 · ⌊(CALLDATASIZE + 72) / 64⌋        (−31 when CALLDATASIZE mod 64 ≥ 56)
```

with **no memory term**. The reference's proved bound is

```
1747 + 155996·⌊(n+72)/64⌋ + 3·⌈(n+31)/32⌉ + C_mem(90 + 2·⌊(n+72)/64⌋)
```

The leaderboard orders the proved-bound category by worst case at
CALLDATASIZE = 2^64−1, where `C_mem` is quadratic in the block count. At that
point the reference's bound is ~6·10^32 and this one is ~5·10^21 — the
constant-memory design wins that ordering by eleven orders of magnitude,
independently of the 8.5× everyone can measure.

## Proof strategy

The good news: the pinned spec `EvmSemantics.Crypto.Sha256.hash` has the same
control flow as this driver — absorb `nFull = size/64` complete blocks from the
input, then build a 1-or-2 block tail with the sentinel and the bit length.
The `rem < 56` split in the bytecode is literally the spec's
`while tail.size % 64 ≠ 56` condition. So the driver-level correctness argument
lines up seam for seam, and the arithmetic lemmas needed are exactly:

- `(x * (2^32+1)) >>> n mod 2^32 = rotr32 x n` for `n < 32`;
- `(x * (2^32+1)) >>> (32+n) = x >>> n`;
- `(u + v) mod 2^32 = (u mod 2^32 + v mod 2^32) mod 2^32` (the lazy-masking
  justification, used everywhere);
- `g ^^^ (e &&& (f ^^^ g)) = Ch e f g` and
  `(a &&& b) ^^^ (c &&& (a ^^^ b)) = Maj a b c`.

The risk: the block body is one straight-line run of ~4,000 instructions.
Symbolically stepping that in Lean may not be tractable. Two mitigations, in
order of preference:

1. **Exploit the eight-fold repetition.** Rounds `t` and `t+8` are
   byte-identical apart from the K and W immediates, so there are only 8
   distinct round shapes. Prove 8 lemmas parameterised by `(K, woff)` and apply
   each 8 times, then compose 112 basic blocks. Keeps full-unroll gas.
2. **Roll the rounds into a loop of 8 iterations over an 8-round body** (the
   permutation is the identity after 8, so this is the natural loop). One body
   lemma plus one invariant. Costs roughly 10–15% gas — K and the W offsets
   stop being immediates — landing near 7.3× instead of 8.5×.

I would build the artifact so the unroll factor is a generator parameter and
decide after trying (1) on a single block.

*Outcome:* both were built, (1) was tried on a single block, and option (2) was
taken — for the reason in [`PROOF_COST.md`](PROOF_COST.md), not the one
predicted here.

## Proof status at the time of writing (see [`TECHNIQUES.md`](TECHNIQUES.md) for the engineering)

*Superseded — the README's "Proof status" section is authoritative. Kept
because it records what was true when the design decision was made.*

The reusable proof layers are built, tuned and axiom-clean
(`propext`, `Classical.choice`, `Quot.sound` only, zero `sorry`):

- `Sha256Fast/Word.lean` — the 32-bit layer. Organising idea: `toUInt32` is a
  homomorphism, and that *is* lazy masking, so the gas optimization also pays
  for itself in proof size.
- `Sha256Fast/Block.lean` — `evm_block`, the `evmStep` simp set, `stackCap`,
  and `runLocatedBlock_append` for chaining blocks.

Verified end to end: a compression round and a message-schedule step both go
from raw bytecode to the FIPS specification; two rounds chain; and all eight
slot permutations (a full cycle) verify with no new lemmas.

Per-block reduction was tuned from 32 s to ~6 s. The remaining bottleneck is
the artifact layer, which is superlinear (`t ∝ n^2.4`) because
`instructionPC i` and `instructions[i]` are each `O(i)` and evaluated once per
instruction. That is what decides full-unroll (8.49×, ~8 h of elaboration)
against loop-of-8 (7.38×, ~7 min *— this second figure is the withdrawn one;
the measured block-lemma set for one compression body came in at ~14 min, and
the composition layer above it is still an open measurement*).
