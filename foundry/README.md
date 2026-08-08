# Independent gas cross-check

The gas numbers in the challenge READMEs are produced by concrete execution in
the pinned Lean EVM semantics. This directory re-derives them with a completely
separate EVM — the revm implementation inside Foundry — running the same frozen
bytecode over the same vectors, and asserts exact agreement.

Nothing here is part of any proof, and nothing here feeds the generated README
gas tables. It is a falsification check on the published measurements: if the
pinned semantics ever mispriced an opcode, charged memory expansion wrongly, or
disagreed with a production EVM about a fork rule, the numbers in this
repository would be wrong in a way no Lean-side test could reveal.

```sh
cd foundry
forge test        # summary
forge test -vv    # with the comparison tables
```

## Result

Every successful scored vector agrees to the gas. Suite totals:

| challenge | vectors | reference (Lean scorer) | reference (revm) | delta |
|---|---:|---:|---:|---:|
| RIPEMD-160 | 17 | 9,862,146 | 9,862,146 | 0 |
| SHA-256 | 19 | 10,179,119 | 10,179,119 | 0 |
| MODEXP | 9 | 19,046,904 | 19,046,904 | 0 |
| BLAKE2f (valid) | 10 | 915,564 | 915,564 | 0 |

The `vs precompile` ratios the READMEs publish reproduce exactly as well:
419.31× for RIPEMD-160, 4199.31× for SHA-256, 1633.53× for MODEXP, and
5831.62× for BLAKE2f's valid vectors. For MODEXP
the check goes one step further and compares the pinned semantics' own
Osaka/EIP-7883 precompile pricing against revm's, tuple by tuple; those agree
too, including the 500-gas floor and the 4,080 charged for the EIP-198 examples.

So the published gas measurements hold up. What was worth checking is the
methodology, and it survived: see [Measurement](#measurement) for why the
naive way of measuring this is off by a small constant, and
[`test/GasProbe.t.sol`](test/GasProbe.t.sol) for the controls that catch it.

## Comparison with eth-act/evmification

[eth-act/evmification](https://github.com/eth-act/evmification) implements the
same precompiles in optimized Solidity. Its `*Deployed` contracts take raw
calldata and return the precompile's exact output bytes, so they are measured
through the identical probe on the identical vectors. Suite totals:

| challenge | reference | evmification | precompile | reference ÷ evmification | reference ÷ precompile | evmification ÷ precompile |
|---|---:|---:|---:|---:|---:|---:|
| RIPEMD-160 | 9,862,146 | 6,597,217 | 23,520 | 1.49× | 419.31× | 280.49× |
| SHA-256 | 10,179,119 | 7,290,263 | 2,424 | 1.40× | 4199.31× | 3007.53× |
| MODEXP | 19,046,904 | 98,126 | 11,660 | 194× | 1633.53× | 8.42× |

For the two hash functions the bundled references cost about 1.4–1.5× the
hand-optimized Solidity, which is the expected price of a deliberately regular,
proof-friendly shape: one 32-byte memory slot per algorithm word, no packing,
no reuse. Against the precompiles, though, both are in a different regime
entirely: the hash precompiles are priced per 32-byte word (`600 + 120 × ceil`,
`60 + 12 × ceil`), so even optimized EVM code lands two to three orders of
magnitude above them, and no vector comes close.

MODEXP is where the comparison becomes interesting, because that precompile is
priced by operand size rather than by word count and carries a 500-gas
EIP-7883 floor. On four of the nine vectors evmification is *cheaper* than the
precompile's own price — 349 gas against 500 for the empty tuple, the
zero-modulus, and the zero-modulus-size cases, and 395 against 500 for the zero
exponent. The suite ratio of 8.42× is carried almost entirely by the two EIP-198
examples (32,350 against 4,080) and the wide-modulus tuple. Each comparison test
reports this count directly:

```
evmification at or below the precompile's price on 4 of 9 vectors    (MODEXP)
evmification at or below the precompile's price on 0 of 17 vectors   (RIPEMD-160)
evmification at or below the precompile's price on 0 of 19 vectors   (SHA-256)
```

MODEXP is a different story, and the gap is concentrated in one vector. The
257-bit-modulus tuple costs 18,958,693 gas in the reference against 28,843 in
evmification — a factor of 657, and 99.5% of the reference's suite total. The
reference falls off its `MULMOD` fast path as soon as the modulus exceeds 32
bytes and switches to a schoolbook 32-limb fallback sized for the whole
1024-byte domain, while evmification uses Montgomery/Barrett arithmetic. Both
return the same bytes on all nine vectors; the fallback is simply not written
for speed.

None of this is a defect in the published numbers. It is what the numbers mean.

The evmification gas figures are reported, not asserted. Its output is required
to equal the precompile's on every vector, but pinning a third party's gas would
turn a submodule bump into an unrelated test failure. Only the reference's gas,
which this repository publishes, is asserted.

### Additional implementations

[eth-act/evmification](https://github.com/eth-act/evmification/tree/main/src)
also implements `identity` (`0x04`), `blake2f` (`0x09`), `point_eval` (`0x0a`),
and the BLS12-381 family (`0x0b`–`0x11`). BLAKE2f is now included: its ten
valid vectors return identical bytes in the reference, native precompile, and
evmification contract; all three malformed vectors must also fail.

## Measurement

Each `Scorer.lean` reports `start.gasAvailable - final.gasAvailable` for a frame
that runs the candidate bytecode with the vector as calldata: the frame's own
consumption, memory expansion included, with no intrinsic transaction cost, no
calldata byte cost, and no charge for the instruction that enters the frame.

Reproducing exactly that quantity from inside the EVM takes some care, because
reading `gas()` around a `STATICCALL` also captures the call instruction's cost
and the surrounding stack traffic. [`src/GasProbe.sol`](src/GasProbe.sol)
subtracts that overhead rather than estimating it: it makes a second, identical
call to an address holding a single `STOP` — a frame that consumes exactly zero
gas — and takes the difference.

Two details matter more than they look, and both were caught by the controls
rather than by reasoning:

- **One call site, not two.** The calibration and the measurement are the same
  `STATICCALL` instruction executed twice by a two-iteration loop. Written as
  two separate calls, the compiler set up the stack differently for a constant
  target than for a variable one, and the resulting 3-gas asymmetry landed
  directly in every reported number.
- **Warming that survives the optimizer.** Both targets are warmed with
  `EXTCODESIZE` before the loop so each call is the warm 100-gas case
  regardless of what earlier calls touched (EIP-2929). An `EXTCODESIZE` whose
  result is discarded is dead code, and via-IR removed it — leaving a 2,500-gas
  cold/warm difference between calibration and measurement. The result is now
  compared against a value `EXTCODESIZE` cannot return, so it cannot be dropped.

[`test/GasProbe.t.sol`](test/GasProbe.t.sol) is what makes the probe
trustworthy: it measures the `0x02` and `0x03` precompiles, whose gas schedules
are fixed by protocol in closed form, and requires the results to match
`60 + 12 × ceil(n/32)` and `600 + 120 × ceil(n/32)` exactly across seven input
sizes. Any offset or scaling error in the probe fails those assertions before it
can reach a reported number.

## Testing the same artifact the proofs cover

A gas measurement is only interesting if it measures the bytecode the Lean
theorems are about, and reading `reference.hex` alone would not establish that.
The proofs do not target that file: `Bytecode.lean` defines
`referenceBytecode := referenceBytes`, and `referenceBytes` is the byte literal
written out in `Bytes.lean`, so `Correct referenceBytecode` is a statement about
the literal.

[`src/LeanArtifact.sol`](src/LeanArtifact.sol) closes that gap without leaving
Foundry. Before any measurement runs, it reads all three artifacts from the
challenge directory and requires them to agree:

- `reference.hex`, parsed into the bytes that get etched and executed;
- `Bytes.lean`, parsed by walking every `abbrev referenceChunk<N>` literal and
  concatenating the chunks in the order the `referenceBytes` body concatenates
  them — which must equal the hex file byte for byte;
- `Bytecode.lean`, which must still define `referenceBytecode` as
  `referenceBytes` and still `include_str "reference.hex"`; and
- the sizes proved by `referenceBytes_size` and `referenceBytecode_size`, which
  must equal the loaded length.

A regenerated hex file, an edited literal, a renamed definition, or a reordered
concatenation fails the load, so no gas number can be reported for bytes the
proof does not cover. [`test/LeanArtifact.t.sol`](test/LeanArtifact.t.sol)
demonstrates each of those rejections against deliberately corrupted copies,
plus the control that an untouched copy still loads.

The artifact then runs at address `0x8200`, the `deployAddress` each `Spec.lean`
fixes, under `evm_version = "osaka"`, the fork each `initialState` fixes.

## Layout

| path | contents |
|---|---|
| [`src/GasProbe.sol`](src/GasProbe.sol) | exact frame-gas measurement |
| [`src/LeanArtifact.sol`](src/LeanArtifact.sol) | artifact loading and provenance |
| [`src/Vectors.sol`](src/Vectors.sol) | the scorers' vector generators, in Solidity |
| [`test/GasProbe.t.sol`](test/GasProbe.t.sol) | probe controls against known schedules |
| [`test/LeanArtifact.t.sol`](test/LeanArtifact.t.sol) | provenance negative controls |
| [`test/GasCrossCheck.sol`](test/GasCrossCheck.sol) | shared scaffolding and report formatting |
| `test/{Ripemd160,Sha256,Modexp}Gas.t.sol` | per-challenge vectors, Lean numbers, assertions |

The vectors are regenerated in Solidity from the definitions in each
`Scorer.lean` rather than exported from Lean, and every generated vector's byte
length is asserted, so a drifted generator fails instead of quietly changing a
gas number. The Lean-reported gas is recorded as constants: this suite never
recomputes it, which is what keeps the comparison between two independent
implementations of the EVM's gas rules instead of two runs of one.

Both dependencies are pinned submodules, and CI pins Foundry itself to a fixed
release — an exact-equality gas assertion is only reproducible against a fixed
revm, so a toolchain bump should be a deliberate change with its own diff.

## Updating the recorded numbers

The Lean-side gas belongs to the scorers, and it appears here only as the
expected value. When a reference artifact changes, the scorers produce the new
numbers:

```sh
lake exe ripemd160challenge   # or sha256challenge, modexpchallenge
```

Copy the per-vector gas into the corresponding `cases.push(...)` line and the
suite total into the `README suite total` assertion. A mismatch between this
suite and the scorers is the finding, so the numbers are meant to be updated
deliberately, never auto-synchronized.
