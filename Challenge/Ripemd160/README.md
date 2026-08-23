# RIPEMD-160 challenge: audit map

This challenge asks for EVM bytecode that replaces Ethereum's RIPEMD-160
precompile interface. The bundled reference is deliberately split into a
minimal specification, readable Yul, frozen compiled bytes, and a direct EVM
proof so that each trust boundary can be audited independently.

## 1. Minimal specification

[`Spec.lean`](Spec.lean) defines:

- `spec input`: twelve zero bytes followed by the 20-byte RIPEMD-160 digest;
- `CalldataFits input`: the protocol-facing bound `input.size < 2^64`;
- `initialState`: the fixed Osaka EVM frame used to judge candidates; and
- `Correct code`: for every fitting input, all sufficiently large gas budgets
  return exactly `spec input`.

[`YulSpec.lean`](YulSpec.lean) defines the source-level counterpart,
`Challenge.Ripemd160.Yul.Correct`. Both predicates require the same 32-byte
result built from `EvmSemantics.Crypto.Ripemd160.hash`, the implementation used
by the pinned EVM semantics for the `0x03` precompile. These are the two
outer-facing predicates for auditors and candidate proofs; neither imports the
reference implementation, optimizer, compiler, scorer, or proof modules.

The Yul predicate runs programs in the shared closed EVM dialect. External
calls and contract creation are unavailable there, and correctness requires a
real terminating run for every admitted input. A source implementation
therefore cannot delegate RIPEMD-160 to the incumbent `0x03` precompile. The
raw-bytecode specification independently disables `0x03` in its execution
configuration.

Reusable submission-independent reductions live in [`ProofSupport/`](ProofSupport/):
`Bytecode.lean` for direct raw-EVM proofs, `Yul.lean` for the verified-compiler
route, and `InitialState.lean` for facts about the fixed initial frame. Shared
instruction, trace, memory, and gas machinery lives in
[`../EvmProof/`](../EvmProof/).

## 2. Reference source and frozen artifact

[`Reference/reference.yul`](Reference/reference.yul) is a straightforward
RIPEMD-160 implementation. It:

1. initializes the five chaining words and the four 80-entry schedule tables;
2. copies and pads calldata at memory offset `0x800`;
3. decodes each 64-byte block into sixteen little-endian words;
4. executes the 80 left-line and 80 right-line rounds;
5. performs RIPEMD-160's cross-line final combination; and
6. returns twelve zero bytes followed by the five final words little-endian.

Every algorithm word occupies a separate 32-byte EVM memory slot and is
truncated to 32 bits. This is intentionally regular and proof-friendly rather
than gas-optimal.

[`Reference/reference.hex`](Reference/reference.hex) is the frozen 1,671-byte
compiler output. It can be reproduced with:

```sh
lake exe yulc Challenge/Ripemd160/Reference/reference.yul
```

`Reference/Bytes.lean` contains the reducible byte literal,
`Reference/Bytecode.lean` exposes `referenceBytecode`, and
`Reference/Proofs/Bytecode/Artifact.lean` pins every located instruction used
by the execution proof to that exact artifact.

[`Reference/Proofs/Yul.lean`](Reference/Proofs/Yul.lean) separately proves the
fixed source parses, optimizes, compiles, and assembles to the frozen bytes.
Its final compiler-route theorem explicitly requires Yul functional semantics
and an initial-state abstraction. The direct bytecode proof does not rely on
those two premises or on source/compiler correctness.

### Source-Yul proof boundary

Reusable source-proof infrastructure is a sibling of `Challenge.EvmProof`:

- `Challenge/YulProof/Interpreter.lean` projects successful executable Yul
  interpreter computations into the relational big-step semantics;
- `Challenge/YulProof/EvmState.lean` provides common EVM-dialect state
  transformers, bulk stores/copies, word reads, and memory-frame relations.

The files under `Reference/Proofs/Yul/` are RIPEMD-specific: `StateModel`
mirrors this source's fixed tables and exact state transitions, `Procedures`
proves its procedure contracts, `Algorithm` relates its 256-bit expressions
to RIPEMD's 32-bit model, `Driver` maintains the RIPEMD block invariant, and
`Execution` proves this program's padding, serialization, and top-level run.
`Reference/Proofs/Yul.lean` separately pins parsing, normalization,
optimization, compilation, and assembly to the frozen bytecode.

The outward-facing theorem for the actual parsed source is:

```lean
referenceParsedBlock_correct :
  Challenge.Ripemd160.Yul.Correct referenceParsedBlock
```

The direct source proof can be checked with:

```sh
lake build Challenge.Ripemd160.Reference.Proofs.Yul.Execution
lake build Challenge.Ripemd160.Reference.Proofs.Yul
```

## 3. Direct-bytecode proof layout

The proof reuses `Challenge.EvmProof.GasSteps`, located instruction paths,
memory lemmas, and the shared gas potential. The main layers are:

- `Word.lean`, `Functions.lean`, `Compression.lean`, and
  `CompressionCorrect.lean`: 32-bit arithmetic, RIPEMD Boolean functions,
  rounds, and final combination;
- `Padding.lean`, `PaddingTrace.lean`, `PaddedBlockBridge.lean`,
  `SpecBridge.lean`, and `HashSpecBridge.lean`: bytecode padding and the bridge
  from padded blocks to the pinned RIPEMD hash;
- `Schedule.lean`, `ScheduleCorrect.lean`, `TableTrace.lean`,
  `RoundTrace.lean`, and `CompressionTrace.lean`: message scheduling and the
  compiled compression paths;
- `DriverTrace.lean`, `OutputTrace.lean`, and `DirectCorrect.lean`: block-loop
  framing, five-word serialization, `RETURN(0, 32)`, and the complete trace
  around an explicit compression seam;
- `CompressionSeamBridge.lean`: strengthens that seam with the mathematical
  chaining-word invariant;
- `CompressionRunTrace.lean`: iterates the concrete compiled compressor over
  every padded block and maintains the five-word mathematical hash invariant;
- `CompressionActiveWords.lean`: proves the compressor's exact memory
  high-water endpoint;
- `OutputResultBridge.lean`: proves the returned 32 bytes from the five final
  words, with no separate digest-result assumption;
- `CompressionCostTrace.lean`, `CompressionRoundCostTrace.lean`, and
  `CompressionGasIntegration.lean`: prove the schedule and per-iteration
  round gas potentials;
- `Compression80GasTrace.lean`: telescopes those potentials across both
  80-round lines;
- `CompressionGasComposition.lean`: closes the schedule, round, and tail
  potentials over the complete compiled compressor and exports its per-block
  cost fact;
- `InitializationGasTrace.lean`, `PaddingGasTrace.lean`, and
  `OuterGasTrace.lean`: meter initialization, padding, driver framing, and the
  active-memory boundaries outside the compressor;
- `ExactGasBridge.lean`: telescopes those memory potentials into the closed gas
  formula;
- `FinalCorrectness.lean`: packages the reusable run/cost interfaces; and
- `ReferenceCorrect.lean`: installs their concrete proofs and exposes the
  unconditional public theorems.

The umbrella imports are `Reference/Proofs/Bytecode.lean` for the direct EVM
route, `Reference/Proofs.lean` for both the bytecode and Yul routes, and
`Challenge.Ripemd160` for the complete challenge package.

### Final theorems

The direct proof has no remaining hypotheses. Its two public endpoints are:

```lean
ReferenceCorrect.reference_correctWithSchedule :
  GasCost.CorrectWithSchedule referenceBytecode GasCost.referenceGasForSize

ReferenceCorrect.reference_correct : Correct referenceBytecode
```

`ReferenceCorrect` constructs `FinalCorrectness.RemainingFacts` from the
concrete compression run, its per-block potential equation, and the outer
trace. It does **not** assume the returned digest, a whole-program trace, or a
whole-program gas equality: those are derived by the output, direct-trace, and
exact-gas bridges.

## 4. Exact reference gas schedule

For calldata of `n` bytes, let

```text
blocks(n) = floor((n + 72) / 64)
words(n)  = floor((n + 31) / 32)
C_mem(w)  = 3w + floor(w² / 512).
```

The frozen reference consumes:

```text
3877 + 148364 * blocks(n) + 3 * words(n)
     + C_mem(65 + 2 * blocks(n)).
```

[`Reference/Proofs/Bytecode/GasCost.lean`](Reference/Proofs/Bytecode/GasCost.lean)
defines this schedule, proves monotonicity, and kernel-checks representative
values. The 376-byte checkpoint is intentionally included because its seventh
block makes `C_mem(65 + 2 * blocks)` cross a quotient boundary; it therefore
distinguishes the final schedule-load high-water mark from padding's
`64 + 2 * blocks` endpoint. `ExactGasBridge.fullTrace_cost` derives the
whole-trace equality from the two explicit potential interfaces;
`ReferenceCorrect.reference_correctWithSchedule` proves sufficiency of the
displayed schedule.

## 5. Proof hygiene and local checks

The direct-bytecode proof contains no `sorry`, `admit`, source-level `axiom`,
`unsafe`, `opaque`, or `native_decide`: its bounded initialization facts and
concrete gas/path costs are kernel-checked. The separate source/artifact route
retains four `native_decide` checks in `Reference/Proofs/Yul.lean` for parsing,
compilation, and byte-for-byte assembly of the fixed source. Lean records those
four finite checks through a generated axiom, but they are not imported by or
used in `ReferenceCorrect.reference_correct`.

Useful focused builds are:

```sh
lake build Challenge.Ripemd160.Reference.Proofs.Bytecode.ReferenceCorrect
lake build Challenge.Ripemd160.Reference.Proofs.Bytecode
lake build Challenge.Ripemd160.Reference.Proofs.Yul
lake build Challenge.Ripemd160.Reference.Proofs
lake build Challenge.Ripemd160
```

[`Scorer.lean`](Scorer.lean) provides executable vectors and gas measurements.
Those tests are useful falsification evidence, not part of the proof.

Candidate bytecode belongs under [`Submissions/`](Submissions/). The mechanical
file, declaration, proof, and optional gas-schedule contract is documented in
[`SUBMITTING.md`](SUBMITTING.md).

<!-- BEGIN GENERATED RIPEMD160 GAS REPORT -->
## 6. Gas report

Generated by `scripts/report-ripemd160-gas.sh`; CI checks that this section is current.

### Category 1: Tier-1 measured gas

Gas is measured by concrete execution in the pinned EVM semantics. A
single number means the clean and dirty initial states agree; `clean /
dirty` is shown otherwise. The total is the sum across all 17 vectors,
all of which the script checks. Ratios compare those suite totals against
the RIPEMD-160 precompile schedule, `600 + 120 × ceil(bytes / 32)`, and
against the bundled reference. These measurements are tests, not proofs.

| implementation | bytes | empty | abc | 55 bytes | 56 bytes | 64 bytes | 1,000 bytes | all vectors | vs precompile | vs reference |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| [Reference](Reference/) | 1671 | 152450 | 152453 | 152456 | 300827 | 300827 | 2378106 | 9862146 | 419.31× | 1.00× |

### Category 2: proved `CALLDATASIZE` gas bounds

A proved row supplies a symbolic `gasFormula`, its executable
`gasSchedule`, and a kernel-checked `CorrectWithSchedule bytecode
gasSchedule` theorem. The checker requires `gasSchedule = gasFormula.eval`
by definitional equality, then renders the proved function directly as
LaTeX. `calldataSize` is exactly the byte length returned by the EVM
`CALLDATASIZE` opcode. Here
$C_{\mathrm{mem}}(w) = 3w + \lfloor w^2/512 \rfloor$. Every expressible
formula is monotone, so entries are ordered by their worst-case bound at
the largest admissible calldata size, $2^{64}-1$, smallest first.
“Not provided” is not inferred from measurements.

| implementation | proved symbolic bound | proof |
|---|---|---|
| [Reference](Reference/) | $G(\mathrm{CALLDATASIZE}) = 3877 + 148364 \cdot \left\lfloor\frac{\mathrm{CALLDATASIZE} + 72}{64}\right\rfloor + 3 \cdot \left\lfloor\frac{\mathrm{CALLDATASIZE} + 31}{32}\right\rfloor + C_{\mathrm{mem}}\left(65 + 2 \cdot \left\lfloor\frac{\mathrm{CALLDATASIZE} + 72}{64}\right\rfloor\right)$ | [proved](Reference/Proofs/Gas.lean) |

<!-- END GENERATED RIPEMD160 GAS REPORT -->
