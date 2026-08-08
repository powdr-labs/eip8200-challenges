# BLAKE2f challenge: audit map

This challenge asks for EVM bytecode replacing the EIP-152 BLAKE2b compression
precompile at `0x09`. BLAKE2f accepts one fixed 213-byte record containing a
caller-selected 32-bit round count; malformed lengths or final flags fail.

## Specification and reusable support

[`Spec.lean`](Spec.lean) defines the big-endian round parser, exact validity
check, pinned `Crypto.Blake2f.compressBytes` result, fixed Osaka frame, and
`Correct code`. The frame disables precompile address `0x09`, so a candidate
cannot satisfy the statement by delegating to the incumbent implementation.

[`ProofSupport/`](ProofSupport/) contains submission-independent reductions:
`Bytecode.lean` for gas-parametric EVM traces, `Yul.lean` for the verified
compiler route, `Word.lean` for masked 64-bit arithmetic and rotations,
`Input.lean` for the exact EIP-152 decoder and little-endian serializer,
`Memory.lean` for reusable array-at-memory predicates, `Algorithm.lean` for
initialization, rounds, and folding, and `InitialState.lean` for fixed-frame
facts. The symbolic gas language additionally exposes calldata size, parsed
rounds `R`, and final flag `f`.

## Reference source and frozen artifact

[`Reference/reference.yul`](Reference/reference.yul) is deliberately regular:
each 64-bit word occupies one 32-byte memory slot. It validates the wrapper,
parses little-endian words, initializes `v := h || IV`, executes eight `G`
mixes per round through the ten-row sigma table, folds into `h`, and returns
64 little-endian bytes.

The verified compiler emits the frozen 1,169-byte artifact:

```sh
lake exe yulc Challenge/Blake2f/Reference/reference.yul
```

`Reference/Bytes.lean` is the reducible byte literal and
`Reference/Proofs/Bytecode/Artifact.lean` kernel-checks its complete 588
instruction assembly. `Reference/Proofs/Yul.lean` separately certifies parsing,
optimization, compilation, exact assembly, and
`Yul.referenceCompiled_correct : Correct (assemble referenceInstructions)`.
Its finite `native_decide` artifact checks are isolated from the direct
bytecode route; the unconditional correctness theorem for the frozen bytes has
no such dependency.

## Tier 1 and gas gap

```sh
lake exe blake2fchallenge
lake exe blake2fchallenge --hex=path/to/bytecode.hex
```

The suite covers round boundaries `0, 1, 2, 9, 10, 11, 12, 100`, both flag
branches, malformed lengths, and an invalid flag. It runs clean and dirty
states and checks published EIP-152 outputs.

For valid input the frozen reference consumes

```text
29,213 + 3,970 × R + 18 × f gas.
```

Wrong-length input reaches `INVALID` after 57 gas; an invalid flag after 94.
The 13-vector total is 915,772. Over the ten valid vectors the reference uses
915,564 gas while the native round-priced precompile uses 157 gas: a
**5,831.62×** gap.

[`foundry/test/Blake2fGas.t.sol`](../../foundry/test/Blake2fGas.t.sol) runs the
same pinned artifact under revm, agrees with every successful Lean gas number,
and compares output with `0x09` and eth-act's evmification implementation.
Caller-side measurement cannot recover gas spent before `INVALID`, because an
exceptional callee burns all forwarded gas; it checks those cases fail.

## Proof map

`Reference/Proofs/Bytecode/Artifact.lean` pins the instructions,
`Invalid.lean` proves both malformed-input paths reach explicit exceptions and
derives their exact 57/94-gas costs from those traces, and `GasCost.lean`
defines the complete path schedule plus a symbolic sufficient schedule and
proves the latter bounds both exceptional costs. Shared
`INVALID` support was added to `Challenge.EvmProof` for reuse by submissions.

The valid path is split into auditable layers:

- `InitializationCorrectness.lean` and
  `ScalarInitializationCorrectness.lean` refine the compiled memory setup to
  the reusable input and initial-vector models.
- `MixGCorrectness.lean` proves one compiled `G`; `RoundCorrectness.lean`
  lifts that result through the sigma schedule and any 32-bit round count.
- `StoreLE64Correctness.lean` and `OutputCorrectness.lean` prove the fold,
  eight-word serialization, and returned bytes equal `spec input`.
- The corresponding trace/gas modules prove exact block costs and
  `ReferenceCorrect.validGasSteps_cost` composes them.

The final endpoints are:

```lean
ReferenceCorrect.reference_correctWithExactGas :
  CorrectWithSchedule referenceBytecode GasCost.referenceGas

ReferenceCorrect.reference_correctWithSchedule :
  CorrectWithSchedule referenceBytecode GasCost.gasSchedule

ReferenceCorrect.reference_correct : Correct referenceBytecode

Gas.gasSchedule_correct :
  CorrectWithSchedule referenceBytecode Gas.gasSchedule
```

`Checks/Blake2f.lean` freezes the axiom footprint of these functional and gas
theorems. CI builds BLAKE2f in its own challenge job and cache, so its expensive
round proof does not make SHA-256, RIPEMD-160, or MODEXP rebuild.

The direct modules contain no `sorry`, project axiom, `unsafe`, or
`native_decide`. Candidate bytecode belongs under [`Submissions/`](Submissions/)
and follows [`SUBMITTING.md`](SUBMITTING.md).

<!-- BEGIN GENERATED BLAKE2F GAS REPORT -->
## Gas report

Generated by `scripts/report-blake2f-gas.sh`; CI checks that this section is current.

### Category 1: Tier-1 measured gas

Gas is measured by concrete execution in the pinned EVM semantics.
A single number means the clean and dirty frames agree; `clean / dirty`
is shown otherwise. The total covers all 13 public vectors.
The precompile ratio compares the ten valid-vector totals against the
EIP-152 round-priced precompile; exceptional inputs are excluded.
Measurements are tests, not proofs.

| implementation | bytes | R=0, f=0 | R=1 | R=12, f=0 | R=12, f=1 | R=100 | bad length | bad flag | all vectors | valid vs precompile | vs reference |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| [Reference](Reference/) | 1169 | 29213 | 33201 | 76853 | 76871 | 426231 | 57 | 94 | 915772 | 5831.62× | 1.00× |

### Category 2: proved calldata-dependent gas bounds

A proved row supplies a symbolic `gasFormula`, its executable
`gasSchedule`, and a kernel-checked
`CorrectWithSchedule bytecode gasSchedule` theorem. The checker requires
`gasSchedule = gasFormula.eval` definitionally and renders the checked
syntax tree directly. Here `R` is the decoded round count and `f` is the
final-block flag. Rows are ordered by their proved schedules summed over
the public vector suite; this benchmark order is not a claim of global
dominance for every calldata value.

| implementation | proved symbolic bound | proof |
|---|---|---|
| [Reference](Reference/) | $`G(I) = \begin{cases}29213 + 3970 \cdot R + 18 \cdot f,&\mathrm{valid}\\94,&\mathrm{invalid}\end{cases}`$ | [proved](Reference/Proofs/Gas.lean) |

<!-- END GENERATED BLAKE2F GAS REPORT -->
