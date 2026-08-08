# EIP-8200 challenges

Write EVM bytecode that replaces a precompile, and prove it.

[EIP-8200](https://eips.ethereum.org/EIPS/eip-8200) proposes replacing native
precompile implementations with ordinary EVM bytecode. This repository hosts
open challenges for producing implementations that are both efficient and
machine-checked against the corresponding function in the pinned EVM
semantics.

## Repository contract

Every challenge defines one small acceptance predicate of the form:

```lean
Correct : ByteArray → Prop
```

A valid candidate contributes concrete bytecode and a Lean theorem proving
`Correct bytecode`. The theorem is checked on the pinned toolchain and may not
depend on `sorry`, `native_decide`, or project-defined axioms. Executable test
vectors are a required falsification check, but they never replace the proof.

Each challenge directory separates:

- `Spec.lean`: the minimal statement an auditor must accept;
- `SUBMITTING.md`: the exact PR layout and required theorem;
- `ProofSupport/`: optional reusable reductions and helper lemmas;
- `AdditionalGoals/`: stronger properties not required by `Correct`;
- `Reference/`: the bundled baseline artifact and its implementation-specific
  proof; and
- `Scorer.lean`: executable testing and gas measurement.

Generic direct-EVM proof infrastructure lives in [`Challenge/EvmProof/`](Challenge/EvmProof/).
It is independent of any particular precompile or challenge specification.

## Active challenges

| challenge | audit map | submission guide |
|---|---|---|
| SHA-256 | [`Challenge/Sha256/README.md`](Challenge/Sha256/README.md) | [`Challenge/Sha256/SUBMITTING.md`](Challenge/Sha256/SUBMITTING.md) |
| MODEXP | [`Challenge/Modexp/README.md`](Challenge/Modexp/README.md) | reference implementation in progress |
| RIPEMD-160 | [`Challenge/Ripemd160/README.md`](Challenge/Ripemd160/README.md) | [`Challenge/Ripemd160/SUBMITTING.md`](Challenge/Ripemd160/SUBMITTING.md) |
| BLAKE2f | [`Challenge/Blake2f/README.md`](Challenge/Blake2f/README.md) | [`Challenge/Blake2f/SUBMITTING.md`](Challenge/Blake2f/SUBMITTING.md) |

## Build and verify

```sh
lake exe cache get
lake build
lake env lean Checks.lean
```

CI additionally checks each contributed candidate using the convention in its
submission guide, freezes reference artifacts, runs challenge scorers, and
verifies that deliberately fake proofs are rejected by the submission checker.

## Independent gas cross-check

The gas figures in the challenge gas reports come from concrete execution in the
pinned Lean semantics. [`foundry/`](foundry/) re-measures the same frozen
bytecode over the same vectors under a production EVM (revm, via Foundry) and
requires exact agreement, so a mispricing in the pinned semantics could not
quietly become a published number. All 45 scored vectors currently agree to the
gas. It also measures the equivalent implementations from
[eth-act/evmification](https://github.com/eth-act/evmification) alongside the
references.

```sh
cd foundry && forge test -vv
```

The cross-check is self-contained: it verifies for itself that the bytecode it
runs is the artifact the Lean theorems cover, and produces no input to the
generated gas tables.

## Trust boundary

Dependencies are pinned in `lakefile.toml`:

- [powdr-labs/evm-semantics](https://github.com/powdr-labs/evm-semantics)
  supplies the EVM execution relation and precompile specifications;
- [powdr-labs/yul-compiler](https://github.com/powdr-labs/yul-compiler)
  supplies an optional verified Yul-to-EVM path.

Challenge specifications import the smallest relevant semantics surface. A
reference implementation, proof helper, compiler, or scorer may depend on a
specification; the specification must not depend on them.

Apache-2.0.
