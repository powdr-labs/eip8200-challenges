# BLS12-381 Precompile Challenges Implementation Plan

> **For Claude:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task.

**Goal:** Add shared proof foundations and seven independently auditable EIP-2537 precompile challenges without duplicating BLS12-381 mathematics across challenge directories.

**Architecture:** Generic EVM word-limb and typed-memory facts live under `Challenge.EvmProof`. BLS-only codec, field-tower, projective-curve, scalar-multiplication, and MSM refinement lives under `Challenge.Bls12381.ProofSupport`. Individual challenge trees own only their ABI/spec adapter, concrete artifact, operation-specific refinement, final correctness and gas results, scorer, and submissions. The three subgroup-sensitive challenge specifications remain gated until the pinned semantics implements EIP-2537 subgroup rejection.

**Tech Stack:** Lean 4.31, pinned `evm-semantics`, Mathlib, the existing direct EVM `Stepper`/`GasSteps` infrastructure, Solidity/Foundry for differential testing, and EIP-2537/RFC 9380 vectors.

## Trust and dependency boundaries

```text
Challenge.EvmProof
        ↓
Challenge.Bls12381.ProofSupport
        ↓
individual BLS12-381 challenges
```

- `Challenge.EvmProof` must not import `Challenge.Bls12381` or an individual challenge.
- `Challenge.Bls12381.ProofSupport` may import `Challenge.EvmProof` and pinned semantic crypto modules, but no individual challenge.
- Each `Spec.lean` imports only `EvmSemantics.EVM.BigStep`.
- Reusable mathematics must not live under `Reference/Proofs`.
- Do not add or use any `CertifiedArtifact` module or builder.
- No final theorem may depend on `sorry`, `native_decide`, or project-defined axioms.

## Semantic gate discovered during audit

EIP-2537 requires subgroup rejection in G1MSM, G2MSM, and pairing. Pinned
`evm-semantics` revision `26fdf59` only checks curve membership for those
operations; upstream `192d611` has the same behavior. Therefore:

- G1ADD, G2ADD, map-Fp-to-G1, and map-Fp2-to-G2 can receive final challenge
  predicates after vector conformance tests pass.
- G1MSM, G2MSM, and pairing may receive shared arithmetic and ABI scaffolding,
  but their final `Correct` predicates and reference proofs must wait for a
  corrected pinned oracle.
- The map implementations do clear cofactors as required; only their file
  headers incorrectly claim otherwise.

### Task 1: Establish import-boundary smoke checks

**Files:**
- Create: `Checks/Bls12381.lean`
- Create: `Challenge/Bls12381.lean`
- Create: `Challenge/Bls12381/ProofSupport.lean`

1. Add a failing check importing the intended shared umbrella modules.
2. Run `lake env lean Checks/Bls12381.lean` and verify the imports are missing.
3. Add the minimal umbrella modules with `warningAsError` enabled.
4. Run `lake env lean Checks/Bls12381.lean` and verify it passes.
5. Check imports with `rg '^import ' Challenge/EvmProof Challenge/Bls12381`.

### Task 2: Add generic word-limb and typed-region boundaries

**Files:**
- Create: `Challenge/EvmProof/Limbs.lean`
- Create: `Challenge/EvmProof/MemoryRegion.lean`
- Modify: `Challenge/EvmProof.lean`
- Modify: `Checks/EvmProof.lean`

1. Write failing Lean examples for two-word reconstruction, canonical bounds,
   region disjointness, same-region reads after writes, and preservation of a
   disjoint region.
2. Run `lake env lean Checks/EvmProof.lean` and verify missing declarations.
3. Implement only the generic definitions and lemmas needed by the examples.
4. Re-run `lake build +Challenge.EvmProof +Checks.EvmProof`.
5. Migrate genuinely generic MODEXP digit/carry/borrow declarations only once
   compatibility can be maintained without duplicating declarations.

### Task 3: Add the BLS codec refinement layer

**Files:**
- Create: `Challenge/Bls12381/ProofSupport/Codec.lean`
- Modify: `Challenge/Bls12381/ProofSupport.lean`
- Modify: `Checks/Bls12381.lean`

1. Add failing examples for exact wire sizes, Fp/Fp2 encode-decode round trips,
   infinity encoding, non-zero padding rejection, field-modulus rejection, and
   malformed-length rejection.
2. Verify the checks fail because the codec boundary is absent.
3. Implement theorem wrappers around the pinned codec and point codecs.
4. Validate with official EIP-2537 success and failure vectors.
5. Re-run the shared BLS checks and inspect the axiom footprint.

### Task 4: Add the base-field refinement layer

**Files:**
- Create: `Challenge/Bls12381/ProofSupport/Fp.lean`
- Modify: `Challenge/Bls12381/ProofSupport.lean`
- Modify: `Checks/Bls12381.lean`

1. Add failing examples defining the `128-bit high : 256-bit low`
   representation used by evmification.
2. Cover reconstruction, comparison with `p`, carry/borrow, conditional
   add/subtract, canonicalization, and byte encoding.
3. Implement the minimal pure representation and refinement lemmas.
4. Add boundaries for schoolbook multiplication and Barrett reduction before
   reasoning about concrete bytecode.
5. Differential-test add/sub/neg/mul/square/inverse against the incumbent
   precompile semantics and Foundry implementation.

### Task 5: Add extension-field refinement

**Files:**
- Create: `Challenge/Bls12381/ProofSupport/Fp2.lean`
- Create: `Challenge/Bls12381/ProofSupport/Fp6.lean`
- Create: `Challenge/Bls12381/ProofSupport/Fp12.lean`
- Modify: `Challenge/Bls12381/ProofSupport.lean`
- Modify: `Checks/Bls12381.lean`

1. Write failing componentwise refinement examples for each layer.
2. Implement Fp2 add/sub/neg/Karatsuba multiplication/square/inverse bridges.
3. Implement Fp6 tower and sparse-multiplication bridges needed by pairing.
4. Implement Fp12 multiplication, conjugation, Frobenius, cyclotomic square,
   and exponentiation bridges needed by pairing.
5. Verify each layer independently before importing the next.

### Task 6: Add projective curve and scalar machinery

**Files:**
- Create: `Challenge/Bls12381/ProofSupport/G1Projective.lean`
- Create: `Challenge/Bls12381/ProofSupport/G2Projective.lean`
- Create: `Challenge/Bls12381/ProofSupport/ScalarMul.lean`
- Create: `Challenge/Bls12381/ProofSupport/Msm.lean`
- Modify: `Checks/Bls12381.lean`

1. Add failing examples for infinity representation, affine projection,
   projective scaling equivalence, addition, doubling, and negation.
2. Prove projective formulas refine the pinned affine operations when the
   input points satisfy the relevant curve invariant.
3. Prove the double-and-add fold against semantic scalar multiplication.
4. Add MSM fold/Pippenger refinement separately from ABI validation.
5. Add subgroup predicates and rejection-boundary tests, but do not claim the
   pinned subgroup-sensitive precompiles satisfy them.

### Task 7: Implement G1ADD

**Files:**
- Create: `Challenge/Bls12381G1Add.lean`
- Create: `Challenge/Bls12381G1Add/Spec.lean`
- Create: `Challenge/Bls12381G1Add/ProofSupport.lean`
- Create: `Challenge/Bls12381G1Add/Reference.lean`
- Create: `Challenge/Bls12381G1Add/Scorer.lean`
- Create: `Checks/Bls12381G1Add.lean`

1. Write failure-first spec/codec/vector checks for exact 256-byte input,
   padding/range/on-curve rejection, infinity cases, and 128-byte output.
2. Freeze a concrete reference only after its wrapper passes all vectors.
3. Prove operation-specific refinement using shared Fp/projective results.
4. Prove end-to-end `Correct` and exact gas through existing execution tools.
5. Add scorer, submission boundary, and axiom checks.

### Task 8: Implement G2ADD

Follow Task 7 under `Challenge/Bls12381G2Add`, with 512-byte input,
256-byte output, Fp2 codecs, and G2 projective refinement. Do not freeze the
current evmification wrapper until its missing validation is fixed or wrapped.

### Task 9: Implement G1MSM and G2MSM up to the semantic gate

**Files:**
- Create corresponding challenge umbrellas and `ProofSupport` modules.
- Defer final `Spec.lean`, `Reference.lean`, and correctness checks if the
  pinned semantics still lacks subgroup rejection.

1. Validate positive-multiple length rules and reject empty input.
2. Validate every point, including subgroup membership, before accumulation.
3. Prove scalar and MSM implementation refinements using shared machinery.
4. Resume final challenge predicates only after the oracle is corrected.

### Task 10: Implement the map precompiles

**Files:**
- Create full challenge trees for `Bls12381MapFpToG1` and
  `Bls12381MapFp2ToG2`.

1. Add official mapping vectors and malformed-codec cases first.
2. Prove SSWU, projective isogeny, exceptional denominators, sign selection,
   and cofactor-clearing refinements in shared BLS support where reusable.
3. Prove the individual ABI/output adapters, exact execution, and gas.
4. Confirm outputs lie in the prime-order subgroup.

### Task 11: Implement pairing up to the semantic gate

**Files:**
- Create: `Challenge/Bls12381Pairing/ProofSupport.lean`
- Create challenge wrapper/scorer/check files only after the gate clears.

1. Test positive-multiple input length, empty rejection, codecs, curve checks,
   subgroup checks, and 32-byte Boolean encoding.
2. Prove Miller loop and final exponentiation against the shared field tower.
3. Prove the multi-pair fold and exact gas.
4. Freeze `Correct` only against subgroup-conformant pinned semantics.

### Task 12: Repository integration

**Files:**
- Modify: `lakefile.toml`
- Modify: `.github/workflows/ci.yml`
- Modify: `.github/lean-package-cache-targets` when the dependency closure changes
- Modify: `README.md`
- Add challenge submission scripts and Foundry cross-checks.

1. Add each completed challenge to Lake/CI independently.
2. Run focused builds and vector tests after every challenge.
3. Run `lake build`, all `Checks` targets, submission self-tests, scorer
   controls, Foundry differential tests, and `git diff --check`.
4. Scan new trusted files for `sorry`, `native_decide`, and unexpected axioms.
