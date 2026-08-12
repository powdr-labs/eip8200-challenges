# BLS12-381 G2ADD Implementation Plan

> **For Claude:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task.

**Goal:** Implement and verify a proof-friendly concrete EIP-2537 G2ADD runtime against the local BLS12-381 shared proof support.

**Architecture:** Keep the challenge adapter, source execution, representation refinement, compilation certificates, and final EVM theorem in separate modules. The concrete algorithm uses naive affine G2 addition over source-faithful Fp2 arithmetic; field multiplication and inversion use fixed-size MODEXP calls. Each large source value and branch condition gets a named challenge-local definition and a focused check so downstream modules consume compiled theorems rather than unfolding both representations.

**Tech Stack:** Lean 4.31, Mathlib, pinned EVM/Yul semantics, local `Challenge.EvmProof` profiled compiler/MODEXP infrastructure, and `Challenge.Bls12381.ProofSupport` codecs and lawful affine arithmetic.

## Resource and correctness invariants

- Build only focused G2ADD targets with `lake -Kjobs=1` until the final relevant gate.
- Observe focused Lean RSS and stop/refactor a declaration approaching 6 GiB.
- Never use `sorry`, `admit`, `native_decide`, custom axioms, unlimited resource settings, or `CertifiedArtifact`.
- Preserve exact 512-byte input, canonical Fp2 decoding, ordinary on-curve validation without subgroup checks, all-zero infinity encoding, 256-byte output, and invalid exceptional behavior.
- Keep executable modules free of proof-only imports and broad tactic dependencies.

### Task 1: Local specification adapter

**Files:**
- Modify: `Challenge/Bls12381G2Add/Spec.lean`
- Create: `Checks/Bls12381G2AddSpec.lean`

1. Add a failing check for `inputBytes`, success/none characterizations, the official vector, non-subgroup acceptance, invalid lengths, and an off-curve input.
2. Run `lake -Kjobs=1 build +Checks.Bls12381G2AddSpec` and confirm failure because the local adapter API is absent.
3. Replace the pinned `run?` adapter with `Codec.decodeG2`, `G2Affine.add`, and `Codec.encodeG2`; prove the small characterization theorems.
4. Re-run the focused check and existing G2ADD/conformance checks.
5. Commit only G2ADD-owned files.

### Task 2: Frozen proof-friendly source and concrete artifact

**Files:**
- Create: `Challenge/Bls12381G2Add/Reference/reference.yul`
- Create: `Challenge/Bls12381G2Add/Reference/Source.lean`
- Create: `Challenge/Bls12381G2Add/Reference/FrozenBytecode.lean`
- Create: `Challenge/Bls12381G2Add/Reference/Bytecode.lean`
- Create: `Challenge/Bls12381G2Add/Reference.lean`
- Create: `Checks/Bls12381G2AddReference.lean`

1. Write a failing reference check for parse/compile equality and a fixed bytecode size/hash boundary.
2. Implement a naive affine G2ADD Yul program with source-identical Fp helpers, explicit Fp2 add/sub/mul/inv/equality/zero/on-curve helpers, fixed memory regions, and fixed MODEXP budgets.
3. Parse and compile the source, freeze the exact emitted bytes, and make the focused artifact check green.
4. Commit the artifact slice.

### Task 3: Compiler and stack certificates

**Files:**
- Create: `Challenge/Bls12381G2Add/Reference/Proofs/Compilation.lean`
- Create bounded lowering, byte-assembly, and stack-certificate modules under `Challenge/Bls12381G2Add/Reference/Proofs/`
- Create matching `Checks/Bls12381G2Add*` focused checks.

1. Add one RED check per certificate boundary.
2. Reuse the profiled compiler interfaces; chunk finite byte/stack checks so no theorem stores whole suffixes.
3. Compile each chunk before its umbrella consumer.
4. Commit lowering, byte assembly, and stack soundness as separate slices.

### Task 4: Source helper execution and representation bridges

**Files:**
- Create staged `Source*Defs.lean`, `Source*Exec.lean`, and `Source*.lean` modules under `Challenge/Bls12381G2Add/Reference/Proofs/`
- Create one dedicated `Checks/Bls12381G2AddSource*.lean` per stage.

1. Prove field helper evaluation and reuse already-compiled G1ADD value/refinement theorems only when the G2 source helper is definitionally the same; do not duplicate large arithmetic proofs blindly.
2. Prove Fp2 add/sub/mul/inv/zero/equality and on-curve execution one named intermediate at a time against `Fp2.*Source`.
3. Split each source evaluator theorem from its representation theorem and compile both before composition.
4. Commit after every helper family.

### Task 5: Main source semantics

**Files:**
- Create staged input, validation, affine-branch, output, and source-correctness modules under `Challenge/Bls12381G2Add/Reference/Proofs/`
- Create focused checks for invalid length, invalid padding/noncanonical/off-curve points, infinity branches, opposite points, doubling, and unequal finite addition.

1. Add RED branch checks before each source theorem.
2. Relate decoded memory words to `Codec.decodeG2` through explicit projection lemmas.
3. Apply the compiled Fp2 helper refinements to the naive affine branch equations.
4. Prove source output equals the local specification, including non-subgroup inputs.
5. Commit each control-flow family separately.

#### G2 point-add reuse map

The finite/infinity case split is the same lawful affine program already used
by G1ADD.  G2 should instantiate the shared endpoint instead of reproving its
branch algebra:

- Both infinity, left infinity, and right infinity map directly to the shared
  `LawfulAffine.add` identity branches (with `G2Affine.curve`).
- Equal finite points with distinct y-coordinates, and equal-x points with
  zero y, map to the shared inverse/vertical-line infinity branch.
- Equal finite nonzero-y points use the shared doubling equation.
- Unequal finite points use the shared ordinary affine-add equation.
- The final x/y formulas and preservation of on-curve membership come from
  shared `LawfulAffine.add` / `G2Affine.onCurve_add`, not a G2-local replay of
  the generic field algebra.

Only the adapters around that endpoint remain G2/Fp2-specific:

- four-word Fp2 equality/zero predicates and canonicality;
- Fp2 add/sub/mul/inv source execution and lawful/field transport;
- the twist equation `y² = x³ + 4(1+u)` and no-subgroup-check validation;
- 512-byte G2 codec/padding, eight-word point copies/stores, and 256-byte
  output encoding;
- matching the Yul branch conditions and scratch-memory values to the shared
  lawful affine branch inputs.

The G1 branch-control theorem shapes may be followed for execution plumbing,
but their scalar-Fp representation lemmas must not be copied as G2 algebra.

### Task 6: End-to-end EVM correctness and gas

**Files:**
- Create final compiler/source composition modules under `Challenge/Bls12381G2Add/Reference/Proofs/`
- Modify: `Challenge/Bls12381G2Add/Reference.lean`
- Modify: `Challenge/Bls12381G2Add.lean`
- Modify: `Checks/Bls12381G2Add.lean`

1. Add RED checks for the concrete runtime `CorrectWithSchedule`, `Correct`, and the gas theorem.
2. Instantiate the real MODEXP-call profile and profiled compiler theorem.
3. Compose source correctness with concrete bytecode execution and a bounded schedule.
4. Add exact expected-axiom guards and source-dependency checks.
5. Run focused G2ADD gates, then the relevant BLS family/conformance gate single-job.
6. Commit the verified G2ADD challenge.
