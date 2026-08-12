# BLS12-381 G1MSM Implementation Plan

> **For Claude:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to
> implement this plan task-by-task.

**Goal:** Implement and verify the EIP-2537 G1MSM challenge using the local
proof-visible codecs and the shared naive MSM operation.

**Architecture:** Parse each 160-byte term through the local subgroup G1 codec
and exact unreduced scalar codec, then evaluate the resulting list with
`Msm.g1Wire`. Implement the same left-to-right pair loop and binary scalar
schedule in proof-friendly Yul, exposing each source helper, loop step, and EVM
trace stage through a separately compiled theorem rather than unfolding the
entire program in one proof.

**Tech Stack:** Lean 4.31, EvmSemantics, YulSemantics/YulEvmCompiler, local
`Challenge.Bls12381.ProofSupport` modules, and focused `lake -Kjobs=1` checks.

## Constraints

- Only `Challenge/Bls12381G1Msm/**` and `Checks/Bls12381G1Msm*.lean` are owned.
- Shared BLS and EVM proof support is frozen; report a missing endpoint rather
  than editing it.
- Use naive binary scalar multiplication and left-fold addition, not Pippenger.
- Reject empty input, non-multiples of 160 bytes, malformed fields, off-curve
  points, and points outside the prime subgroup.
- Never reduce the 32-byte scalar modulo the subgroup order.
- Use one RED-to-GREEN proof slice per commit. Build with one job and stop a
  focused process before it reaches 6 GiB RSS.
- Do not use `sorry`, `admit`, `native_decide`, custom axioms,
  `CertifiedArtifact`, or unlimited resource settings.

### Task 1: Strict local specification adapter

**Files:**

- Modify: `Challenge/Bls12381G1Msm/Spec.lean`
- Create: `Checks/Bls12381G1MsmSpec.lean`

1. Write a failing check that requires `decodeTerm`, `decodeTerms`, and the
   adapter to use `Codec.decodeG1Subgroup`, `Codec.decodeScalar`, and
   `Msm.g1Wire`.
2. Run `lake -Kjobs=1 build +Checks.Bls12381G1MsmSpec` and confirm the check
   fails because the local API does not exist.
3. Add a structural recursive decoder over the pair count. Preserve input
   order and package each scalar with `ScalarMul.scalar256OfDecode`.
4. Define `spec` as strict length validation, term decoding, naive wire MSM,
   and exact G1 encoding.
5. Check empty, short, trailing-byte, infinity, canonicality, curve,
   subgroup, official single-term, and official two-term cases.
6. Rebuild the focused target, inspect peak RSS, scan the changed files for
   forbidden proof escapes, and commit.

### Task 2: Adapter characterization

**Files:**

- Create: `Challenge/Bls12381G1Msm/SpecRefinement.lean`
- Modify: `Checks/Bls12381G1MsmSpec.lean`

1. Add failing theorem signatures for the zero-count decoder, successor step,
   exact term count, successful point/scalar decoding, and strict rejection.
2. Prove each property in a small module without unfolding the full MSM.
3. Export a compact success characterization for later source-loop proofs.
4. Add exact axiom guards and commit after focused verification.

### Task 3: Frozen proof-friendly runtime

**Files:**

- Create files under `Challenge/Bls12381G1Msm/Reference/`
- Create focused `Checks/Bls12381G1MsmRuntime*.lean` files

1. Write failing parser/evaluator checks for each source helper and main branch.
2. Implement explicit Yul helpers for 64-byte field windows, subgroup testing,
   affine add/double, binary scalar multiplication, and the outer pair loop.
3. Keep source definitions separate from evaluation and representation proofs.
4. Compile the program and freeze its assembled runtime bytes behind an exact
   equality check; do not introduce a certified-artifact builder.
5. Verify representative valid and rejection inputs, then commit the runtime
   independently of its correctness proof.

### Task 4: Staged source refinement

**Files:**

- Create bounded proof modules under
  `Challenge/Bls12381G1Msm/Reference/Proofs/`
- Create matching focused checks under `Checks/`

1. Prove calldata and field-window framing one helper at a time.
2. Prove point/subgroup and scalar decoder refinement without exposing MSM.
3. Prove one binary scalar-loop step and compile it to an `.olean` boundary.
4. Prove one outer MSM-loop step using the scalar theorem and shared
   `Msm.foldG1_cons` semantics.
5. Compose success, each rejection branch, output encoding, and memory framing.
6. Measure every focused module and split any declaration approaching the RSS
   limit before continuing.

### Task 5: EVM execution, gas, and final theorem

**Files:**

- Create challenge-local artifact, compiler, execution, gas, and correctness
  modules under `Challenge/Bls12381G1Msm/Reference/`
- Modify: `Challenge/Bls12381G1Msm/ProofSupport.lean`
- Modify: `Challenge/Bls12381G1Msm/AdditionalGoals.lean`
- Modify: `Challenge/Bls12381G1Msm/Scorer.lean`
- Modify: `Challenge/Bls12381G1Msm.lean`
- Modify: `Checks/Bls12381G1Msm.lean`

1. Add failing checks for source-to-bytecode execution refinement and the
   concrete runtime theorem.
2. Compose independently compiled compiler/execution stages.
3. Prove a schedule theorem that preserves the actual pair/bit loop and covers
   the EIP discounted G1MSM schedule without claiming optimized execution gas.
4. Derive `Correct` with `correct_of_schedule`, wire the verified runtime into
   the scorer/submission surfaces, and pin exact theorem axioms.
5. Run all `+Checks.Bls12381G1Msm*` targets serially, then the relevant BLS
   family gates serially. Scan owned files for forbidden escapes and confirm a
   clean owned diff before the final commit.
