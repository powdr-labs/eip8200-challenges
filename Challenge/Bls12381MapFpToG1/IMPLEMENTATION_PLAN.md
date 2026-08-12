# BLS12-381 MAP_FP_TO_G1 Implementation Plan

> **For Claude:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to
> implement this plan task-by-task.

**Goal:** Implement and verify the EIP-2537 MAP_FP_TO_G1 challenge against the
shared lawful `MapToG1.run` operation.

**Architecture:** The challenge specification is a strict 64-byte adapter to
the shared map. The concrete runtime uses the same proof-friendly two-word Fp
representation and fixed MODEXP calls as G1ADD, evaluates the projective SSWU
and homogeneous 11-isogeny schedules in bounded memory, and clears the
cofactor with naive binary affine scalar multiplication. Source values,
interpreter execution, arithmetic bridges, compiler artifacts, and final EVM
execution are compiled as separate opacity boundaries.

**Tech Stack:** Lean 4.31, EvmSemantics, YulSemantics/YulEvmCompiler, shared
`Challenge.Bls12381.ProofSupport.MapToG1`, and single-job focused Lake checks.

## Constraints

- Own only `Challenge/Bls12381MapFpToG1/**`, the top-level challenge import,
  and `Checks/Bls12381MapFpToG1*.lean`.
- Treat shared BLS support as frozen; coordinate any demonstrably missing
  generic EVM theorem before editing outside the owned files.
- Use the naive shared algorithm: projective SSWU, homogeneous 11-isogeny,
  and binary cofactor scalar multiplication. Do not use the native map
  precompile or Pippenger-style machinery.
- Build one focused target at a time with `lake -Kjobs=1`; stop and split a
  declaration before its process reaches 6 GiB RSS.
- Do not use `sorry`, `admit`, `native_decide`, custom axioms,
  `CertifiedArtifact`, or unlimited heartbeats/recursion settings.
- Use one observable RED-to-GREEN slice per commit.

### Task 1: Strict shared specification adapter

**Files:**

- Modify: `Challenge/Bls12381MapFpToG1/Spec.lean`
- Create: `Checks/Bls12381MapFpToG1Spec.lean`

1. Add a failing check for `inputBytes`, `spec_eq_some_iff`,
   `spec_eq_none_iff`, and the exact shared-map output.
2. Run `lake -Kjobs=1 build +Checks.Bls12381MapFpToG1Spec` and verify it
   fails because the challenge-local characterization is absent.
3. Set `spec := ProofSupport.MapToG1.run` and prove the exact strict success
   and rejection characterizations through `Codec.decodeFp`.
4. Check all five official positive vectors and all five vendored failure
   inputs through the public `spec` interface.
5. Run the focused check, inspect axioms/resource use, and commit.

### Task 2: Proof-friendly source and frozen runtime

**Files:**

- Create: `Challenge/Bls12381MapFpToG1/Reference/reference.yul`
- Create: `Challenge/Bls12381MapFpToG1/Reference/Source.lean`
- Create: `Challenge/Bls12381MapFpToG1/Reference/Bytecode.lean`
- Create focused runtime checks under `Checks/`

1. Add a failing parser/source-vector check.
2. Implement two-word Fp canonicality, addition, subtraction, wide
   multiplication, MODEXP reduction/inversion/exponentiation, and fixed
   memory helpers using the established G1ADD layouts.
3. Implement source SSWU, four homogeneous Horner evaluations, pole-aware
   affine isogeny conversion, affine point addition, and a fixed 64-bit naive
   cofactor loop.
4. Check all ten official/failure cases against the public spec, then freeze
   the exact runtime bytes and parser/compiler equality.
5. Commit only after the focused runtime remains below the memory ceiling.

### Task 3: Staged source arithmetic refinement

**Files:**

- Create bounded modules under
  `Challenge/Bls12381MapFpToG1/Reference/Proofs/`
- Create matching focused checks under `Checks/`

For each behavior, first add a check whose missing theorem fails, then add the
minimal proof and rerun it:

1. Decode length, padding, and canonical field rejection.
2. Fp predicate/add/sub/full-multiply/MODEXP call refinement.
3. Sqrt-ratio exponentiation and branch result.
4. Projective SSWU named intermediates and shared-result equality.
5. Each homogeneous polynomial fold and coefficient table.
6. Isogeny denominator/pole branch and affine output equality.
7. Affine point-add branches and one scalar-loop step.
8. Fixed cofactor loop, exact output encoding, and full source/spec match.

Every composite theorem must consume previously compiled bridge lemmas through
targeted rewrites; it must not broadly unfold both source and shared map DAGs.

### Task 4: Compiler and bytecode certificates

**Files:**

- Create challenge-local frozen block/assembly/byte/stack modules under
  `Challenge/Bls12381MapFpToG1/Reference/Proofs/`

1. Add failing checks for parser-to-frozen-block, compilation, lowering,
   byte assembly, and stack soundness.
2. Freeze ordinary Lean data for the normalized block, optimized assembly,
   instructions, bytes, and compact stack certificate.
3. Split byte and stack certificates into independently compiled chunks.
4. Prove profiled compiler correctness with successful MODEXP realization.
5. Run all focused artifact checks and commit.

### Task 5: Final EVM correctness and delivery gates

**Files:**

- Create: `Challenge/Bls12381MapFpToG1/Reference/Proofs/FinalCorrectness.lean`
- Modify: `Challenge/Bls12381MapFpToG1/Scorer.lean`
- Modify: `Challenge/Bls12381MapFpToG1.lean`
- Modify: `Checks/Bls12381MapFpToG1.lean`
- Create final correctness/reference checks under `Checks/`

1. Add failing public checks for `gasSchedule`,
   `reference_correctWithSchedule`, `reference_correct`, and scorer exposure.
2. Compose source refinement and profiled compiler correctness into the
   proof-extracted schedule theorem, without claiming optimized gas.
3. Derive `Correct`, expose the verified reference artifact and scorer, and
   guard exact theorem axioms.
4. Run every `+Checks.Bls12381MapFpToG1*` target serially, then the relevant
   BLS family gate serially.
5. Scan owned files for forbidden mechanisms, review the full owned diff, and
   commit the verified public/CI surface.
