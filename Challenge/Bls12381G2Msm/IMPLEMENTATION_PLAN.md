# BLS12-381 G2MSM Implementation Plan

> **For Claude:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to
> implement this plan task-by-task.

**Goal:** Implement and verify EIP-2537 G2MSM with strict local codecs and the
shared proof-visible naive MSM operation.

**Architecture:** Decode each 288-byte term as a subgroup-checked 256-byte G2
point followed by an exact unreduced 32-byte scalar.  Evaluate terms in wire
order with `Msm.g2Wire`.  The concrete Yul mirrors that naive left fold and a
fixed 256-bit binary scalar loop, with G2ADD-compatible Fp/Fp2 helpers and
separately compiled source, arithmetic, compiler, byte, and stack boundaries.

**Tech Stack:** Lean 4.31, EvmSemantics, YulSemantics/YulEvmCompiler, local
`Challenge.Bls12381.ProofSupport`, and focused `lake -Kjobs=1` checks.

## Invariants

- Own only `Challenge/Bls12381G2Msm/**`, `Checks/Bls12381G2Msm*.lean`, and
  this plan.  Do not modify shared support or the other BLS challenges.
- Reject empty input, non-multiples of 288 bytes, malformed/off-curve G2
  points, and points outside the prime subgroup.
- Preserve the full unsigned scalar in `[0, 2^256)` without reduction.
- Use naive binary scalar multiplication and left-fold addition, not
  Pippenger.
- Add one behavioral check before each implementation/proof slice and observe
  it fail for the intended missing endpoint.
- Build one focused target at a time with `lake -Kjobs=1`; stop and split a
  declaration before 6 GiB RSS.
- Do not use `sorry`, `admit`, `native_decide`, custom axioms,
  `CertifiedArtifact`, or unlimited resource settings.

### Task 1: Strict specification adapter

1. Add a RED check requiring local `scalarAt`, `decodeTerm`, `decodeTerms`,
   and success/rejection behavior.
2. Replace the legacy mutable-loop spec with `Codec.decodeG2Subgroup`,
   `Codec.decodeScalar`, and `Msm.g2Wire`.
3. Check exact 288-byte framing, official vectors, multi-term order, infinity,
   canonicality, curve, subgroup, and maximum-scalar behavior.
4. Commit the green adapter slice.

### Task 2: Adapter refinement

1. Add RED theorem checks for one-term decoding, subgroup acceptance, decoded
   list length, strict failure, and successful output characterization.
2. Prove the endpoints in a small `SpecRefinement` module.
3. Guard exact expected axioms and commit after focused verification.

### Task 3: Frozen proof-friendly runtime

1. Add RED parser/evaluator checks for the invalid-length branch and each
   helper family.
2. Implement explicit Fp/Fp2 operations, G2 validation/subgroup testing,
   affine point addition, a fixed 256-bit scalar loop, and the outer term loop.
3. Keep source definitions separate from evaluator and representation proofs.
4. Freeze the parsed source, optimized/lowered assembly, runtime bytecode, and
   stack certificate behind exact kernel-visible checks.
5. Commit the runtime and each certificate boundary separately.

### Task 4: Staged source refinement

1. Prove field and Fp2 helpers through named intermediate values, reusing
   compiled G2ADD/G1MSM endpoints where definitions exactly agree.
2. Prove input framing, point/subgroup decoding, and scalar decoding.
3. Prove one point-add branch family at a time through shared
   `LawfulAffine` semantics.
4. Prove one scalar-loop step, then one outer MSM-loop step using
   `Msm.foldG2_cons`.
5. Compose success and all rejection branches without unfolding the whole
   interpreter or arithmetic DAG.

### Task 5: Concrete EVM theorem and gates

1. Add RED checks for compiler execution, `CorrectWithSchedule`, `Correct`,
   and gas/schedule claims.
2. Instantiate the profiled MODEXP compiler theorem and compose the compiled
   source correctness boundary with concrete bytecode execution.
3. Expose an honest schedule retaining the actual term and 256-bit loops;
   derive `Correct` using `correct_of_schedule`.
4. Wire the verified runtime into scorer/submission modules and pin expected
   theorem axioms.
5. Run all focused G2MSM checks serially, then the relevant BLS/conformance
   gate, audit forbidden mechanisms and owned changes, and request review.
