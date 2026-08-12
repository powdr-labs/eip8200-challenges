# Stack-Certificate Chunk Consolidation Implementation Plan

> **For Codex:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task.

**Goal:** Replace twenty-five 100-entry G1ADD/G2ADD certificate decision files with five measured 500-entry compilation units while preserving every 100-entry theorem, trust boundary, and a safe CI memory schedule.

**Architecture:** Retain `prove_frozen_entry_chunk` once per 100-entry window so Lean still closes ten-entry subproofs as opaque declarations. Group five adjacent public chunk theorems into each physical `.lean` file. The aggregate theorem and all public theorem names remain unchanged; only imports and physical compilation units change.

**Tech Stack:** Lean 4, Lake, shared `Challenge.EvmProof.StackCertificate`, GitHub Actions, `/usr/bin/time -v`.

---

### Task 1: Consolidate G1ADD decision chunks

**Files:**
- Modify: `Challenge/Bls12381G1Add/Reference/Proofs/StackCertificateChunk0.lean`
- Modify: `Challenge/Bls12381G1Add/Reference/Proofs/StackCertificateChunk5.lean`
- Modify: `Challenge/Bls12381G1Add/Reference/Proofs/StackCertificateChunks.lean`
- Delete: G1ADD `StackCertificateChunk1`–`4` and `6`–`9`

**Steps:**
1. Put theorem windows 0–4 in chunk 0 and 5–9 in chunk 5, using distinct private data names.
2. Preserve the public theorem names `stackFrozenEntryChecks_chunk0` through `chunk9`.
3. Make the aggregate import only chunk 0 and chunk 5.
4. Compile each merged unit independently and verify peak RSS remains below 6 GiB.
5. Compile the aggregate theorem and its axiom guard.

### Task 2: Consolidate G2ADD decision chunks

**Files:**
- Modify: `Challenge/Bls12381G2Add/Reference/Proofs/StackCertificateChunk0.lean`
- Modify: `Challenge/Bls12381G2Add/Reference/Proofs/StackCertificateChunk5.lean`
- Modify: `Challenge/Bls12381G2Add/Reference/Proofs/StackCertificateChunk10.lean`
- Modify: `Challenge/Bls12381G2Add/Reference/Proofs/StackCertificateChunks.lean`
- Delete: the other twelve G2ADD 100-entry decision files

**Steps:**
1. Group theorem windows 0–4, 5–9, and 10–14 in three compilation units.
2. Preserve all fifteen public chunk theorem names.
3. Update aggregate imports only; do not rewrite the aggregate proof.
4. Compile each merged unit independently and verify peak RSS remains below 6 GiB.
5. Compile the aggregate theorem and its axiom guard.

### Task 3: Serialize heavy units in CI

**Files:**
- Modify: `.github/workflows/ci.yml`
- Modify: `scripts/test-bls-ci-cache-policy.py` or add a focused CI-policy test only if needed

**Steps:**
1. Build the two G1ADD and three G2ADD merged units explicitly, one command at a time, before aggregate roots.
2. Keep the general root/check build after those cached units.
3. Add a deterministic policy assertion that the serialized targets remain present in CI.
4. Run the policy self-test.

### Task 4: Verify and record evidence

**Files:**
- Modify: `docs/bls-proof-engineering-lessons.md`
- Modify: `docs/bls-file-count-and-memory-review.md`

**Steps:**
1. Record per-unit wall time and maximum RSS.
2. Run proof-policy and cache-policy tests.
3. Build G1ADD and G2ADD roots plus every retained check with one job.
4. Run direct frozen artifact checks.
5. Confirm the production-tree reduction is twenty files and `git diff --check` passes.

## Result

Completed. The five final units peaked at 4,697,568--5,534,628 KiB RSS and
retained every 100-entry theorem name. Serialized CI commands are enforced by
the cache-policy self-test. G1ADD now has 105 production Lean files and passed
2,335 jobs; G2ADD has 211 and passed 2,519 jobs. Both frozen artifact checks,
the proof-policy scan, the cache-policy test, and `git diff --check` passed.
