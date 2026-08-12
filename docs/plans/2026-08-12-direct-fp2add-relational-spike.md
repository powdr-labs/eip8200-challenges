# Direct `fp2Add` Relational Contract Implementation Plan

> **For Codex:** REQUIRED SUB-SKILL: Use superpowers:test-driven-development to implement this plan task by task.

**Goal:** Determine whether replacing one downstream use of G2 `fp2Add`'s named exact final-state graph with a selected-observation contract reduces prover RSS and makes any production proof modules removable.

**Architecture:** Keep the existing exact evaluator proof as the private connection to Yul semantics, but make the selected consumer reason through an opaque contract containing execution, output, and frame facts. The consumer must not unfold or rewrite `fp2AddFinalState`. This tests the architectural claim that exact states should be confined to one bridge; it does not pretend that merely renaming the existing exact theorem is a memory optimization.

**Tech Stack:** Lean 4.31, `yul-semantics`, `yul-compiler`, `evm-semantics`, Lake, `/usr/bin/time -v`, repository axiom and proof-policy checks.

---

## Baseline and stop conditions

- Baseline on the current warm tree:
  - `SourceFp2AddOutput.lean`: 2,700,520 KiB maximum RSS.
  - `SourceOnCurveRhs.lean`: 2,682,040 KiB maximum RSS.
- The experiment is successful only if the migrated consumer no longer mentions `fp2AddFinalState` and the new API exposes selected observations rather than equality to a complete state.
- Reject a purported direct proof if it unfolds `fp2AddFinalState` in the consumer, recovers equality with it by determinism, or expands both the evaluator state graph and `Fp2.addSource` in one declaration.
- Do not delete an exact-state file unless `rg` and a clean build show that it is unreachable from all production roots. A neutral RSS result is still useful evidence and must be recorded.

## Task 1: Freeze the desired consumer-facing theorem

**Files:**

- Modify: `Checks/Bls12381G2AddSourceFp2AddRefinement.lean`
- Modify: `Challenge/Bls12381G2Add/Reference/Proofs/SourceFp2AddPreservation.lean`

1. Add a compile check requesting a contract for a completed `fp2Add` call that provides the output value and preservation of a disjoint lower memory window without exposing a concrete final-state expression.
2. Run `lake env lean Checks/Bls12381G2AddSourceFp2AddRefinement.lean` and confirm it fails because the contract declaration is absent.
3. Add the smallest proposition/structure needed by the check; keep arithmetic characterization in existing opaque theorems.

## Task 2: Prove one bridge and keep the state graph private

**Files:**

- Modify: `Challenge/Bls12381G2Add/Reference/Proofs/SourceFp2AddRefinement.lean`
- Modify only if dependency direction requires it: `Challenge/Bls12381G2Add/Reference/Proofs/SourceFp2AddPreservation.lean`

1. Construct the contract once from the existing source execution, output, arithmetic, and preservation facts.
2. Ensure the public theorem quantifies over the resulting state and states selected observations; it must not have `fp2AddFinalState` in its type.
3. Run the focused check and the repository proof-policy checker. Confirm no new axioms.

## Task 3: Migrate the `onCurve` arithmetic consumer

**Files:**

- Modify: `Challenge/Bls12381G2Add/Reference/Proofs/SourceOnCurveRhs.lean`
- Potentially modify: `Challenge/Bls12381G2Add/Reference/Proofs/SourceOnCurveDefs.lean`

1. Add a failing check that rejects direct occurrences of `fp2AddFinalState` in the migrated correctness declaration or its local proof path.
2. Change the `onCurve` RHS canonicality and lawful-value proofs to consume the selected-observation theorem.
3. Do not unfold the exact state graph in those proofs.

## Task 4: Measure and decide

**Files:**

- Modify: `docs/bls-proof-engineering-lessons.md`
- Modify: `docs/bls-proof-architecture-research.md`

1. Measure `SourceFp2AddRefinement.lean` and `SourceOnCurveRhs.lean` with `/usr/bin/time -v lake env lean ...` under the same warm-cache conditions.
2. Compare against the recorded baseline. Treat changes below ordinary run-to-run noise as neutral.
3. Run `lake env lean Checks/Bls12381G2AddSourceFp2AddRefinement.lean`, the affected G2 check root, and the proof-policy script.
4. Use `rg` plus Lean dependency output to identify newly dead production modules. Delete only modules with no remaining production consumer.
5. Record why memory did or did not move: theorem elaboration peak, transitive import floor, retained exact execution consumers, or actual reduction in simultaneous term construction.

## Result

Completed on 2026-08-12. The `onCurve` addition execution and correctness slice
uses a computable irreducible `fp2AddContractState`; the four migrated modules
contain no occurrence of `fp2AddFinalState`. The contract publishes execution,
selected Fp2 output, and lower-memory frame facts. A generic four-word
extensionality theorem was moved down from the `onCurve` tree, and
`SourceFp2AddOutput` now imports its store/load lemmas directly.

The experiment was memory-neutral. `SourceFp2AddOutput.lean` measured
2,690,440--2,691,984 KiB versus a 2,700,520 KiB baseline;
`SourceOnCurveRhs.lean` measured 2,682,152--2,687,168 KiB versus 2,682,040 KiB.
The approximately 2.68 GiB imported-environment floor dominates these small
leaves. The exact chain remains live because other main branches consume it.
The general in-place/output-order corollary did make the two 102-line
`SourceOnCurveAddInputA/B` adapters dead, so those production files were
removed without merging any execution firebreak.
