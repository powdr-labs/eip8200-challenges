# Yul Procedure Contract Spike Implementation Plan

> **For Claude:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task.

**Goal:** Establish one reusable proof-facing Yul execution contract, migrate one complete G1ADD branch to it, and measure whether the boundary stays memory-neutral while hiding the concrete final state from consumers.

**Architecture:** Add a small source-only contract over `YulSemantics.Run` under `Challenge.EvmProof`. A challenge supplies a precondition and relational postcondition; consumers receive an existential environment, final Yul state, and outcome together with execution and the postcondition. `ProfiledCorrectness` supplies a separate lifting theorem that transports a proved source contract through the existing compiler simulation into `EvmSemantics.EVM.Steps`. The first consumer is the existing G1ADD both-infinity branch, whose return/frame summary already demonstrates the desired projection boundary.

**Tech Stack:** Lean 4.31, `yul-semantics`, `yul-compiler`, `evm-semantics`, Lake, `/usr/bin/time -v`, repository axiom and proof-policy checks.

## Design constraints

- Do not change `yul-semantics`, `yul-compiler`, or `evm-semantics` in this spike.
- Keep gas out of the source postcondition because `YulSemantics.EVM.EvmState` is gas-free.
- Do not make the source-only contract import compiler correctness.
- Do not expose a challenge-specific constructed final-state expression through the new consumer theorem.
- Preserve the existing final theorem and axiom footprint.
- Stop or restage any process trending toward 6 GiB RSS.
- Do not touch the paused G1MSM/G2MSM trees or the user's `Scratch.lean`.

### Task 1: Characterize the desired source boundary

**Files:**

- Modify: `Checks/Bls12381G1AddSourceRun.lean`

1. Add an example requiring a generic `Challenge.EvmProof.YulRunContract` API and a G1 both-infinity specialization.
2. Compile the check and confirm it fails because the generic API does not exist.
3. Record the failure before adding production code.

### Task 2: Add the source-only contract

**Files:**

- Create: `Challenge/EvmProof/YulContract.lean`
- Modify: `Challenge/Bls12381G1Add/Reference/Proofs/SourceRun.lean`

1. Define `YulRunContract` as the existential closure of `YulSemantics.Run` and a relational postcondition.
2. Provide only shallow introduction, postcondition weakening, and projection theorems needed by the first caller.
3. Separate the G1 return/frame postcondition from execution.
4. Express `run_main_bothInfinity_contract` through the generic contract without changing its useful projection theorem.
5. Compile the boundary check and confirm it passes.

### Task 3: Lift the contract through compilation

**Files:**

- Modify: `Challenge/EvmProof/ProfiledCorrectness.lean`
- Modify: `Checks/Bls12381G1AddSourceRun.lean`

1. Add a theorem that consumes `YulRunContract` and the existing explicit compiler evidence.
2. Return the source postcondition together with the existing bounded target-EVM execution guarantee.
3. Add a type-level characterization and axiom census to the existing check.
4. Compile the generic bridge and G1 check.

### Task 4: Measure and verify

**Files:**

- Modify: `docs/bls-proof-engineering-lessons.md`
- Modify: `docs/bls-file-count-and-memory-review.md`
- Modify: this plan with measured results

1. Measure direct elaboration of the source contract module, `SourceRun.lean`, and the compiler bridge using `/usr/bin/time -v lake env lean ...`.
2. Run the narrow G1 source check, compiler-correctness consumer, public G1ADD root, proof-policy tests, and `git diff --check`.
3. Compare the result with the existing roughly 2.76 GiB `SourceRun` baseline.
4. Record whether the abstraction reduced consumer exposure, changed RSS, or made any old production stage removable.

## Acceptance criteria

- The source-only generic API has no compiler or target-EVM import.
- The migrated G1 consumer does not name `mainBothInfinityReturnState`.
- Existing G1ADD correctness and trust checks pass.
- Peak RSS remains below 6 GiB and does not materially regress the recorded source leaf.
- The experiment records honestly if it improves architecture but removes no physical file yet.

## Result

Implemented on 2026-08-12 with a red/green boundary check. The initial check
failed on the absent `YulRunContract` and G1 specialization. After the
source-only module and G1 theorem were added, `SourceSpec` was migrated to the
generic existential postcondition. A second check failed on the absent
compiler adapter; the accepted bridge now transports any contract for the
frozen block through the existing explicit compilation, lowering, stack, and
profile evidence.

The source-only module imports `YulSemantics.BigStep` and compiled at
816,180 KiB RSS. Direct leaf measurements were 2,759,020 KiB for `SourceRun`,
2,782,420 KiB for `SourceSpec`, 1,871,648 KiB for the generic compiler bridge,
and 2,383,636 KiB for the G1 compiler instantiation. Every measured leaf was
below 6 GiB. `SourceRun` is unchanged from its previous roughly 2.76 GiB
range, so the accepted conclusion is architectural improvement with neutral
memory—not a memory reduction.

The new generic and G1 theorems retain the expected axiom footprint. The
migrated `SourceSpec` branch contains no reference to
`mainBothInfinityReturnState`. One shared production file was added and no
old stage is removable from this first migration; later adoption must justify
that temporary file-count cost by converging other branch contracts on this
API.

Verification completed with the conservative proof-policy scanner, its
self-test, the BLS cache-policy self-test, all shared and G1 contract/axiom
checks, and the complete G1ADD root plus every retained G1ADD check. The final
integration build passed 2,343 jobs. `git diff --check` passed, and the user's
untracked `Scratch.lean` remained untouched.

### Finite unequal-x follow-up

A second red/green cycle required `MainUnequalPre`, `MainUnequalPost`, and
`main_unequal_yulContract`; the boundary check initially failed because none
existed. The complete unequal-x arithmetic branch now returns the compact
`mainFiniteUnequalExpected` observation. The accepted precondition contains
only execution conditions and four canonical input-coordinate facts. An
initial compiling design that also required lambda canonicality, x
distinctness, and the lawful slope was deepened before acceptance: those facts
are now derived by
`mainFiniteDispatcher_unequal_returned_expected_of_inputs`.

`SourceSpec` no longer mentions `mainFiniteUnequalFinalState`, the post-return
state constructor, or the lambda schedule in this branch. Four unused private
representation bridge lemmas were removed. The exact execution chain remains
the one-time implementation of the contract, so no complete production file
became removable.

Repeated direct measurements placed `SourceRun` at
2,720,812--2,726,188 KiB RSS and `SourceSpec` at
2,748,408--2,774,056 KiB; the lawful endpoint measured
2,653,416--2,660,108 KiB. The small difference from earlier measurements is
classified as noise rather than a proven memory reduction.

The focused source, compiler, axiom, proof-policy, and cache-policy checks all
passed. The complete G1ADD root and every retained G1ADD check then passed
2,343 jobs in 9.49 seconds at 2,707,076 KiB peak RSS. `git diff --check` passed,
no `sorry` or `admit` was introduced, and `Scratch.lean` remained untouched.
