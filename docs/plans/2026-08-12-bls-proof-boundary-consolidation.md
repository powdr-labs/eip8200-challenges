# BLS Proof Boundary Consolidation Implementation Plan

> **For Claude:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task.

**Goal:** Reduce the conceptual and physical overhead of the completed G1ADD
and G2ADD proofs without removing the opaque compilation boundaries that keep
Lean memory bounded.

**Architecture:** First remove the accidental import of the all-inclusive BLS
proof umbrella and enforce that boundary in the existing proof-policy checker.
Then consolidate checks by observable purpose. Address the underlying memory
cause separately by publishing deep arithmetic contracts and testing a
relational state-transition contract before removing any proof-stage files.
G1MSM and G2MSM remain paused and untouched throughout.

**Tech Stack:** Lean 4.31, Lake, Python 3 policy checks, shell self-tests,
`/usr/bin/time`, pinned `evm-semantics`, and the verified Yul-to-EVM compiler.

## Design choice

Three interface shapes were considered:

1. New challenge-specific shared facade files would give descriptive names,
   but would add files and duplicate the existing `Spec` and leaf-module
   boundaries.
2. Capability facades for codecs, affine arithmetic, Fp, and Fp2 would be
   flexible, but the existing shared leaf modules already have those roles.
3. Reuse the existing challenge and shared modules as facades, remove only the
   accidental umbrella edge, and deepen existing arithmetic modules with
   consumer contracts.

Use option 3. It has no migration aliases, adds no facade files, and produced
the best immediate measured improvement. Warm elaboration of the challenge
`ProofSupport.lean` modules fell from about 3.22 GiB RSS to about 2.18 GiB for
G1ADD and 2.48 GiB for G2ADD when the broad umbrella import was omitted.

## Task 1: Enforce narrow imports for completed ADD challenges

**Files:**

- Modify: `scripts/check-lean-proof-policy.py`
- Modify: `scripts/test-check-lean-proof-policy.sh`
- Modify: `Challenge/Bls12381G1Add/ProofSupport.lean`
- Modify: `Challenge/Bls12381G2Add/ProofSupport.lean`
- Modify: `.github/workflows/ci.yml`

**Step 1: Write the failing policy self-test**

Add fixtures under paths containing `Challenge/Bls12381G1Add` and
`Challenge/Bls12381G2Add` that import the exact broad umbrella:

```lean
import Challenge.Bls12381.ProofSupport
```

Assert that both are rejected with a `forbidden broad BLS proof-support
import` diagnostic. Add an accepted fixture showing that a precise leaf import
such as `Challenge.Bls12381.ProofSupport.FpAddSub` remains allowed.

**Step 2: Run the self-test and verify RED**

Run:

```sh
scripts/test-check-lean-proof-policy.sh
```

Expected: failure because the scanner does not yet recognize the broad import.

**Step 3: Implement the scoped import rule**

Extend the existing Python scanner so the exact broad umbrella import is
forbidden only for Lean files under completed G1ADD and G2ADD trees. Do not
apply the rule to paused G1MSM/G2MSM files or the shared umbrella itself.

**Step 4: Run the policy tests and verify GREEN**

Run:

```sh
scripts/test-check-lean-proof-policy.sh
python3 scripts/check-lean-proof-policy.py \
  Challenge/Bls12381G1Add Challenge/Bls12381G1Add.lean \
  Challenge/Bls12381G2Add Challenge/Bls12381G2Add.lean
```

Expected: the self-test passes; the repository scan fails on exactly the two
current broad imports.

**Step 5: Remove the two broad imports**

Delete only:

```lean
import Challenge.Bls12381.ProofSupport
```

from the G1ADD and G2ADD challenge-level `ProofSupport.lean` files. Add no new
facade file and do not alter theorem statements.

**Step 6: Use the common scanner in both CI gates**

Replace the G1ADD ad hoc forbidden-spelling grep with the same policy
self-test and scoped scanner used by G2ADD. Keep the G2ADD gate unchanged
except for any command formatting needed to scan both local challenge roots.

**Step 7: Verify the narrow boundaries**

Run:

```sh
scripts/test-check-lean-proof-policy.sh
python3 scripts/check-lean-proof-policy.py \
  Challenge/Bls12381G1Add Challenge/Bls12381G1Add.lean \
  Challenge/Bls12381G2Add Challenge/Bls12381G2Add.lean
lake env lean Challenge/Bls12381G1Add/ProofSupport.lean
lake env lean Challenge/Bls12381G2Add/ProofSupport.lean
```

Expected: all commands pass without warnings.

**Step 8: Measure and build the final boundaries**

With no competing Lean worker, run focused single-job builds and record elapsed
time and maximum RSS:

```sh
/usr/bin/time -v lake -Kjobs=1 build \
  +Challenge.Bls12381G1Add.Reference.Proofs.FinalCorrectness
/usr/bin/time -v lake -Kjobs=1 build \
  +Challenge.Bls12381G2Add.Reference.Proofs.FinalCorrectness
```

Also build the two final public/trust check modules. No internal proof-stage or
MSM file is changed in this task.

## Task 2: Define the permanent check taxonomy

**Files:**

- Create or modify: `docs/bls-check-inventory.md`
- Inspect: `Checks/Bls12381G1Add*.lean`
- Inspect: `Checks/Bls12381G2Add*.lean`

**Step 1: Inventory each check**

Classify every completed-ADD check as one or more of:

- public API;
- final trust census;
- conformance or branch behavior;
- frozen artifact identity;
- certificate validity;
- resource-regression boundary; or
- temporary internal theorem restatement.

Record any assertion unique to a temporary file before proposing its removal.

**Step 2: Select permanent gates**

Prefer these existing roots:

- `Checks/Bls12381G1Add.lean`;
- `Checks/Bls12381G1AddReference.lean`;
- `Checks/Bls12381G2Add.lean`;
- `Checks/Bls12381G2AddReference.lean`; and
- `Checks/Bls12381G2AddReferenceRuntime.lean`.

Do not delete anything in this classification step.

## Task 3: Migrate one representative check cluster

**Files:** Determined by the Task 2 inventory.

**Step 1: Add missing boundary assertions first**

Move each unique observable assertion into the appropriate permanent gate.
Run that gate before deleting old checks. If the assertion already exists at a
public boundary, document the replacement.

**Step 2: Remove only covered restatement checks**

Delete a small representative cluster, preferably one whose files merely
restate internal theorem types and axiom messages. Update imports and CI target
enumeration as needed.

**Step 3: Verify all permanent gates**

Build the public, reference, and runtime gates serially and run the policy
scanner. Compare final theorem axiom output with the pre-change result.

## Task 4: Publish one deep Fp contract

**Files:** Exact paths selected after inspecting the current canonicality and
lawfulness theorems, expected under
`Challenge/Bls12381/ProofSupport/Fp*.lean` and one G1ADD `Source*` consumer.

**Step 1: Write a failing consumer check**

State the desired consumer theorem: one call should supply both output
canonicality and mathematical meaning without importing or unfolding the
internal multiplication/reduction schedule.

**Step 2: Add the minimal bundled contract**

Compose existing compiled theorems into the contract. Do not rewrite the
arithmetic implementation in this task.

**Step 3: Migrate one G1ADD helper**

Make one source refinement consume the new contract through a precise import.
Measure dependency closure and peak RSS before considering any old stage
redundant.

### Task 4 implementation status

Completed on 2026-08-12. `Fp.mulCanonical_spec` now bundles output
canonicality and field meaning in the existing `FpMul` module. The G1ADD
`SourceOnCurveRefinement.fpMulOutput_eq_mulCanonical` helper consumes that
contract once. A failing boundary check was observed before the theorem was
added, and the shared Fp check now guards its type and axiom footprint. The
consumer's imports did not change; warm A/B peak RSS was effectively unchanged,
so no internal proof file was removed. Final G1ADD and G2ADD correctness roots
and all permanent gates rebuilt successfully after the shared-module change.

## Task 5: Publish one deep Fp2 contract

Repeat Task 4 for a representative G2ADD operation using the existing Fp2
source program and lawful refinement. Preserve the authoritative-program,
multiple-interpreters structure already present in `Fp2SourceProgram.lean`.

### Task 5 implementation status

Partially completed on 2026-08-12. `Fp2.mulSource_spec` now bundles canonicality
and field meaning in the existing `Fp2SourceLawful` module, with a type check
and guarded axiom census. The attempted G2ADD consumer bridge equated the
concrete final-state output with the reducible direct interpreter. Direct
definitional equality timed out; a named-rewrite variant reached about 16.7 GiB
RSS after 44 seconds and was terminated. The bridge and consumer edits were
rolled back, leaving the repository compiling. No heartbeat was raised and no
proof-stage file was removed. The restored G2ADD final root, shared Fp2 check,
and all permanent gates then passed at 2,907,560 KiB peak RSS.

Do not retry that equality shape. Before migrating a concrete Fp2 consumer,
establish a relational stage summary that carries selected output values and
frame facts without constructing the complete EVM and interpreter graphs
together. This finding moves the relational-contract spike ahead of further
Fp2 migration.

**Completed safe follow-up 2026-08-12.** `Fp2MulLowContract` now bundles the
existing staged evaluation, canonical selected output, lawful multiplication,
low-memory frame preservation, and equality to `Fp2.mulSource` only after
`Fp2.toField` projection. It lives in the existing low-memory lawful boundary;
no module was added. `onCurveY2` consumes the bundled canonicality and lawful
result projections.

The producer leaf measured 2,704,512 KiB before and 2,713,660 KiB after; the
consumer measured 2,717,384 KiB before and 2,710,556 KiB after. These small
changes are noise. The contract's trust footprint is `[propext,
Classical.choice, Quot.sound]`. The full G2ADD root and all 46 retained checks
passed 2,534 jobs in 1:25.67 at 2,897,300 KiB maximum child RSS. A process-group
monitor observed no individual process above 2,881,032 KiB, so the 6 GiB stop
condition was not approached.

An attempted 6 GiB virtual-address limit was rejected as a measurement method:
Lean could not map a Mathlib `.olean.private` file even though RSS was only
816,500 KiB. Future stop guards must monitor per-process RSS instead of setting
`ulimit -v`, and must not sum RSS across processes because mapped shared pages
would be double-counted.

## Task 6: Spike a relational G1ADD stage contract

**Files:** New or existing generic EVM contract module chosen only after a
small design review; one complete G1ADD branch consumer.

Define a contract that records selected result values, permitted memory
changes, gas delta, and halt status. Connect it once to concrete EVM/Yul
execution and compare it with the current expanded-state proof chain.

Success requires lower or equal peak RSS, no new trust assumptions, and a
smaller consumer interface. Otherwise retain the current stages and record the
failed approach.

**Completed 2026-08-12.** The spike reused
`Reference/Proofs/SourceRun.lean`; it added no module or check file. The
both-infinity path now exposes `MainBothInfinityContract yst final`, whose
final state is existential. Consumers receive the complete source `Run`, the
selected returned bytes and halt kind, the permitted active-memory expansion,
and frame equalities for memory, storage, transient storage, environment,
returndata, logs, and selfdestructs. The concrete
`mainBothInfinityReturnState` remains private to the bridge proof.

The Yul `EvmState` has no gas field. Gas was therefore not invented in the
source contract: the compiled-EVM gas schedule remains a separate contract to
be composed at the compiler-correctness boundary. This is an intentional
cross-layer split, not a missing frame field.

TDD exposed a small instance of the root failure mode. Constructing all frame
fields with blanket `all_goals rfl` reached Lean's maximum recursion depth.
Restricting reduction to the two shallow updates with
`simp only [mainBothInfinityReturnState, touchMemory]` compiled the source-run
leaf in 1.82 s at 2,760,112 KiB RSS. `SourceSpec` now consumes only the
existential contract and its `returned_inputWindow` projection for the complete
both-infinity branch.

The new contract theorem has the same guarded trust footprint as the legacy
exact-state theorem: `[propext, Classical.choice, Quot.sound]`. A warm
single-job build of the complete G1ADD root and all 43 remaining G1ADD check
modules passed 2,342 jobs in 10.03 s at 2,721,348 KiB peak RSS while a Lean
language-server worker was active. The earlier post-Fp G1ADD verification was
3,126,220 KiB, so the acceptance condition is satisfied, but this is not a
controlled cold A/B benchmark. The import closure did not change; the gain is
a smaller logical consumer interface and a reusable proof shape.

No old proof-stage module became redundant from this first branch. The exact
state chain is still the one-time implementation of the relational bridge, and
other branches still consume exact states. Task 7 must therefore classify
stages conservatively rather than deleting the both-infinity chain.

**Follow-up first-infinity slice.** The branch-specific structure was deepened
into `MainReturnContract yst beforeReturn final offset size`, with
`MainBothInfinityContract` retained as a specialization and a new
`MainFirstInfinityContract` specialization for the post-copy state. A failing
boundary check preceded the implementation. `SourceSpec` now consumes only
the existential run and its specification-facing affine-identity projection;
it no longer names `mainFirstInfinityReturnState`.

Apples-to-apples direct elaboration of `SourceRun.lean` measured 2,759,628 KiB
before and 2,761,184 KiB after, a 0.06% difference treated as noise. The axiom
footprint remains `[propext, Classical.choice, Quot.sound]`. The complete
G1ADD root and all 43 checks passed 2,342 jobs at 2,716,696 KiB. The exact
first-infinity execution module remains necessary to implement the bridge, so
this slice removes no production file.

## Task 7: Consolidate only obsolete proof stages

After Tasks 4-6, identify files whose only purpose has been replaced by a deep
contract. Merge or remove them one at a time, rebuilding the narrow consumer
after each change. Retain any file that still provides a measured `.olean`
memory boundary.

**Classified 2026-08-12; no production stage removed.** A recursive local
import scan found all 115 G1ADD challenge modules and all 229 G2ADD challenge
modules reachable from their public/final roots. The new relational contract
hides the exact state from `SourceSpec`, but the old state chain still
implements that bridge once. The short byte-assembly chunks are bounded
decision certificates, and the short G2 inversion chain is the measured
replacement for a roughly 14.2 GiB monolith. None is obsolete yet.

The separate check cleanup could safely finish: all 119 remaining G2ADD files
whose only content was internal `#check` lookup were removed (886 lines). They
did not provide `.olean` firebreaks for production and their imported modules
were already in final-correctness closure. Completed-ADD checks now total 89
(43 G1ADD and 46 G2ADD), down 131 files from the 220-file snapshot. The
CI-shaped G2ADD root plus every remaining check passed 2,534 jobs at
2,732,800 KiB peak RSS; policy and cache-policy tests also passed.

**Follow-up production consolidation.** After Task 8 made certificate
soundness generic, each challenge's 72-line `StackCertificateSound.lean`
became a shallow adapter above `StackCertificateChunks.lean`. The bridge was
moved into that existing aggregate boundary and both adapters were removed.
This reduced the reachable counts to 114 G1ADD and 228 G2ADD modules including
their top-level entry points, while retaining every bounded certificate chunk
and every staged source/arithmetic module.

## Task 8: Extract the generic compact certificate checker

Baseline one G1ADD and one G2ADD certificate chunk plus final soundness. Move
only challenge-independent checker and composition logic into
`Challenge.EvmProof`; keep generated data and bounded chunks challenge-local.
Preserve original theorem names with aliases and accept the extraction only if
single-job RSS does not regress.

**Completed 2026-08-12.** `Challenge.EvmProof.StackCertificate` now owns the
challenge-independent compact numeric representation, finite key/entry
checker, chunk composition, suffix-restricted proof certificate, validity and
boundedness bridge, and final assembly stack-bound theorem. Frozen program,
certificate entries, entry decision proofs, and bounded chunks remain
challenge-local. Existing G1ADD/G2ADD theorem names are preserved by thin
instantiation modules, so compiler-correctness callers and trust guards did not
change.

The shared module is imported precisely by the two ADD compilation/core
modules and its check; it was deliberately not added to the broad
`Challenge.EvmProof` umbrella, which is consumed by unrelated SHA, RIPEMD,
MODEXP, and Blake support.

The first adapter attempt made every local compatibility definition an
`abbrev`. Chunk checking stayed green, but both soundness files failed because
their scoped `unfold`/`dsimp` proofs relied on local projection names. The
accepted design keeps three tiny local data projections (`thawStackEntry`,
`materializeStackCertificate`, and the frozen length lookup) while sharing the
checker and 224-line soundness algorithm. This is a useful opacity lesson:
deduplicate the algorithm, not proof-stabilizing names.

Warm leaf A/B measurements with the language server active:

| Leaf | Before RSS | After RSS | Before wall | After wall |
| --- | ---: | ---: | ---: | ---: |
| G1ADD certificate chunk 0 | 3,489,692 KiB | 3,489,648 KiB | 7.38 s | 7.34 s |
| G2ADD certificate chunk 0 | 3,997,984 KiB | 3,970,804 KiB | 12.44 s | 12.53 s |
| G1ADD certificate soundness | 2,444,200 KiB | 2,410,840 KiB | 1.71 s | 1.63 s |
| G2ADD certificate soundness | 2,111,160 KiB | 2,062,832 KiB | 1.65 s | 1.59 s |

The first post-change G2 chunk sample was 4,021,148 KiB; the repeated sample
above was used to avoid treating a 0.58% fluctuation as a regression. The
extraction is memory-neutral and below the stop threshold.

The new shared trust guards report `[propext, Quot.sound]` for checker
equivalence and validity, and `[propext, Classical.choice, Quot.sound]` for the
final execution bound, matching the existing challenge guards. Shared checks,
policy tests, and both full challenge gates passed. The post-change G1ADD gate
built 2,343 jobs in 1:23.26 at 3,375,136 KiB; G2ADD built 2,535 jobs in 2:50.47
at 4,361,416 KiB. These broad rebuilds are verification figures, not leaf A/B
performance claims.

The subsequent adapter consolidation retained the same theorem names and
axiom guards. Aggregate-plus-check builds peaked at 2,458,036 KiB for G1ADD and
2,127,740 KiB for G2ADD; both compiler-correctness consumers rebuilt. The
separate soundness files were therefore deleted, but the core instantiation,
generated data, and bounded decision chunks remain separate compilation
units. The public roots and all retained checks subsequently passed 2,342
G1ADD jobs and 2,534 G2ADD jobs.

## Stop conditions

- Do not modify or resume G1MSM or G2MSM.
- Stop and restage a proof trending toward 6 GiB RSS.
- Do not merge files solely to reduce their count.
- Do not remove a check before its observable purpose is classified and
  covered.
- Do not accept a memory claim without a narrow, recorded build.
