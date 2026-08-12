# BLS12-381 File Count and Proof-Memory Review

The reusable incidents, diagnostic workflow, and material intended for a
future proof-engineering skill are maintained in
[`bls-proof-engineering-lessons.md`](bls-proof-engineering-lessons.md).

## Status and scope

G1ADD and G2ADD are the completed BLS12-381 precompile challenges in the
current work. G1MSM and G2MSM contain partial work that an agent started before
being told to stop because the repository's file count had grown too large.
That MSM work is paused and is not part of the completed-precompile scope.

This review distinguishes four things that currently all appear as Lean files:

1. public conceptual APIs;
2. private proof stages introduced to bound Lean elaboration memory;
3. generated or closed certificate chunks; and
4. development checks that restate internal theorem types or trust results.

They should not all be treated as equally valuable public modules.

## Quantitative snapshot

Compared with the merge base of `origin/main`, the BLS-related work added
approximately:

| Area | Files | Added lines |
| --- | ---: | ---: |
| Shared BLS proof support | 135 | 14,713 |
| G1ADD challenge and proof | 117 | 15,784 |
| G2ADD challenge and proof | 232 | 22,526 |
| Other BLS challenges, primarily paused G1MSM/G2MSM | 576 | 55,274 |
| BLS check modules | 556 | 14,766 |
| Shared specifications, vectors, artifacts, CI, docs, and entry points | 18 | 1,628 |
| **Total** | **1,634** | **124,691** |

The central observation is that 1,132 of the 1,634 files are either check
modules or work on BLS challenges other than G1ADD/G2ADD. Most of the physical
file count was therefore not directly required to complete those two
precompiles.

The shared proof-support source occupies about 1.1 MiB, while its current
compiled artifact tree occupies about 105 MiB. Several prime-certificate
`.olean` files are individually between roughly 3 and 9.5 MiB. Source size,
compiled artifact size, and peak elaboration RSS are different measurements;
only a controlled narrow build measures peak memory.

## Why many physical files are justified

In Lean, a separately compiled module can act as an opaque `.olean` firebreak.
Downstream proofs consume the exported theorem instead of reconstructing and
normalizing its full proof term, source interpreter, EVM state, arithmetic
schedule, and large constants.

This is a demonstrated requirement rather than a stylistic preference. A
monolithic G1ADD field-subtraction refinement exceeded approximately 19.8 GiB
RSS without finishing. The staged equivalent completed around 2.7 GiB RSS.
Other BLS source and compiler proofs showed similar reductions after being
split at semantic intermediate results.

The following physical splits should therefore remain unless a controlled
benchmark proves that a replacement is no worse:

- large field identities, range proofs, and representation refinements;
- source execution separated from mathematical representation refinement;
- branch-sensitive EVM/Yul execution stages;
- prime and root certificate evidence;
- bounded byte-assembly and stack-certificate chunks; and
- runtime definitions separated from Mathlib-heavy lawful proofs.

Combining these into one large `ProofSupport.lean` file would reduce the file
count while recreating the memory problem.

## The root cause behind the memory spikes

Physical module splitting contains the symptom; it does not completely remove
the underlying cause. The worst declarations ask Lean to relate two enormous
reducible computations at once:

```text
expanded Yul/EVM execution state
        =
expanded limb/field/curve computation
```

Unification, simplification, or definitional equality can materialize both
graphs simultaneously. Narrowing imports reduces the ambient environment and
rebuild cost, but it does not prevent that pathological normalization inside a
single declaration.

The stronger architectural direction is therefore:

1. **Compositional stage contracts.** Prove execution, result, frame, and gas
   properties as small state-transition contracts, then compose those
   contracts without reopening either implementation.
2. **One deep specification theorem per arithmetic operation.** A consumer of
   Fp multiplication should receive output canonicality and mathematical
   meaning from one theorem. It should not import or unfold schoolbook limbs,
   Barrett or Montgomery reduction, carry schedules, or embedded constants.
3. **One authoritative parametric operation where practical.** Interpret the
   same operation as executable limbs, source/Yul behavior, and mathematical
   behavior. Prove interpreter refinement instead of asking Lean to discover
   equality between independently written expanded programs.
4. **Relational state summaries.** Track selected stack values, named memory
   regions, gas delta, result status, and a frame condition instead of carrying
   a fully expanded `EvmState` through every source proof.
5. **Genuinely linear certificates.** Represent certificate entries with
   instruction indices, stack heights, and compact local facts rather than a
   complete remaining-program suffix per instruction. A generic checker should
   establish one soundness boundary.
6. **Deliberate opacity.** Keep large executable definitions available to their
   evaluator, while proof consumers use opaque characterization and projection
   theorems.

This deeper work is what can reduce both peak memory and the need for “one file
per elaboration emergency.” More RAM, larger heartbeat limits, serial builds,
file merging, narrower imports alone, or deleting checks alone do not solve the
root cause. Serial builds and narrow imports remain useful controls, but they
address different failure modes.

## Where the count is excessive

### Broad shared umbrella imports

`Challenge.Bls12381.ProofSupport` imports the complete codec, field tower,
curve, scalar multiplication, MSM, map-to-curve, subgroup, and prime
certificate graph. Both G1ADD and G2ADD challenge support currently import
that entire umbrella.

Consequently, a challenge that needs a comparatively small set of Fp/Fp2,
codec, and affine facts can inherit the full shared compiled environment.
Physical proof stages may remain separate, but callers should use narrow,
deep facades or direct stable contracts instead of the all-inclusive umbrella.

### Check-module proliferation

There are currently 425 BLS check files. Of those, 311 are at most 30 lines
and 332 contain axiom-message guards. The completed G1ADD/G2ADD subset is now
89 files, down from the 220-file review snapshot after removal of 131
development-only forwarding or signature wrappers. Many checks were useful as focused red/green
development checks, but retaining a separate check for almost every internal
lemma makes the private proof graph part of the permanent public contract.

The long-term check surface should instead concentrate on:

1. public API and compatibility theorem types;
2. a deliberate trust/axiom census rooted at final theorems;
3. official-vector and adversarial conformance;
4. artifact identity and certificate validity; and
5. separately run resource-regression probes for known expensive boundaries.

Fine-grained checks should remain only where they protect a real regression,
such as a branch behavior, artifact identity, trust boundary, or historically
expensive elaboration boundary.

### Duplicated certificate frameworks

G1ADD and G2ADD duplicate challenge-independent stack-certificate checking,
chunk composition, thawing, lookup, and soundness machinery. The generated
assembly, byte, and certificate payloads must remain challenge-local and
chunked, but the checker framework should live once under
`Challenge.EvmProof`.

### Shallow forwarding modules

Some import-only wrappers and one-theorem forwarding `Source*` modules do not
obviously provide a stable public name or a measured memory firebreak. These
are candidates for consolidation, but only after recording their current
import closure and peak RSS. Small line count alone is not sufficient evidence
that a file is unnecessary.

### Paused MSM work

The partial G1MSM and G2MSM trees account for most of the "other BLS
challenge" category. Those files are not redundant with G1ADD/G2ADD: they are
unfinished work for different precompiles. However, they should remain paused
and outside the current refactoring scope. No further MSM proof expansion
should occur until the shared architecture and file-count policy are agreed.

## Recommended first changes

### 1. Narrow imports without removing memory firebreaks

Introduce or select small stable facades for the concepts G1ADD and G2ADD
actually consume. Replace their import of the complete shared proof umbrella
with those narrow imports. Keep internal arithmetic, certificate, and execution
stages as separate compiled modules.

Validation must include:

- an automated import-policy check that fails while the broad umbrella import
  remains;
- focused G1ADD and G2ADD final-correctness builds with one job;
- unchanged public theorem types and axiom footprints; and
- before/after dependency closure, wall time, and maximum RSS measurements.

### 2. Consolidate checks by purpose

Classify existing BLS checks as public API, trust, conformance, artifact,
resource, or temporary internal restatement. Create the smaller permanent
gates before deleting any old checks. Remove an old check only when its
meaning is covered by one of those boundary gates or it is shown to be a
development-only restatement.

The first slice should establish the new check policy and migrate a small,
representative group. A bulk deletion without classification would risk losing
meaningful trust or artifact regressions.

### 3. Establish deep Fp/Fp2 operation contracts

Before removing any fine-grained proof stage, select one existing Fp operation
used by G1ADD and publish a stable theorem that bundles canonicality and
mathematical meaning. Migrate one source helper to consume that theorem without
unfolding the arithmetic implementation. Repeat for one representative Fp2
operation used by G2ADD.

Measure whether those callers can avoid importing internal arithmetic stages
and whether their peak RSS remains bounded. Only then consolidate proof-stage
files made redundant by the new contract.

### 4. Introduce a relational stage-contract spike

Model one complete G1ADD branch with a small transition contract covering its
result, permitted memory changes, gas delta, and status. Connect that contract
to concrete execution once and compare its proof size and peak RSS with the
current expanded-state chain. Do not roll this across G2ADD until the spike has
clear evidence.

Completed for two G1ADD identity branches on 2026-08-12. Both-infinity and
first-infinity now specialize one `MainReturnContract` that hides the expanded
final state from `SourceSpec`. The second slice was memory-neutral at the leaf
(2,759,628 versus 2,761,184 KiB RSS), retained the same trust footprint, and
passed the full 2,342-job G1ADD gate at 2,716,696 KiB. These contracts reduce
consumer exposure to exact states, but the exact execution chains still
implement the bridges and therefore are not yet removable memory barriers.

The same selected-field principle is now validated for one G2ADD Fp2
multiplication caller. `Fp2MulLowContract` relates the frozen staged output to
the authoritative `mulSource` program only through `Fp2.toField`, while also
carrying execution, canonicality, lawful meaning, and low-memory preservation.
This avoided the rejected 16.7 GiB whole-representation equality. The producer
and consumer leaves remained around 2.71 GiB, and the full 2,534-job G2ADD gate
passed at 2,897,300 KiB. The improvement is removal of the pathological proof
shape, not a measurable reduction in ordinary leaf RSS, and no production
stage is obsolete yet.

The first generic source/target boundary is also in place.
`Challenge.EvmProof.YulContract` defines a source-only `YulRunContract`, and
the G1ADD both-infinity branch now instantiates it with explicit pre- and
postconditions. `SourceSpec` consumes this generic contract without naming the
constructed return state. A separate theorem in `ProfiledCorrectness` lifts
the existential source run through the existing compiler certificates and
attaches the target-EVM gas/execution guarantee. The source contract itself
imports neither the compiler nor target EVM semantics.

This spike was memory-neutral: `SourceRun` measured 2,759,020 KiB RSS versus
the earlier 2,759,628--2,761,184 KiB range, and `SourceSpec` measured
2,782,420 KiB. It adds one shared production file and removes none yet. That
temporary count increase is acceptable only if subsequent branch migrations
replace local contract shapes and eventually make exact-state consumer stages
or compatibility wrappers removable.

The finite unequal-x G1ADD path subsequently migrated to the same generic
contract. Its accepted precondition contains branch conditions and canonical
input coordinates only; lawful x-distinctness, lambda canonicality, and slope
correctness are derived behind the contract. `SourceSpec` no longer names the
unequal branch's constructed final state or lambda schedule, and four private
representation bridge lemmas became removable. No whole production stage is
obsolete because those exact execution and memory modules still implement the
contract once.

Repeated `SourceRun` samples were 2,720,812--2,726,188 KiB and `SourceSpec`
samples were 2,748,408--2,774,056 KiB. Those figures are about one percent
below the earlier one-shot measurements but are conservatively classified as
memory-neutral. The generic contract therefore now has a substantive
arithmetic consumer, but the repository still has one additional shared file
and no net production-file deletion from this architectural path.
The complete 2,343-job G1ADD integration gate passed after the migration at
2,707,076 KiB peak RSS, with the proof-policy and trust guards unchanged.

The next experiment applied the same principle to the complete G2ADD
`onCurve` call to `fp2Add`. The caller now composes an irreducible computable
`fp2AddContractState` through execution, selected-output, and lower-memory
frame theorems; its execution and correctness modules no longer name
`fp2AddFinalState`. A proof-only `Classical.choose` state was rejected because
it would have made the remaining symbolic source model noncomputable.

This migration repaired two accidental reversed imports by moving the generic
four-word `fp2At` extensionality lemma below `fp2Add` and importing the direct
store/load memory leaf. It did not lower warm RSS: `SourceOnCurveRhs` measured
2,682,152--2,687,168 KiB after a 2,682,040 KiB baseline, and
`SourceFp2AddOutput` measured 2,690,440--2,691,984 KiB after 2,700,520 KiB.
The measured leaves sit on an approximately 2.68 GiB imported-environment
floor and did not contain the known pathological equality shape.

No `fp2Add` execution-stage file is dead yet. The eight `fp2Add` modules still
implement the one concrete bridge, while main finite/double consumers still
use the exact state API. However, a general in-place/output-order corollary
replaced the only use of `SourceOnCurveAddInputA` and
`SourceOnCurveAddInputB`; those two shallow production adapters (102 lines)
were deleted. This is the intended deletion pattern: relational migration can
remove caller-specific translations even while the measured RSS stays flat.
The exact stages become removable only after the last exact-state consumer is
migrated and a dependency scan confirms they are unreachable. The CI-shaped
G2 root plus all retained G2 checks passed 2,533 jobs after deletion.

### 5. Extract the generic certificate checker later

After import narrowing and check consolidation are measured, extract the
duplicated checker and soundness framework while retaining opaque
challenge-local data chunks. This is likely the highest-value code
deduplication, but abstraction can enlarge Lean terms and therefore requires a
separate memory baseline.

Completed on 2026-08-12: the common compact checker and soundness bridge now
live in `Challenge.EvmProof.StackCertificate`, while generated data and bounded
chunks remain challenge-local. One shared production file was added. The two
challenge core files remain as the thin instantiation boundary used by every
bounded chunk; the two separate `StackCertificateSound.lean` adapters were
subsequently folded into `StackCertificateChunks.lean`, which already owned
the aggregate Boolean certificate proof.
Certificate chunk and soundness leaf RSS was neutral or slightly lower in
repeated warm measurements. The consolidated aggregate boundaries measured
2,458,036 KiB for G1ADD and 2,127,740 KiB for G2ADD and preserved the existing
axiom guards. This removes two more production files without merging the
100-entry decision chunks. The public roots and all retained checks then built
successfully: 2,342 G1ADD jobs and 2,534 G2ADD jobs. Together with the completed
check cleanup, the overall repository change removes 132 files net from the
reviewed ADD surface.

The final certificate file-count pass widened only the physical compilation
units, not the theorem granularity. Each original 100-entry theorem still uses
the shared macro's ten-entry opaque declarations. Five adjacent theorems now
share one source file: two files for G1ADD and three for G2ADD. The five units
measured 4,697,568--5,534,628 KiB RSS, below the 6 GiB ceiling, and CI builds
them in serialized Lake invocations protected by a policy self-test. This
removed twenty additional production files, leaving 105 G1ADD and 211 G2ADD
Lean files below their challenge directories. Full retained gates passed 2,335
and 2,519 jobs respectively, with frozen artifact checks unchanged.

The practical sequence is therefore:

1. narrow the completed challenges' ambient imports;
2. establish the smaller permanent check policy;
3. publish and consume one deep Fp/Fp2 operation contract;
4. test a relational stage contract on one G1ADD branch;
5. consolidate only the proof-stage files made unnecessary by those contracts;
6. extract the generic compact certificate checker;
7. consolidate only measured certificate units with explicit CI serialization;
   and
8. keep G1MSM/G2MSM paused throughout.

## Decision rule

The objective is not the minimum number of `.lean` files. It is:

- a small public conceptual graph;
- a private physical graph large enough to keep elaboration bounded;
- no duplicated generic proof frameworks;
- no permanent check file for every private helper theorem; and
- no broad import that loads unrelated BLS subsystems into completed
  challenges.

Any proposed consolidation that crosses an existing proof boundary is a
memory regression until a controlled narrow build demonstrates otherwise.
Heavy aggregate builds must also have verified concurrency control; in the
current local Lake 5 setup, `lake -Kjobs=1` did not serialize independent
sibling modules.
