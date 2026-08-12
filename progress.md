# BLS12-381 proof progress

Last updated: 2026-08-12
Working branch: `kw/new-precompiles`

This is the durable handoff for the BLS12-381 work. It records what is actually
proved, what is still incomplete, and which proof-engineering approaches are
safe to resume. The Lean sources and fresh verification output remain the
authority if this file becomes stale.

Implementation is paused by user request. The last GREEN branch checkpoint is
`kw/new-precompiles` at `e802e69`. Incomplete RED experiments are preserved on
`wip/bls-proof-pause-2026-08-12` at `2bca845`; they are not part of the GREEN
branch history.

## Current scope

The current milestone is the six non-pairing EIP-2537 precompiles:

1. G1ADD
2. G2ADD
3. G1MSM
4. G2MSM
5. MAP_FP_TO_G1
6. MAP_FP2_TO_G2

Pairing is deliberately deferred to a separate task. The first implementation
is intentionally naive: affine addition, binary scalar multiplication, and
left-fold MSM. Pippenger and other optimizations are not on the critical path.

## Status summary

| Area | Status | Authoritative evidence / next boundary |
| --- | --- | --- |
| Shared proof support | Complete for the six-precompile milestone | `Challenge/Bls12381/ProofSupport`; `+Checks.Bls12381` and conformance gates were green at the shared freeze. |
| G1ADD | Complete, independently reviewed, CI-gated | Final proof `dacd447`; exports `231813b`; artifact-sensitive CI fixes `f45f847`, `e5ee4cc`. Exact runtime: 1,723 bytes. |
| G2ADD | Complete, independently reviewed, CI-gated | Final challenge gate `8beb159`; correctness `5dc8f27`; CI/direct-artifact gate `a8491b5`; cache/policy hardening through `61ec724`. Exact runtime: 2,788 bytes. |
| G1MSM | Paused; roughly two-thirds of the end-to-end deliverable | Last GREEN checkpoint `e802e69`. Resume total point-add value/preservation, then scalar semantics, subgroup/outer MSM, main correctness, gas/scorer/CI. |
| G2MSM | Paused; roughly three-quarters of the end-to-end deliverable | Last GREEN checkpoint `04c2a5c`. Resume concrete doubling preservation/composition, total point-add semantics, scalar/MSM semantics, and final correctness/gas/CI. |
| MAP_FP_TO_G1 | Paused | Strict shared-adapter spec and all ten vector/axiom checks are complete at `3e2cfec`. Concrete runtime construction is the next boundary. |
| MAP_FP2_TO_G2 | Not started at challenge-runtime level | Shared implementation/proofs/vectors are complete. Start after a worker slot becomes available. |
| Pairing | Deferred | Do not pull it into this milestone. |
| Architecture cleanup/refactor | On hold by user request | Do not explore, propose, or apply architecture changes until explicitly resumed. |

## Shared layer: completed endpoints

The shared folder is sufficient for a first naive implementation of every
non-pairing precompile. It includes:

- strict Fp, Fp2, scalar, G1, and G2 codecs with canonical rejection and framed
  round trips;
- ordinary point decoding separated from subgroup decoding;
- lawful Fp/Fp2 add, subtract, multiply, inverse, predicates, sign, and complete
  square-root boundaries;
- one generic affine curve boundary with all infinity, equal, opposite, y=0,
  doubling, and unequal-x branches;
- a proof-only bridge to Mathlib's independent affine additive group;
- exact unreduced `Fin (2^256)` scalar decoding;
- naive binary scalar multiplication with independent `n • P` semantics;
- naive left-fold G1/G2 MSM with independent sum-of-scalars semantics;
- subgroup predicates and MSM subgroup closure;
- shared G1/G2 SSWU, sqrt-ratio, isogeny, cofactor multiplication, codecs, and
  all official map vectors;
- profiled compiler correctness, successful MODEXP call realization, memory
  copy/read bridges, fixed MODEXP layouts, and gas-independent execution
  infrastructure.

Optional strengthening still absent: a certified BLS group-order/exponent
theorem proving universal `N • map(u) = 0`. No assumption was added. This does
not block the current naive map implementation milestone.

## Completed precompiles

### G1ADD

The proof covers the local strict EIP adapter, all canonical rejection paths,
ordinary non-subgroup acceptance, all affine branches, staged field helpers,
full source-to-spec refinement, compiled EVM execution, gas schedule, scorer,
and generated C. A real source bug was found and fixed: opposite points and the
equal-point/y=0 tangent now explicitly store canonical infinity before return.

Important final evidence:

- exact 1,723-byte frozen runtime;
- `reference_correctWithSchedule` and `reference_correct`;
- final axiom footprint `[propext, Classical.choice, Quot.sound]`;
- all dedicated G1ADD checks, conformance, and C generation passed in the final
  implementation gate;
- independent spec/quality review approved after CI cache fixes.

### G2ADD

The proof covers the strict 512-byte adapter, Fp2/twist arithmetic, ordinary
non-subgroup acceptance, all affine branches, staged source execution,
source-to-spec refinement, the direct-compiler artifact, stack and byte
certificates, gas schedule, scorer, and generated C.

Important final evidence:

- exact 2,788-byte direct-compiler runtime (ordinary `yulc` produces a separate
  3,339-byte optimized artifact and is not the proof boundary);
- 1,734 lowered instructions and certified stack depth at most 1,023;
- `reference_correctWithSchedule` and `reference_correct`;
- all 176 dedicated checks and conformance gates passed;
- independent proof/runtime review approved;
- dedicated CI dynamically builds every G2ADD check and the direct artifact
  boundary.

The BLS CI cache is artifact-sensitive for non-Lean `include_str` inputs. The
proof-policy scan is intentionally conservative raw-source scanning: forbidden
spellings in comments or strings must be reworded rather than hidden behind a
partial Lean lexer.

## Paused G1MSM work

Recoverable checkpoint: `e802e69` adds the GREEN smart constructor and cached
`x3Hi` projection on top of the unequal-X arithmetic checkpoint `2e18e53`.
Later concrete right-subtraction specialization files are RED and preserved
only on WIP commit `2bca845`.

Completed:

- strict local 160-byte-term spec using subgroup decoding and unreduced scalars;
- official/rejection vectors;
- proof-friendly 3,688-byte runtime;
- frozen AST, compiler, lowering, bytecode, stack certificate, and profiled
  compiler theorem;
- invalid-length and field helper execution;
- complete branchwise point-add execution: identities, vertical/opposite,
  doubling, and unequal-x;
- fixed 256-bit loop control and structural scalar trace;
- fixed high-memory point-region model and point-add readiness;
- lawful unequal slope plus exact X/Y output readback is in late-stage closure.

Still required:

1. Finish total point-add output equality and preservation for every branch.
2. Induct the 256-bit trace to shared `ScalarMul.g1` semantics.
3. Prove the exact subgroup check and outer naive MSM fold refine the shared
   subgroup/MSM APIs.
4. Compose the full source/main theorem.
5. Instantiate final compiled `CorrectWithSchedule` / `Correct`.
6. Add honest gas, scorer, public umbrellas, CI, and independent review.

No worker is active. Resume from the value-only right-subtraction projection
boundary documented in the WIP files.

## Paused G2MSM work

Recoverable checkpoints: `19078bd` proves the lawful doubling numerator and
`07f1f25` proves the denominator, inverse, and final slope stages. `04c2a5c`
composes the lawful double slope. The next RED memory-preservation leaf is
preserved only on WIP commit `2bca845`.

Completed:

- strict local 288-byte-term spec using `decodeG2Subgroup`, unreduced scalars,
  and the shared naive left fold;
- official single/multi/rejection vectors;
- proof-friendly 3,264-byte runtime;
- normalized source frozen in chunks;
- 1,934-entry optimized assembly, 2,069 lowered instructions, exact byte
  reconstruction, and a 1,653-state stack certificate;
- profiled compiler correctness;
- local staged Fp/Fp2 helpers, predicates, on-curve, stores, and inversion;
- complete structural point-add execution and all branch paths;
- complete 256-step scalar-loop structure and trace existence;
- lawful point-add postlude formulas and pure identification with
  `G2Affine.add` / `G2Affine.double`.

Still required:

1. Finish branch slope lawfulness and total point-add value/preservation.
2. Induct the trace to shared `ScalarMul.g2` semantics.
3. Prove subgroup checking and outer term-loop refinement to `Msm.g2Wire`.
4. Compose main/source correctness.
5. Instantiate final `CorrectWithSchedule` / `Correct`.
6. Add gas, scorer, public/CI gates, and independent review.

No worker is active. On resume, rebuild heavy leaves serially before any broad
G2MSM umbrella.

## Paused MAP_FP_TO_G1 work

Checkpoint `3e2cfec` migrates the challenge spec to the shared `MapToG1.run`
adapter and proves the strict 64-byte rejection characterization, five official
positive vectors, five official failure vectors, and exact axiom guards. The
shared adapter supplies SSWU, the 11-isogeny, naive effective-cofactor
multiplication, on-curve/wire validity, and rejection theorems. The
challenge-level worker must still:

1. build and freeze a proof-friendly concrete runtime;
2. prove staged source execution/refinement to the shared map;
3. certify compiler, bytes, stack, and MODEXP calls;
4. prove final correctness/gas and add scorer/CI/review gates.

The placeholder source wrapper and intentionally failing first runtime vector
are preserved only on WIP commit `2bca845`. No worker is active.

## Proof-engineering rules learned here

Read `docs/why-concrete-evm-proofs-are-expensive.md` before changing a concrete
proof. The following are operational requirements, not optional style advice:

- Use one focused build at a time and monitor per-process RSS. Kill and split a
  proof around 6 GiB; never raise an unlimited resource setting.
- `-Kjobs=1` is a Lean option, not a Lake scheduler limit. Lake may build stale
  sibling dependencies concurrently. Rebuild expensive leaves serially before
  running an aggregate target.
- Keep large arithmetic graphs, interpreter stages, byte chunks, and stack
  certificate chunks behind opaque `.olean` firebreaks.
- Prefer relational `Step`/`BigStep` composition to whole-program interpreter
  simplification.
- For successive arithmetic operations, export a value-only context and cached
  projection lemmas. Do not let a downstream theorem import and unfold the full
  previous execution DAG.
- Prove memory locality/readback by disjoint ranges and fixed high-water
  invariants. Do not normalize long chains of `touchMemory`/`storeWord` updates
  in one theorem.
- Compose large finite checks from bounded leaves and half-aggregators. A green
  leaf is not permission to restate all leaf equalities in a monolithic theorem.
- Never retry a killed monolithic proof unchanged.
- Preserve exact public theorem axiom guards and run the conservative proof
  policy scanner in challenge CI.

Representative failures and successful replacements:

| Failed approach | Observed RSS | Successful replacement |
| --- | ---: | --- |
| G2 Fp2 multiplication full-DAG simplification | about 17.6 GiB | Named component/value endpoints, about 3.4 GiB each. |
| G2 inversion low-memory chain | about 14.2 GiB | Square/scalar/real/neg/imag/store stages, about 3.4 GiB each. |
| G1MSM whole-program interpreter soundness | about 8.3 GiB | Relational prefix/tail composition, about 2.6 GiB. |
| G1MSM subtraction output/context projections | 7–12 GiB | Generic value-only context and cached smart-constructor projections, about 3.5 GiB. |
| G2MSM monolithic compiler equality | about 8.3 GiB | Frozen normalized AST, assembly, byte, and stack chunks; roughly 2–5.2 GiB per leaf. |
| G2MSM optimizer equality aggregate | about 6.3 GiB | Opaque half-aggregators plus tiny final composition. |

## Resume checklist

Before resuming work:

1. Run the superpowers bootstrap and read the concrete-EVM memory note.
2. Inspect `git status --short`, current worker ownership, `git log`, `free -h`,
   and the largest Lean processes.
3. Treat active dirty files as another worker's property.
4. Locate the last committed green boundary and add a focused RED check for the
   next single theorem.
5. Build only that leaf. Record peak RSS and refactor immediately if it trends
   toward 6 GiB.
6. Commit a bounded green slice with exact axiom guards and scoped forbidden
   scan before starting the next slice.
7. Do not call a precompile complete until source/spec, compiled correctness,
   gas/scorer, CI, focused gates, and independent review all pass.

## Architecture work

Architecture exploration and refactoring are on hold by user request. Do not
continue from `docs/bls-proof-architecture-research.md` or its linked sources
until explicitly directed to resume.
