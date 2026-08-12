# Proof Architecture Roadmap for the Remaining Precompiles

Status: architecture and proof-efficiency audit, 2026-08-10.

## Scope

This document covers the nine remaining precompile challenges after excluding
ECRECOVER, BN254 ADD/MUL/PAIRING, and KZG point evaluation:

1. Identity (`0x04`)
2. BLS12-381 G1ADD (`0x0b`)
3. BLS12-381 G1MSM (`0x0c`)
4. BLS12-381 G2ADD (`0x0d`)
5. BLS12-381 G2MSM (`0x0e`)
6. BLS12-381 pairing (`0x0f`)
7. BLS12-381 map Fp to G1 (`0x10`)
8. BLS12-381 map Fp2 to G2 (`0x11`)
9. P256VERIFY (`0x100`)

The current RIPEMD160, MODEXP, BLAKE2f, and SHA256 proofs were reviewed to
identify which patterns should be reused and which proof infrastructure should
be deepened before implementing these challenges.

## Executive summary

The existing proof architecture should not be copied into nine independent
proof trees unchanged. The four current direct-bytecode proof trees already
contain roughly 68,000 lines of Lean proof code, 151 `maxHeartbeats` overrides,
and hundreds of proofs that expose evaluator and artifact implementation
details.

The best existing template is BLAKE2f's separation between:

- a pure algorithm;
- a typed memory representation;
- bytecode execution traces;
- algorithmic refinement;
- exact gas accounting.

The largest scaling problem is repeated execution-path normalization. The most
important cryptographic problem is that all seven BLS challenges depend on the
same 381-bit field arithmetic and projective curve machinery. Those foundations
should be proved once and shared.

Before defining the new challenge correctness predicates, the pinned precompile
semantics should also be checked against the primary specifications and test
vectors. Some of the current BLS semantics and comments are inconsistent, and
the dependency's BLS test coverage is currently too small to treat it as an
unquestioned oracle.

## What already works well

### Structural artifacts

[`ProgramArtifact`](../../Challenge/EvmProof/Program.lean) converts a single
assembly equality into indexed decoder and jump-destination facts. The newer
BLAKE2f artifact is the best current use of this machinery: it proves
well-formedness for the whole artifact and uses compact, `Fin`-indexed located
paths.

### Executable EVM traces

[`Stepper`](../../Challenge/EvmProof/Stepper.lean) provides an executable
supported-opcode evaluator and connects successful evaluation to the relational
EVM semantics. This is substantially easier to use than proving each EVM step
manually.

### Gas composition

[`GasSteps`](../../Challenge/EvmProof/Gas.lean) removes gas subtraction from
symbolic states, composes exact costs additively, and supports bounded loops.
The memory meter in [`Meter`](../../Challenge/EvmProof/Meter.lean) treats memory
expansion as a potential difference, allowing expansion costs to telescope over
paths and loops.

### Algorithm and representation separation

BLAKE2f's `ProofSupport` tree keeps its pure compression model independent of
bytecode and uses a representation predicate to hide its byte-array layout.
MODEXP also contains valuable bytecode-independent multi-limb definitions in
[`Reference/Proofs/Limbs.lean`](../../Challenge/Modexp/Reference/Proofs/Limbs.lean),
although they currently live under a reference-specific namespace.

## Current bottlenecks

### Artifact and path normalization

`ProgramArtifact.instructionPC` computes a program counter by assembling the
entire instruction prefix. Large downstream simplifications therefore normalize
large artifact terms repeatedly. Challenge proofs also commonly unfold
`runLocatedBlock`, `runLocated`, `runInstr`, the artifact, and the instruction
list together.

### Exposed execution plumbing

Proofs frequently establish executable success, lift it to relational
execution, then traverse the same path again for exact cost. Stable frame facts
such as code, fork, calldata, non-precompile status, and unchanged state fields
are repeatedly carried through block and loop lemmas. Frequent uses of
`GasSteps.cast` are another sign that endpoint-equality plumbing remains visible
to clients.

### Pointwise memory reasoning

The generic memory library contains correct read/write and disjointness lemmas,
but clients repeatedly reconstruct region-level invariants. This becomes much
more expensive for arrays of limbs, Fp2 values, extension-field elements, and
projective points.

### Challenge-specific arithmetic libraries

The generic word library contains some 32-bit-specific material, BLAKE2f has a
separate 64-bit layer, and MODEXP's broadly useful 256-bit limb algebra is
reference-specific. The new precompiles need width-independent bounded-word and
multi-limb results under a shared proof boundary.

### Deterministic-only direct endpoint

SHA256, RIPEMD160, and MODEXP use a direct endpoint that expects one returned
result. BLAKE2f requires a separate relational endpoint because malformed
inputs fail. The new precompiles also have validation failures, so the BLAKE2f
divergence would otherwise be repeated.

## Specification audit required before proving correctness

The pinned semantic implementation needs a conformance pass before it becomes
the target of nine correctness proofs.

Observed risks include:

- BLS pairing decoding currently omits subgroup checks;
- map-to-G1 and map-to-G2 comments say that cofactor clearing is omitted, while
  their implementations later perform cofactor multiplication;
- the pairing crypto module's gas comment disagrees with dispatcher pricing;
- the local dependency has only four pairing smoke identities and no
  substantial map, MSM, codec, or P256 vector suites.

The audit should cover every success and failure branch using primary vectors
from:

- [EIP-2537: BLS12-381 curve operations](https://eips.ethereum.org/EIPS/eip-2537)
- [RFC 9380: Hashing to Elliptic Curves](https://www.rfc-editor.org/rfc/rfc9380.html)
- [EIP-7951: P256VERIFY](https://eips.ethereum.org/EIPS/eip-7951)
- [EIP-7666: Identity precompile evmification](https://eips.ethereum.org/EIPS/eip-7666)

This should be completed before freezing each challenge's `Correct` predicate.

## Dependency map for the nine targets

| Targets | Shared foundation required |
| --- | --- |
| Identity | Generic initial state, calldata copy, return, memory expansion, and gas |
| P256VERIFY | One-word modular field operations, projective P-256, simultaneous scalar multiplication, encoding and validation |
| G1ADD, G1MSM, map-to-G1 | 381-bit multi-limb Fp, common codec, projective G1, scalar loops |
| G2ADD, G2MSM, map-to-G2 | Fp2 and projective G2, in addition to the base-field foundation |
| Pairing | Fp6/Fp12, Miller loop, sparse multiplication, Frobenius maps, final exponentiation, and a dynamic pair fold |

P256's field modulus fits in one EVM word, allowing `ADDMOD` and `MULMOD` to be
used directly. It is therefore a useful projective-curve proof before tackling
BLS multi-limb reduction.

BLS12-381's base-field modulus is 381 bits and cannot be represented by a
single EVM word. Efficient implementations need a specialized multi-limb
reduction layer. They also use projective/Jacobian formulas, whereas the pinned
semantic curve operations are affine and perform modular inversions during
addition and doubling. A reusable refinement from projective operations to the
affine specification is essential.

The inspected evmification implementation already reflects the intended shared
structure. It has common `Fp`, `Fp2`, `Fp6`, and `Fp12` libraries used by the
seven BLS implementations. Its base-field hot path represents a 48-byte value
as a 128-bit high limb and a 256-bit low limb and uses specialized Montgomery
multiplication for exponentiation.

## Architectural deepening candidates

All candidates are in-process dependencies: they are internal modules that can
be changed and tested in this repository or its pinned Lean dependencies.

### 1. Compositional block-execution and metering boundary

**Cluster:** `Stepper`, `Meter`, `GasSteps`, stable execution-frame facts, and
each challenge's trace helpers.

**Why these belong together:** executable paths, relational soundness, stable
state fields, and exact cost all describe one execution block. They are
currently exposed as several layers that downstream proofs manually assemble
and repeatedly normalize.

**Test impact:** replace repeated per-challenge execution, frame, cast, and cost
plumbing with boundary tests for:

- final observable state;
- exact cost and memory-potential equation;
- preservation of code, fork, calldata, and unrelated state fields;
- composition through branches and bounded loops;
- kernel-checkable relational soundness.

### 2. Shared typed-memory and multi-limb arithmetic

**Cluster:** `EvmProof.Memory`, bounded-word lemmas, BLAKE2f's memory
representation, and MODEXP's `Limbs` proofs.

**Why these belong together:** an arithmetic representation is only useful to
an EVM proof when its mathematical value is connected to loads, stores, array
updates, and frame preservation. BLS field and point values will otherwise
repeat the same byte-level reasoning in every challenge.

**Test impact:** introduce shared boundary tests for:

- fixed-width digit reconstruction;
- carries, borrows, and overflow bounds;
- modular addition, subtraction, multiplication, and reduction;
- canonical encodings;
- typed loads, stores, arrays, and structured regions;
- disjoint writes and preservation of unrelated regions.

### 3. Pure cryptographic refinement hierarchy

**Cluster:** base-field operations, Fp2/Fp6/Fp12, projective G1/G2, scalar
multiplication, MSM, maps, and pairing.

**Why these belong together:** the seven BLS challenges share the same field
and curve tower. Proving each optimized implementation directly against the
affine semantic definitions would repeat the hardest algebra. Field laws and a
projective-to-affine bridge should instead be established once.

RFC 9380's projective isogeny evaluation is especially relevant to the map
precompiles because it avoids modular inversions.

**Test impact:** organize proofs and executable tests around boundaries for:

- Fp representation and operations;
- Fp2, Fp6, and Fp12 component refinements;
- projective addition and doubling;
- scalar multiplication and MSM folds;
- simplified SWU and projective isogenies;
- Miller-loop steps, Frobenius maps, and final exponentiation.

### 4. Reusable codec and validation refinement

**Cluster:** EIP-2537 field/point codecs, calldata parsing, infinity handling,
curve and subgroup validation, result encoding, and failure behavior.

**Why these belong together:** all seven BLS challenges use the same 64-byte
field-element ABI and invalid-input rules. Duplicating these proofs would add
substantial code and make inconsistent validation behavior more likely.

**Test impact:** add primary conformance vectors covering:

- exact and malformed lengths;
- required padding;
- canonical and non-canonical field elements;
- infinity encodings;
- curve and subgroup membership;
- empty and multi-item MSM/pairing inputs;
- exact success output and failure behavior.

### 5. Compositional procedure contracts and relational endpoints

**Cluster:** source-level Yul proof support, compiler correctness,
`runLocatedBlock`, stable execution-frame properties, loops, and
`EventuallyEvaluates`.

**Why these belong together:** the verified Yul route avoids raw-bytecode
reasoning but currently leaves a large relational source execution proof.
Meanwhile, the direct proof route repeatedly exposes block frame facts and only
has a convenient endpoint for deterministic returned values.

Functional correctness and exact gas should share algorithm and representation
proofs but need not use the same final route:

- source/Yul semantics and compiler correctness can establish functional
  behavior;
- direct EVM execution proofs can establish exact gas for leaderboard scoring.

**Test impact:** add boundary tests and theorems for:

- reusable function and loop contracts;
- stable-frame preservation through blocks and loops;
- compiler transport of source behavior;
- a generic relation-valued execution endpoint covering both returns and
  exceptional results;
- reuse of one functional trace by exact-cost proofs where possible.

## Recommended implementation order

1. Audit the nine pinned specifications and add primary conformance vectors.
2. Deepen block-level execution, frame preservation, and exact-cost
   composition.
3. Prove Identity as the minimal end-to-end pilot for the new harness.
4. Extract shared typed-memory and limb arithmetic.
5. Prove P256VERIFY to develop projective-curve refinement without BLS
   multi-limb field arithmetic.
6. Build the BLS base-field and codec core.
7. Prove G1ADD, then G2ADD.
8. Prove G1MSM, then G2MSM.
9. Prove map-to-G1, then map-to-G2.
10. Prove pairing last, after the complete extension-field tower and curve
    machinery are available.

## Proof-development discipline

- Profile focused cold builds before and after infrastructure changes. Lean
  4.31 supports `set_option diagnostics true` and `trace.profiler.serve`;
  see the [Lean 4.31 release notes](https://lean-lang.org/doc/reference/latest/releases/v4.31.0/).
- Prefer short execution segments and compact theorem boundaries over
  normalizing complete artifact terms downstream.
- Use explicit `simp only` sets in expensive proofs so unrelated global simp
  lemmas do not change performance unpredictably.
- Treat large or unlimited heartbeat settings as diagnostics, not as the final
  solution to a proof-architecture problem.
- Keep `native_decide` out of the correctness core. Lean documents its native
  code dependency as a bespoke axiom; see
  [Axioms and computation](https://lean-lang.org/doc/reference/latest/Axioms/).
- Retain axiom-footprint checks for trusted infrastructure and final correctness
  theorems.

## Proposed decision sequence

Before starting the nine challenge implementations, decide the following in
order:

1. Whether the pinned semantics are authoritative as written or will be fixed
   to match primary specifications.
2. Which shared multi-limb representation and reduction strategy the BLS
   implementation will use.
3. Whether functional correctness will primarily follow the verified Yul route,
   direct bytecode blocks, or a combination of source correctness and direct
   metering.
4. The exact boundary between shared BLS field/curve proofs and
   challenge-specific execution proofs.
