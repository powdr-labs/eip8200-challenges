# BLS12-381 proof architecture research

Status: architecture study only. This document does not propose importing an external package or changing a proof until the affected module is benchmarked in this repository.

## Executive summary

The current BLS12-381 work does not primarily suffer from a lack of mathematics. It suffers from having three different kinds of boundaries represented in the same way:

1. public conceptual APIs, such as field multiplication or projective addition;
2. private proof stages introduced to keep Lean below its memory limit; and
3. generated certificate/data chunks introduced so closed computation fits in the kernel.

Those are all Lean files today, but they should not all be treated as public modules. The best architecture is therefore **fewer public concepts, not a single large physical module**. Keep expensive declarations, large numerals, and closed certificate checks behind separate `.olean` firebreaks. Put a small, deep facade in front of each subsystem, move reusable checking machinery out of individual challenges, and treat generated chunks as private artifacts.

The four external repositories support that conclusion:

- [`hex-dev`](https://github.com/kim-em/hex-dev/tree/43c95129f23a046fac9ee4f20e31288e718b4c14) has the strongest module and validation discipline: narrow computational libraries, separate Mathlib correspondence layers, independent conformance tests, and separate runtime and fresh-module proof benchmarks.
- [`leanprover/hex`](https://github.com/leanprover/hex/tree/9c1d1828fafa3d5edac2f2b30530e28805952f23) is the released aggregation repository. It is useful as dependency-layout evidence, not as a second implementation to copy.
- [`CompPoly`](https://github.com/Verified-zkEVM/CompPoly/tree/75c0681bd37567af00e8f0bd13fd59f1423e4217) provides an excellent executable-representation-to-mathematical-field boundary: definitions isolated from proofs, round invariants, one end-to-end `mul_spec`, and a `ringEquiv`. Its concrete BLS code is for the **255-bit scalar field**, not the 381-bit base field.
- [`CompElliptic`](https://github.com/daira/CompElliptic/tree/ac9b8e376a4c8a42b2d91e906c27c29a9aa15e15) provides reusable curve-level ideas: a generic `CoordinateSystem`, a short-Weierstrass group bridge, binary scalar multiplication, MSM refinement, and a focused axiom census. Its fast formulas are Pasta-specific and its optimized MSM is deliberately not needed for the first naive implementation here.

The highest-value near-term changes are:

1. Introduce deep public facades while retaining measured internal `.olean` stages.
2. Extract the duplicated G1/G2 projective formula core and the duplicated per-challenge certificate checker framework.
3. Give each executable arithmetic layer one small refinement contract—canonicality plus mathematical meaning—so downstream proofs rewrite with a theorem instead of unfolding the implementation.
4. Separate runtime definitions from Mathlib-heavy lawful proofs and from EVM source proofs.
5. Replace thousands of internal theorem-restatement checks with three deliberate gates: public API/trust checks, conformance vectors, and resource regression probes.
6. Keep naive scalar multiplication and naive MSM as the first correctness path. Add Pippenger only behind the same mathematical interface, after the naive challenges are complete and runtime measurements justify it.

The present staged design has already prevented a known `fpSub` proof from expanding toward roughly 20 GiB; the staged version was observed around 2.7 GiB. Any consolidation that crosses such a boundary must be considered a regression until cold-build peak RSS proves otherwise. See [Why concrete EVM proofs are expensive](why-concrete-evm-proofs-are-expensive.md).

## Scope, pins, and method

This review used the current workspace at commit `c775d05791138c6f754da082af82e6a1e3451dc4` on 2026-08-12. Concurrent G1ADD, G2ADD, and G1MSM work was active, so file counts are a snapshot rather than a permanent invariant. No broad build was run: two unrelated Lean workers were already using approximately 4.1 GiB and 3.7 GiB RSS during measurement. Static source/import inspection and existing `.olean` artifacts were used instead. All compile-memory recommendations below are marked as requiring a benchmark.

The four external repositories were cloned into an isolated temporary directory outside this workspace. They were not vendored and no submodule was changed.

| Repository | Pinned commit | Lean toolchain | Observed license/provenance | Compatibility note |
|---|---|---|---|---|
| `kim-em/hex-dev` | [`43c9512`](https://github.com/kim-em/hex-dev/commit/43c95129f23a046fac9ee4f20e31288e718b4c14) | `v4.33.0-rc1` | Root [`LICENSE`](https://github.com/kim-em/hex-dev/blob/43c95129f23a046fac9ee4f20e31288e718b4c14/LICENSE), Apache-2.0 | Two minor releases newer; its `module`/`public import`/`@[expose]` conventions need a Lean 4.31 spike. |
| `leanprover/hex` | [`9c1d182`](https://github.com/leanprover/hex/commit/9c1d1828fafa3d5edac2f2b30530e28805952f23) | `v4.33.0-rc1` | Root [`LICENSE`](https://github.com/leanprover/hex/blob/9c1d1828fafa3d5edac2f2b30530e28805952f23/LICENSE), Apache-2.0 | Aggregator/release repository; pin narrow component packages rather than importing `Hex`. |
| `Verified-zkEVM/CompPoly` | [`75c0681`](https://github.com/Verified-zkEVM/CompPoly/commit/75c0681bd37567af00e8f0bd13fd59f1423e4217) | `v4.33.0` | Root [`LICENSE`](https://github.com/Verified-zkEVM/CompPoly/blob/75c0681bd37567af00e8f0bd13fd59f1423e4217/LICENSE), Apache-2.0 | Fixed 8×32-bit Montgomery implementation and newer module system; proof pattern ports more directly than code. |
| `daira/CompElliptic` | [`ac9b8e3`](https://github.com/daira/CompElliptic/commit/ac9b8e376a4c8a42b2d91e906c27c29a9aa15e15) | `v4.30.0` | README says [Apache-2.0 or MIT](https://github.com/daira/CompElliptic/blob/ac9b8e376a4c8a42b2d91e906c27c29a9aa15e15/README.md#license), and source headers repeat that statement. The pinned tree does **not** contain the referenced root `LICENSE-APACHE` or `LICENSE-MIT` files. | Lean version is close. Selective technical porting is plausible, but copied code should preserve provenance and the missing-license-file discrepancy should be resolved before redistribution. |

The local toolchain is `v4.31.0`. This review treats all four repositories as candidate sources of reusable design and code, as requested, but it does not claim that an API compiles unchanged or that provenance questions have already been resolved.

## Current state and pain points

### Quantitative snapshot

| Area | Lean files | LOC | Files ≤20 LOC | Files ≤50 LOC | Files ≥500 LOC |
|---|---:|---:|---:|---:|---:|
| `Challenge/Bls12381/ProofSupport` | 134 | 14,613 | 14 | 41 | 0 |
| `Challenge/EvmProof` | 27 | 8,127 | 0 | 3 | 5 |
| `Challenge/Bls12381G1Add` | 80 | 8,072 | 24 | 48 | 3 |
| `Challenge/Bls12381G2Add` | 59 | 6,862 | 36 | 44 | 5 |
| `Challenge/Bls12381G1Msm` | 6 | 371 | 1 | 4 | 0 |

Small files alone are not evidence of bad architecture. The important question is whether a file provides one of these benefits:

- a cached opaque result that prevents downstream re-elaboration;
- a bounded closed computation or numeral payload;
- a stable interface separating source execution from mathematical refinement; or
- a meaningful reusable API.

If it provides none of them, it is likely shallow-module noise.

The largest existing `ProofSupport` `.olean` files make the distinction concrete. Prime-certificate chunks range from about 6.1 to 10 MB; individual root-evidence files are about 2.8–3.5 MB. [`LawfulAffine.lean`](../Challenge/Bls12381/ProofSupport/LawfulAffine.lean) is about 2.1 MB, [`Fp2SourceProgram.lean`](../Challenge/Bls12381/ProofSupport/Fp2SourceProgram.lean) about 1.1 MB, and [`LawfulFp6Norm.lean`](../Challenge/Bls12381/ProofSupport/LawfulFp6Norm.lean) about 1.0 MB. These are real cached proof payloads, not merely navigation overhead.

### What is already architecturally sound

Several local patterns should be preserved and generalized:

- [`Fp2SourceProgram.lean`](../Challenge/Bls12381/ProofSupport/Fp2SourceProgram.lean) defines an `Ops` interface and one authoritative `runMulWith`/`runInvWith` program, then proves direct, audited, and semantic views. This is exactly the “one program, multiple interpreters” architecture that should also guide round-based hash proofs.
- [`ScalarMulProgram.lean`](../Challenge/Bls12381/ProofSupport/ScalarMulProgram.lean) applies the same idea to scalar multiplication. It is already the right naive-first abstraction.
- [`SswuCore.lean`](../Challenge/Bls12381/ProofSupport/SswuCore.lean) separates generic definition-level SSWU machinery from the heavier lawful proofs in [`SswuCoreLawful.lean`](../Challenge/Bls12381/ProofSupport/SswuCoreLawful.lean).
- [`MapToG1Executable.lean`](../Challenge/Bls12381/ProofSupport/MapToG1Executable.lean) keeps the executable map separate from [`MapToG1Map.lean`](../Challenge/Bls12381/ProofSupport/MapToG1Map.lean), which proves curve and codec properties.
- [`LawfulAffine.lean`](../Challenge/Bls12381/ProofSupport/LawfulAffine.lean) explicitly documents the ideal long-term solution: upstream the missing generic affine facts instead of keeping a permanent project-local lawful shim. [`AffineGroup.lean`](../Challenge/Bls12381/ProofSupport/AffineGroup.lean) then bridges to Mathlib once.
- [`SpecRefinement.lean`](../Challenge/Bls12381G1Msm/SpecRefinement.lean) isolates decoder success/failure equations from the subgroup/MSM semantics in [`Spec.lean`](../Challenge/Bls12381G1Msm/Spec.lean). That is a useful seam.

### Essential resource firebreaks

These physical splits should remain unless a cold benchmark proves a replacement is cheaper:

1. **Large prime and root certificates.** The tiny source files have multi-megabyte `.olean`s. Combining them only makes a larger declaration environment and a worse invalidation unit.
2. **Closed byte-assembly and stack-certificate chunks.** G1ADD currently has 11 byte-assembly chunks and 10 stack-certificate chunks; G2ADD has 18 byte-assembly chunks, 15 stack-certificate chunks, and 3 frozen-data chunks. Each closed `decide` theorem is deliberately bounded.
3. **Large field identities and range proofs.** The documented `fpSub` incident shows why an apparently simple theorem must be staged through compact intermediate facts.
4. **Execution versus representation bridges.** Exact EVM/Yul execution carries large syntax, state, memory, and gas terms. It should consume opaque arithmetic refinement theorems rather than expose their proofs.
5. **Branch-sensitive composite refinements.** Decoder failure cases, exceptional affine branches, square-root branches, and source-control-flow joins are safer as measured declarations than as one broad `simp` proof.

The firebreak is the **opaque declaration and its compiled `.olean`**, not necessarily a permanently public module name. Internal files can remain while a facade gives downstream code a smaller conceptual API.

### Shallow noise and duplication

The following are good consolidation targets:

- [`Codec.lean`](../Challenge/Bls12381/ProofSupport/Codec.lean) is a 16-line compatibility umbrella importing seven codec modules. That umbrella is fine as a public facade, but downstream code should either use it deliberately or import the one narrow codec it needs; it should not coexist with many ad hoc partial umbrellas.
- [`G1Projective.lean`](../Challenge/Bls12381/ProofSupport/G1Projective.lean) and [`G2Projective.lean`](../Challenge/Bls12381/ProofSupport/G2Projective.lean) repeat the same Jacobian `Point`, infinity, conversion, double, and add structure over different fields/codecs. A generic definition-only core plus thin G1/G2 adapters would remove maintenance duplication without merging G1 and G2 lawful proofs.
- The G1ADD and G2ADD `FrozenStackCertificate`, `StackCertificateCore`, and `StackCertificateSound` layers repeat a challenge-independent compact length lookup, chunk decomposition, thawing, and soundness argument. Generated entries and final challenge names should remain local; the checker framework belongs under `Challenge/EvmProof`.
- Many files under individual `Reference/Proofs` directories are import-only wrappers or one-theorem forwarding stages. Keep a wrapper when it is a stable public name; otherwise replace it with a compatibility import/alias during migration and remove it after callers move.
- BLS-related `Checks` contained about 8,839 LOC, 68 direct check imports in [`Checks/Bls12381.lean`](../Checks/Bls12381.lean), and 1,553 occurrences of `#print axioms` or guarded-message commands at this snapshot. Rechecking every internal lemma's type and axioms makes the internal module graph part of the public contract. Checks should concentrate on headline APIs and trust boundaries.

## External repository findings

### `hex-dev`: narrow executable cores and explicit evidence lanes

The relevant arithmetic surface is small relative to the monorepo: `HexArith` has 13 Lean files/4,944 LOC, `HexModArith` 5/2,519, and `HexModArithMathlib` 2/406.

#### Reusable APIs and layout

[`HexArith/Montgomery/Context.lean`](https://github.com/kim-em/hex-dev/blob/43c95129f23a046fac9ee4f20e31288e718b4c14/HexArith/Montgomery/Context.lean) exposes:

- `r2OfModulus (p : UInt64) : UInt64`;
- `MontCtx.mk (p : UInt64) (hp : p % 2 = 1) : MontCtx p`;
- `toMont`, `fromMont`, and `mulMont` on `UInt64`;
- characterization theorems including `toNat_toMont`, `fromMont_repr`, `fromMont_toMont`, `mulMont_repr`, and `toNat_mulMont`.

The important design is not its single-word carrier. It is that clients use characterization theorems instead of unfolding reduction. [`HexModArithMathlib/ZMod64Equiv.lean`](https://github.com/kim-em/hex-dev/blob/43c95129f23a046fac9ee4f20e31288e718b4c14/HexModArithMathlib/ZMod64Equiv.lean) makes the boundary explicit:

```lean
def toZMod (a : Hex.ZMod64 p) : ZMod p
def ofZMod (a : ZMod p) : Hex.ZMod64 p
theorem ofZMod_toZMod (a : Hex.ZMod64 p) : ofZMod (toZMod a) = a
theorem toZMod_ofZMod (a : ZMod p) : toZMod (ofZMod a) = a
theorem toZMod_add (a b : Hex.ZMod64 p) : toZMod (a + b) = toZMod a + toZMod b
theorem toZMod_mul (a b : Hex.ZMod64 p) : toZMod (a * b) = toZMod a * toZMod b
def equiv : Hex.ZMod64 p ≃+* ZMod p
```

This is the right shape for `Fp`: executable representation first, one bridge to `Fin p`/`ZMod p`, then all curve proofs over the mathematical field.

Hex's testing doctrine is also directly reusable. [`SPEC/testing.md`](https://github.com/kim-em/hex-dev/blob/43c95129f23a046fac9ee4f20e31288e718b4c14/SPEC/testing.md) requires independent conformance and at least typical, edge, and adversarial cases per operation, keeps oracle generation outside library source, and bans `native_decide`. [`SPEC/benchmarking.md`](https://github.com/kim-em/hex-dev/blob/43c95129f23a046fac9ee4f20e31288e718b4c14/SPEC/benchmarking.md) separates compiled runtime benchmarks from fresh-module proof elaboration/kernel measurements. This repository should make the same distinction: “the EVM program runs faster” and “the proof elaborates with less peak RSS” are separate claims.

#### Risks and non-applicability

- The Montgomery implementation is one `UInt64`, not the BLS base field and not the current two-`UInt256` EVM representation.
- `@[extern]`, `@[implemented_by]`, or compiled accelerators cannot establish exact EVM source semantics. They may be used later as a separately proved implementation, never as an unproved replacement in the correctness path.
- Hex's Lean 4.33 module/exposure discipline is desirable, but `@[expose]` can increase unfolding. In this project, large program and certificate definitions should stay opaque; expose only cheap equations or constructor-level definitions.
- Do not add the aggregate `Hex` dependency just for a narrow arithmetic component. [`leanprover/hex`](https://github.com/leanprover/hex/tree/9c1d1828fafa3d5edac2f2b30530e28805952f23) demonstrates that released libraries can be pinned independently.

### `CompPoly`: a strong field refinement boundary, but the wrong concrete BLS field

The BLS-specific directory contains only two files/114 LOC:

- [`BLS12_381/Basic.lean`](https://github.com/Verified-zkEVM/CompPoly/blob/75c0681bd37567af00e8f0bd13fd59f1423e4217/CompPoly/Fields/BLS12_381/Basic.lean) defines `scalarFieldSize`, `ScalarField := ZMod scalarFieldSize`, and `ScalarField_is_prime` using a Pratt certificate.
- [`BLS12_381/Fast.lean`](https://github.com/Verified-zkEVM/CompPoly/blob/75c0681bd37567af00e8f0bd13fd59f1423e4217/CompPoly/Fields/BLS12_381/Fast.lean) instantiates an eight-32-bit-limb Montgomery field, then exposes `Fast.ScalarField`, `ofField`, and `ringEquiv`.

This modulus is the BLS12-381 scalar modulus `r`, not the 381-bit base modulus `p`. It cannot replace the local base field, Fp2, maps, or curve code.

#### Reusable proof organization

The generic Montgomery directory has 9 files/3,146 LOC. [`Native64x8Defs.lean`](https://github.com/Verified-zkEVM/CompPoly/blob/75c0681bd37567af00e8f0bd13fd59f1423e4217/CompPoly/Fields/Montgomery/Native64x8Defs.lean) deliberately has zero imports so native precompilation does not pull in a proof closure. [`Native64x8Mul.lean`](https://github.com/Verified-zkEVM/CompPoly/blob/75c0681bd37567af00e8f0bd13fd59f1423e4217/CompPoly/Fields/Montgomery/Native64x8Mul.lean) proves `mulAccum_spec`, `mulReduce_spec`, and `mulRound_spec` before one end-to-end theorem:

```lean
theorem mul_spec (q : Limbs8) (negInv : UInt64) (a b : Limbs8)
    (hq : q.Bounded) (ha : a.Bounded) (hb : b.Bounded)
    (hn : negInv.toNat < 2 ^ 32)
    (hnq : negInv.toNat * q.toNat % 2 ^ 32 = 2 ^ 32 - 1)
    (haq : a.toNat < q.toNat) (hq2 : 2 * q.toNat < 2 ^ 256) :
    (mul q negInv a b).Bounded ∧ (mul q negInv a b).toNat < q.toNat ∧
      2 ^ 256 * (mul q negInv a b).toNat ≡
        a.toNat * b.toNat [MOD q.toNat]
```

That result bundles exactly the facts downstream clients need: representation bounds, canonicality, and modular meaning. [`Native64x8Field.lean`](https://github.com/Verified-zkEVM/CompPoly/blob/75c0681bd37567af00e8f0bd13fd59f1423e4217/CompPoly/Fields/Montgomery/Native64x8Field.lean) packages constants in `Mont64x8Field`, defines the bounded `FastField` carrier, proves `toField_add`/`toField_mul` and inverse laws, and transfers a `Field` instance over `ringEquiv`.

The local Fp source proof should copy this **theorem shape and staging**, adapted to two 256-bit limbs and the exact EVM arithmetic. It should not copy the fixed carrier.

#### Hard incompatibilities

- `Limbs8` is 8×32 = 256 bits. Its class requires `2 * modulus < 2^256`; BLS base `p` is 381 bits, so the premise is impossible.
- It proves a native/Lean executable, not the exact Yul/EVM schedule. A later optimized implementation would still need a refinement to the source program used by the challenge.
- It uses Lean 4.33 `module`, `public section`, and intentional `@[expose]` declarations. Port the abstraction in a small 4.31 experiment before changing local modules.
- The `Field` instance is useful for abstract consumers but could cause typeclass search to import too much into runtime/source modules. Keep the bridge on the proof side.

CompPoly's [`module-system.md`](https://github.com/Verified-zkEVM/CompPoly/blob/75c0681bd37567af00e8f0bd13fd59f1423e4217/docs/wiki/module-system.md), [`typeclass-minimization.md`](https://github.com/Verified-zkEVM/CompPoly/blob/75c0681bd37567af00e8f0bd13fd59f1423e4217/docs/wiki/typeclass-minimization.md), and [`build-cache.md`](https://github.com/Verified-zkEVM/CompPoly/blob/75c0681bd37567af00e8f0bd13fd59f1423e4217/docs/wiki/build-cache.md) reinforce three local rules: imports should be narrow, opaque definitions should be characterized rather than unfolded, and measurement should build a narrow target from a known cache state.

### `CompElliptic`: generic group scaffolding and later optimization seams

The repository has 27 Lean files/7,106 LOC under `CompElliptic`. Its value is the generic interface around formulas, not a ready BLS implementation.

#### Generic coordinate and affine layers

[`CoordinateSystem.lean`](https://github.com/daira/CompElliptic/blob/ac9b8e376a4c8a42b2d91e906c27c29a9aa15e15/CompElliptic/CoordinateSystem.lean) defines:

```lean
structure CoordinateSystem (R : Type u) where
  Valid : R → Prop
  Rel : R → R → Prop
  zero : R
  add : R → R → R
  neg : R → R
  valid_zero : Valid zero
  valid_add : Valid a → Valid b → Valid (add a b)
  valid_neg : Valid a → Valid (neg a)
  -- equivalence, congruence, and group laws modulo Rel
```

It constructs a subtype of valid representations, quotients by `Rel`, and derives an `AddCommGroup` once. This is a good model for a generic Jacobian core: formulas and validity remain executable; the abstract group law is downstream and proof-only.

[`CurveForms/ShortWeierstrass.lean`](https://github.com/daira/CompElliptic/blob/ac9b8e376a4c8a42b2d91e906c27c29a9aa15e15/CompElliptic/CurveForms/ShortWeierstrass.lean) packages raw `OnCurve`, `Valid`, `neg`, `add`, `smul`, the `SWCurve`/`SWPoint` types, conversion to Mathlib, and the main `valid_add`, `add_assoc`, and `toPt_add` results. This overlaps heavily with local [`LawfulAffine.lean`](../Challenge/Bls12381/ProofSupport/LawfulAffine.lean) and [`AffineGroup.lean`](../Challenge/Bls12381/ProofSupport/AffineGroup.lean).

Selective porting could reduce local lawful maintenance, but replacement is not free: the local point type has an explicit `.infinity`, while CompElliptic uses an affine sentinel convention; local Fp2 and wire-codec bridges would remain. The safe path is to compare theorem surfaces and upstream or adapt missing generic lemmas, preserving current local theorem names as aliases. Do not rewrite all BLS proofs around a new point representation merely to remove the word “Lawful”.

#### Scalar multiplication and MSM

[`ScalarMul.lean`](https://github.com/daira/CompElliptic/blob/ac9b8e376a4c8a42b2d91e906c27c29a9aa15e15/CompElliptic/ScalarMul.lean) provides:

```lean
def linNsmul (add : M → M → M) (zero : M) : ℕ → M → M
def binNsmul (add : M → M → M) (zero : M) (n : ℕ) (x : M) : M
theorem binNsmul_eq_linNsmul (n : ℕ) (x : M) :
  binNsmul add zero n x = linNsmul add zero n x
```

The local [`ScalarMulProgram.lean`](../Challenge/Bls12381/ProofSupport/ScalarMulProgram.lean) already has a richer “multiple interpreters plus audit” structure. Prefer the local program and compare its algebraic theorem against `binNsmul_eq_linNsmul`; importing a second scalar algorithm now would add concepts without removing proof work.

[`Curves/Pasta/Fast/Msm.lean`](https://github.com/daira/CompElliptic/blob/ac9b8e376a4c8a42b2d91e906c27c29a9aa15e15/CompElliptic/Curves/Pasta/Fast/Msm.lean) is generic over an additive commutative monoid for much of its surface:

```lean
def naiveMsm (terms : List (ℕ × M)) : M
def pippenger (c : ℕ) (terms : List (ℕ × M)) : M
theorem pippenger_eq_msm (c : ℕ) (hc : 0 < c) (terms : List (ℕ × M)) :
  pippenger c terms = (terms.map fun t => t.1 • t.2).sum
def pippengerFast (c : ℕ) (terms : List (ℕ × M)) : M
theorem pippengerFast_eq_msm ...
```

[`MsmProj.lean`](https://github.com/daira/CompElliptic/blob/ac9b8e376a4c8a42b2d91e906c27c29a9aa15e15/CompElliptic/Curves/Pasta/Fast/MsmProj.lean) adds `pippengerProj_eq_msm`. These are credible later optimization candidates. For the first G1MSM/G2MSM proofs, the user-selected naive fold is better: it has a smaller state invariant, matches [`MsmSemantics.lean`](../Challenge/Bls12381/ProofSupport/MsmSemantics.lean), and avoids window/bucket proof and source complexity. The interface should make a later Pippenger implementation prove equality to the same `List` sum without changing specifications.

#### Projective formulas, order proofs, and trust

[`Curves/Pasta/Fast/Projective.lean`](https://github.com/daira/CompElliptic/blob/ac9b8e376a4c8a42b2d91e906c27c29a9aa15e15/CompElliptic/Curves/Pasta/Fast/Projective.lean) proves `valid_padd`, `toAffine_padd`, `pnsmulFast_spec`, and `smulFast_eq`. The concrete complete formula is specialized to the Vesta/Pasta curve (`a = 0`, `b = 5`) and must not be assumed correct for BLS G1 or G2. Its architecture—raw formula, validity, affine refinement, scalar refinement—is reusable.

It also records an important performance result: a raw-`Nat` formula was about 17× slower under the interpreted/`native_decide` execution tier despite being intended as a fast path; many small interpreted operations lost to fewer GMP-backed operations. The lesson is general: benchmark in the execution context that matters. A source-level micro-optimization may worsen proof evaluation or elaboration.

[`CurveOrder.lean`](https://github.com/daira/CompElliptic/blob/ac9b8e376a4c8a42b2d91e906c27c29a9aa15e15/CompElliptic/CurveOrder.lean) provides `dvd_natCard_of_prime_witness`, `card_eq_of_prime_witness`, `card_eq_of_prime_witness_of_lt_three_mul`, `card_fibre_le_two`, and `card_le_two_mul_card_add_one`. These can inform subgroup infrastructure, but they do not directly prove BLS full-group/cofactor facts: the BLS curve groups and their subgroup/cofactor relationship require the correct non-prime full group order and extension-field reasoning.

Finally, [`Meta/AxiomCheck.lean`](https://github.com/daira/CompElliptic/blob/ac9b8e376a4c8a42b2d91e906c27c29a9aa15e15/CompElliptic/Meta/AxiomCheck.lean) and [`TrustBoundary.lean`](https://github.com/daira/CompElliptic/blob/ac9b8e376a4c8a42b2d91e906c27c29a9aa15e15/CompElliptic/TrustBoundary.lean) show a better pattern than repeating `#print axioms` for every internal lemma: write one deliberate census over the public results. CompElliptic permits narrowly classified `native_decide` facts; this repository's stricter core policy should remain. Reuse the census mechanism, not the trust relaxation.

### Comparison matrix

| Concern | Current repository | Hex | CompPoly | CompElliptic | Recommended decision |
|---|---|---|---|---|---|
| Executable/proof separation | Present in Fp2, SSWU, maps; uneven elsewhere | Strong Mathlib-free/bridge split | Strong `Defs`/proof split | Present in projective Montgomery lane | Adopt consistently now. |
| Field representation bridge | `Refines`, `Canonical`, `toField`; multiple theorem layers | `toZMod` plus ring equivalence | `FastField` plus `ringEquiv` | Vendored CompPoly for Pasta | Deepen local facade; selectively port theorem organization. |
| Exact BLS base field code | Local two-word/EVM-aware code | No | No—scalar `r`, 256-bit only | No | Keep local implementation. |
| Generic affine/group theory | Local lawful shim + Mathlib bridge | Not central | Not central | Strong SW/coordinate APIs | Compare/selectively upstream; preserve local explicit-infinity API. |
| Projective formulas | Duplicated G1/G2 definition modules | No | No | Strong but Pasta-specific | Extract local generic Jacobian core; use CompElliptic as API guide only. |
| Scalar multiplication | Naive authoritative program + audit | No relevant curve API | No | Generic binary refinement | Keep local naive path; align headline theorem. |
| MSM | Naive fold semantics | No | No | Naive and Pippenger proofs | Naive now; selectively port Pippenger later behind same spec. |
| Conformance | Official-vector checks exist | Very strong independent oracle discipline | Tests/build docs | Trust-focused | Adopt Hex's typical/edge/adversarial and oracle rules. |
| Trust checking | Very many local `#print axioms` guards | Project-wide bans and checks | Standard proof discipline | Focused census | Consolidate to public theorem census. |
| Memory evidence | Incident docs and staged modules | Fresh proof probes | Narrow cache/build guidance | Some execution measurements | Add repeatable per-boundary resource probes. |
| Module system | Lean 4.31 traditional imports | 4.33 public/opaque modules | 4.33 public/opaque modules | 4.30 traditional imports | Benchmark 4.31-compatible facades now; do not upgrade as part of this refactor. |

## Recommended target architecture

The target has two graphs:

- a **small public conceptual graph** used by challenge authors; and
- a **larger private compilation graph** whose boundaries are chosen by memory evidence.

Changing directory names is not the first step. Create facades and generic cores while leaving compatibility imports and theorem aliases so active proofs continue to build.

```text
Challenge/
├── EvmProof/
│   ├── Execution.lean                 # public execution contracts
│   ├── Gas.lean                       # public gas contracts
│   ├── Limbs.lean
│   ├── MemoryRegion.lean
│   ├── Certificate.lean               # deep public certificate API
│   ├── Certificate/
│   │   ├── CompactStack.lean           # generic data/checker/soundness
│   │   └── Internal/
│   │       └── Chunking.lean           # take/drop/check combinators
│   └── Source/
│       ├── Contract.lean               # pre/post stage contract
│       └── Procedure.lean              # source-program interpreter API
│
├── Bls12381/
│   └── ProofSupport/
│       ├── Codec.lean                  # public wire API
│       ├── Field.lean                  # public Fp/Fp2/Fp6/Fp12 refinement API
│       ├── Curve.lean                  # public affine/projective/group API
│       ├── Scalar.lean                 # scalar mul + naive MSM API
│       ├── Map.lean                    # map-to-curve API
│       ├── Field/
│       │   └── Internal/               # existing measured arithmetic stages
│       ├── Curve/
│       │   ├── JacobianCore.lean       # definition-only generic formulas
│       │   ├── G1.lean                 # thin constants/codec adapter
│       │   ├── G2.lean
│       │   └── Internal/               # expensive lawful/refinement stages
│       ├── Scalar/
│       │   ├── Program.lean            # authoritative naive program
│       │   └── Semantics.lean
│       ├── Map/
│       │   ├── Core.lean               # generic SSWU/isogeny interfaces
│       │   ├── G1.lean
│       │   └── G2.lean
│       └── Generated/
│           └── PrimeCertificate/...    # private checked data chunks
│
└── Bls12381G1Add/
    └── Reference/Proofs/
        ├── Compilation.lean            # challenge adapter
        ├── FrozenProgram.lean           # local program/data identity
        ├── CertificateData/...          # generated private chunks
        ├── Refinement.lean              # operation-specific composition
        ├── Correctness.lean
        └── Gas.lean
```

“Internal” here is an ownership convention that can be introduced before the Lean module-system upgrade. Existing import paths can remain as forwarding modules during migration. “Generated” does not mean trusted: generation is outside the trusted base, and a small kernel-checked theorem validates the payload.

### Deep field interface

Downstream curve and EVM proofs should need a compact surface resembling:

```lean
namespace Bls12381.Fp

structure Repr where
  lo : UInt256
  hi : UInt256

def toField : Repr → Fin p
def Canonical : Repr → Prop

theorem add_spec (a b : Repr) (ha : Canonical a) (hb : Canonical b) :
    Canonical (addSource a b) ∧
      toField (addSource a b) = toField a + toField b

theorem mul_spec (a b : Repr) (ha : Canonical a) (hb : Canonical b) :
    Canonical (mulSource a b) ∧
      toField (mulSource a b) = toField a * toField b

end Bls12381.Fp
```

The exact names should alias current public theorems rather than force a mass rename. The crucial property is that the source proof consumes `mul_spec`; it does not unfold schoolbook multiplication, Montgomery rounds, or normalization. Each internal round may remain a separate file if it is a measured firebreak.

For Fp2 and higher extensions, use the same shape and keep `LawfulFp2`/Fp6/Fp12 implementation details behind `toField_*` or `toLawful_*` headline theorems. Avoid a highly polymorphic typeclass framework for one EVM schedule: generalize where it removes G1/G2 duplication, not where it merely moves parameters into instance search.

### Deep curve interface

The generic Jacobian layer should parameterize the field operations and curve constants, but should not know wire widths or codecs:

```lean
structure JacobianParams (F : Type) where
  a b : F

structure Jacobian (F : Type) where
  x y z : F

def Jacobian.infinity [Zero F] [One F] : Jacobian F
def Jacobian.add (params : JacobianParams F) : Jacobian F → Jacobian F → Jacobian F
def Jacobian.double (params : JacobianParams F) : Jacobian F → Jacobian F

theorem Jacobian.add_refines ... :
  Valid p → Valid q → Rel (add params p q) (affineAdd params p q)
```

G1 and G2 modules instantiate `F`, `a`, and `b` and prove the bridge to their existing explicit-infinity wire points. Formula families should be explicit parameters or separate named implementations; do not silently reuse a formula whose completeness assumptions differ over Fp and Fp2.

CompElliptic's `CoordinateSystem` is a strong candidate for selective porting if its quotient/group construction removes more local proof than the bridge costs. First compare a minimal adapter for the existing local Jacobian type. Preserve the current public `G1Projective.*`, `G2Projective.*`, `G1Affine.*`, and `G2Affine.*` names as aliases.

### Deep certificate interface

Challenge code should supply data and receive a bounded validity theorem:

```lean
structure CompactStackCertificate where
  entries : List FrozenStackEntry
  initial : FrozenCertValue

def CompactStackCertificate.check
    (assembly : List Asm) (cert : CompactStackCertificate) : Bool

theorem CompactStackCertificate.sound
    (h : cert.check assembly = true) :
    (cert.toCert assembly).Valid
```

The current `stackKeyChecks`, `stackIndexedEntryChecks`, `all_take_drop`, thawing, lookup-by-suffix-length, and final soundness proof should live once under [`Challenge/EvmProof`](../Challenge/EvmProof). Each challenge retains:

- frozen assembly and bytes;
- frozen certificate entries;
- generated data and `decide` chunks;
- the final aliases `referenceCheckedCert_valid`, `referenceCheckedCert_bounded`, and bytecode equality, so existing checks do not break.

Do not concatenate generated entries into one enormous source term during elaboration. If the list must be logically whole, assemble it from opaque chunk constants and prove a shallow append theorem.

### Source/EVM stage contracts

The public unit of composition should be a state transition theorem, not a trace expansion:

```lean
structure StageContract (State : Type) where
  pre : State → Prop
  post : State → State → Prop
  cost : Nat

theorem execute_stage
    (hpre : contract.pre s) :
    ∃ s', Runs code s s' ∧ contract.post s s' ∧ gasUsed s s' = contract.cost
```

Arithmetic/source stages can additionally prove that their postcondition refines a mathematical operation. The final challenge correctness theorem composes stage contracts; the gas theorem sums the same `cost` fields. This avoids rerunning the full symbolic execution once for correctness and again for gas.

The first complete G2 `fp2Add` caller migration refines this recommendation.
An executable symbolic caller cannot generally use a `Classical.choose` final
state without making every later state definition noncomputable. Use a
computable representative, prove its selected execution/output/frame
characterizations once, then make the representative irreducible. Reserve the
existential theorem for proof-facing consumers.

This migration was memory-neutral: `SourceOnCurveRhs` remained at roughly
2.68 GiB warm RSS. The result separates two claims that must not be conflated:
the contract prevents consumers from constructing the exact `fp2Add` graph,
but it does not remove the imported environment or the exact bridge modules.
An RSS win requires a measured target whose peak was caused by the eliminated
construction, or a smaller import closure. A general in-place/output-order
corollary did remove two caller-specific `onCurve` input adapters; the exact
`fp2Add` stages are not removable until the remaining finite/double exact-state
consumers migrate.

## Staged migration plan

### Stage 0: establish evidence before moving files

1. Record current cold and warm build wall time and peak RSS for one representative module in each class: Fp arithmetic, Fp2 lawful bridge, G1ADD source stage, byte chunk, stack chunk, and final correctness.
2. Record direct/transitive dependency counts and `.olean` sizes.
3. Use one job and a hard memory monitor. Stop/refactor a process before 6 GiB; do not let a proposed consolidation reproduce the historical `fpSub` blow-up.
4. Save measurement metadata: commit, Lean version, command, cache state, wall time, maximum RSS, and whether other Lean workers were running.

No architecture claim about memory is accepted without this baseline.

### Stage 1: add facades without changing implementation

Add `Field.lean`, `Curve.lean`, `Scalar.lean`, `Map.lean`, and `EvmProof/Certificate.lean` as carefully chosen public surfaces. Existing modules remain authoritative; facades import only stable headline APIs. Update one leaf challenge at a time, starting with G1MSM because its proof surface is still small.

Validation: public theorem names and `#print axioms` results remain unchanged; import closure and peak RSS must not materially increase.

### Stage 2: extract challenge-independent certificate code

Move or copy-then-deprecate the generic compact certificate definitions and soundness lemmas into `Challenge/EvmProof`. Parameterize assembly, frozen entries, and chunk partition. Keep challenge data and chunk theorems local. Provide aliases under the original namespaces.

This is high benefit and low mathematical risk because G1ADD and G2ADD already contain near-identical frameworks. It should be done before more BLS challenges clone them.

### Stage 3: extract the generic Jacobian definition core

Create one definition-only core and instantiate it for G1 and G2. First prove definitional or extensional equivalence to the current `double` and `add`, then redirect new code. Do not combine G1/G2 lawful proofs initially. Benchmark the new import closure: abstraction can make terms larger through projections even when source LOC falls.

Only after the equivalence layer is stable should duplicate old definitions be deprecated.

### Stage 4: deepen field contracts

For each Fp operation, publish one bundled canonicality/refinement theorem. Keep the existing internal stage files and adapt current theorems into this surface. Then make Fp2 source refinements consume those contracts only. Split executable definitions from lawful/Mathlib imports where they are currently mixed.

This stage should use CompPoly's `mulRound_spec` → `mul_spec` → `ringEquiv` organization as a template, but retain the local representation and EVM schedule.

### Stage 5: reduce check noise

Replace per-internal-lemma restatement modules with:

1. `Checks.Bls12381PublicApi`: selected theorem types and compatibility names;
2. `Checks.Bls12381Trust`: a programmatic axiom census over headline theorems;
3. `Checks.Bls12381Conformance`: official vectors plus typical/edge/adversarial failures and gas boundaries; and
4. resource probes run separately because they measure performance rather than logical truth.

Retain a fine-grained check only when it guards a real regression: theorem statement, trust set, branch behavior, official vector, or previously expensive compile boundary.

### Stage 6: evaluate external curve reuse

Create a small non-production compatibility spike for CompElliptic's `CoordinateSystem` and short-Weierstrass surface on the current Lean version. Measure:

- how many local lawful theorems become direct instances;
- the adapter LOC for explicit infinity, Fp2, and wire points;
- transitive imports and peak RSS; and
- whether public theorem statements remain simple.

If the bridge costs more than it removes, upstream the missing generic Mathlib lemmas instead and keep the local facade. In either outcome, retain comments explaining that upstream support is the ideal end state.

### Stage 7: optimize only behind stable specifications

Once naive G1MSM and G2MSM are proved, an optimized Pippenger implementation can target the same `List`-sum theorem. Likewise, a native Montgomery carrier can target the same `toField` contract. Runtime speed, source byte size, gas, elaboration time, and peak RSS must all be measured independently. An optimization should be revertible without changing the challenge specification.

## Repository-wide rules

### Module and import rules

1. A public module represents a user concept; an internal module represents a compilation boundary. Do not equate public API count with physical file count.
2. Runtime/program definitions import the smallest definition-level dependencies possible. Mathlib-heavy lawful and equivalence proofs import runtime modules, never the reverse.
3. Put large constants and generated certificates in data-only modules. Their checkers are generic and small.
4. Default large definitions to opaque across module boundaries. Export cheap characterization equations rather than encouraging `unfold`.
5. Expose a definition body only after demonstrating a downstream need and measuring the effect. `@[expose]` is a tool, not a default.
6. Avoid broad `Mathlib.Tactic` and broad `simp`; use precise imports and `simp only` at expensive boundaries.
7. Use the weakest algebraic typeclass assumptions needed by an algorithm. Do not pull field/finite-field instances into a source module that only needs `Add`, `Mul`, and constants.
8. Preserve theorem names with aliases during migration so check guards and active proofs are not rewritten simultaneously.

### Field and curve rules

1. Every executable representation has a total interpretation function (`toField`, `toAffine`) and an explicit representation invariant (`Canonical`, `Valid`).
2. Each primitive operation publishes one bundled result containing output validity/canonicality and mathematical meaning.
3. Prove a generic round/step invariant before instantiating large constants.
4. Separate affine/projective formula correctness from codecs and EVM memory layout.
5. State every exceptional case: infinity, zero divisor, equal/opposite points, square-root branch, invalid padding, non-subgroup point.
6. Reuse generic group scaffolding only when its point-at-infinity convention and formula completeness assumptions are explicit.
7. Keep naive algorithms as executable specifications. Optimized algorithms prove equality to them or to the same mathematical result.
8. Do not use CompPoly's BLS scalar field as the BLS base field and do not use Pasta-specific projective formulas for BLS.

### Concrete source/EVM proof rules

1. Write one authoritative parametric program and obtain direct, audited, symbolic-source, and mathematical views through interpreters when practical.
2. Split symbolic execution at semantic state contracts: decoded input, canonical field value, completed arithmetic primitive, stored output—not at arbitrary source line counts.
3. Keep arithmetic refinement opaque before introducing the full EVM state and syntax term.
4. Prove memory-region and gas facts from the same stage contracts used for functional correctness.
5. Prefer named projection/update lemmas over normalizing a whole nested EVM state.
6. Never use unrestricted `simp`, `unfold`, `dsimp`, or `with_unfolding_all` over a large source graph. The last is acceptable only for a bounded, closed certificate chunk whose peak RSS is recorded.
7. When a composite proof spikes, first isolate the first large intermediate term and cache a smaller semantic lemma. Increasing heartbeats does not solve retained-term memory.

### Certificate and generated-data rules

1. Generators are outside the trusted base; small kernel-checked checkers validate their output.
2. Chunk size is a measured parameter. Keep the checker theorem generic so rechunking does not change semantics.
3. Never make downstream correctness depend on reducing the entire frozen list. Provide opaque chunk summaries and one shallow composition theorem.
4. Version generated payloads by source/assembly hash and fail if the identity no longer matches.
5. Keep byte equality, stack validity, stack bound, and source refinement as separate certificates; one change should not invalidate unrelated evidence.

### Trust, conformance, and measurement rules

1. The public trust census lists final correctness, gas, field/curve bridge, and certificate-soundness theorems. Internal helper axioms are reached through those roots.
2. Keep `native_decide` out of the core correctness path. Compiled evaluation is not a substitute for exact source semantics.
3. For each externally visible operation, test at least typical, edge, and adversarial inputs. Include malformed lengths/padding and infinity/subgroup cases for BLS codecs.
4. Cross-check generated expected outputs with an independent implementation and record oracle version/provenance.
5. Measure compiled execution separately from proof elaboration and kernel checking.
6. For memory comparisons use `/usr/bin/time -v`, `-Kjobs=1`, a narrow target, recorded cache state, and no concurrent Lean workers. Compare maximum RSS and wall time; `.olean` size and import count are supporting signals, not substitutes.
7. Mark every refactor that changes an import, opacity boundary, large proof, or chunk size **benchmark required** until cold and warm evidence is collected.
8. A 6 GiB per-process ceiling is a design constraint. Terminate or restage a proof approaching it; do not normalize a 20 GiB term because the machine happens to have enough RAM.

## Applying the rules to RIPEMD-160, MODEXP, BLAKE2F, and SHA-256

The same architecture applies beyond BLS:

- Move the generic material in [`Challenge/Modexp/Reference/Proofs/Limbs.lean`](../Challenge/Modexp/Reference/Proofs/Limbs.lean) toward [`Challenge/EvmProof/Limbs.lean`](../Challenge/EvmProof/Limbs.lean) once theorem names and imports are audited. MODEXP-specific big-number loop invariants remain in MODEXP.
- Treat RIPEMD-160 and SHA-256 compression schedules as authoritative parametric programs with direct and EVM interpreters. Round-group modules should publish state-transition theorems, not expose expanded 64/80-round terms.
- BLAKE2F's `MixG`, round, initialization, output, and gas layers already suggest semantic stages. Their public facade should expose the operation contracts while preserving separate `.olean`s for expensive execution proofs.
- Hash proof chunking should follow state boundaries (message schedule prepared, N rounds complete, state accumulated), not merely a fixed number of syntax nodes.
- Gas proofs should reuse the same stage decomposition and per-stage cost theorem instead of building an independent full trace.
- Generated instruction/stack certificates for all precompiles should use the same `EvmProof.Certificate` checker and challenge-local data.
- Conformance should distinguish the mathematical algorithm from byte-level precompile behavior, including short input, padding, endian conversion, and gas failure.

The existing deep directories under [`Challenge/Sha256/Reference/Proofs/Bytecode`](../Challenge/Sha256/Reference/Proofs/Bytecode), [`Challenge/Ripemd160/Reference/Proofs/Bytecode`](../Challenge/Ripemd160/Reference/Proofs/Bytecode), [`Challenge/Blake2f/Reference/Proofs/Bytecode`](../Challenge/Blake2f/Reference/Proofs/Bytecode), and [`Challenge/Modexp/Reference/Proofs/Bytecode`](../Challenge/Modexp/Reference/Proofs/Bytecode) should therefore be reviewed with the same question: which files cache essential state contracts, and which merely forward an internal theorem? The goal is a smaller public graph, not indiscriminate file deletion.

## Prioritized action list

`Benchmark required` means the change must not land on architectural intuition alone.

| Priority | Action | Expected benefit | Risk | Affected paths | Prerequisite | Validation |
|---:|---|---|---|---|---|---|
| 1 | Extract generic compact stack-certificate checker/soundness into `EvmProof`; keep data chunks local. | High reuse before seven BLS challenges duplicate it; smaller maintenance surface. | Low–medium; abstraction may enlarge terms. **Benchmark required.** | `Challenge/EvmProof`, G1ADD/G2ADD `Reference/Proofs/*Certificate*` | Baseline one G1 and G2 chunk plus final soundness RSS. | `lake -Kjobs=1 build +Challenge.Bls12381G1Add.Reference.Proofs.StackCertificateSound` and G2 equivalent; compare RSS and `#print axioms`. |
| 2 | Add deep `Field`, `Curve`, `Scalar`, `Map`, and `Certificate` facades with compatibility aliases. | High navigability; lets later challenges depend on stable concepts. | Low if imports remain narrow; umbrella imports can bloat closure. **Benchmark required.** | `Challenge/Bls12381/ProofSupport`, `Challenge/EvmProof` | Record import closures for representative current leaf modules. | `lake env lean --deps <leaf>.lean`; build leaf and final checks with one job. |
| 3 | Publish one bundled canonicality/refinement theorem per Fp operation. | Very high proof simplification; stops implementation unfolding in Fp2/EVM layers. | Medium proof work; theorem statements must match source invariants. | `Fp*`, `Fp2Source*`, G1/G2 source arithmetic proofs | Choose stable `Canonical`/`toField` contract. | Build operation theorem, Fp2 lawful consumer, then one EVM consumer; ensure no broad unfolding. |
| 4 | Extract definition-only generic Jacobian core; preserve G1/G2 aliases. | Medium–high reduction in formula duplication; single optimization seam. | Medium; parameter projections can hurt elaboration and formula assumptions may differ. **Benchmark required.** | `G1Projective.lean`, `G2Projective.lean`, new internal curve core | Extensional equivalence test for current formulas. | Build G1/G2 projective checks and one add challenge each; compare peak RSS/`.olean`. |
| 5 | Consolidate BLS Checks into public API, trust census, conformance, and resource gates. | High signal-to-noise improvement; internal refactors stop causing mass check churn. | Medium; can accidentally drop a meaningful regression guard. | `Checks/Bls12381*.lean` | Classify each existing guard by public/trust/vector/resource purpose. | `lake build Checks.Bls12381 Checks.Bls12381Conformance`; census must cover final roots. |
| 6 | Split remaining executable definition layers from Mathlib lawful bridges. | Medium import-closure and native-compilation improvement. | Medium; moving definitions may change reducibility. **Benchmark required.** | Fp/Fp2/maps/scalar modules | Facades and baselines. | Compare `--deps`, cold/warm RSS, and runtime conformance before/after. |
| 7 | Compatibility spike for CompElliptic `CoordinateSystem`/SW bridge. | Potentially high deletion of local lawful boilerplate or a clear upstream plan. | High representation/API churn; provenance discrepancy; may increase Mathlib closure. **Benchmark required; selective port only.** | `LawfulAffine`, `AffineGroup`, G1/G2 affine adapters | Resolve desired infinity convention and provenance handling. | Isolated adapter compiles on Lean 4.31, maps existing add theorem, and beats local LOC/RSS threshold. |
| 8 | Adopt Hex-style conformance fixture/oracle metadata and fresh proof probes. | High long-term confidence in optimization and resource changes. | Low–medium CI engineering; avoid broad default builds. | `Checks`, scripts/CI in a later authorized task | Define representative operations and resource budget. | Regenerate fixtures byte-for-byte; three cases/operation; proof probes record command/hash/RSS. |
| 9 | Evaluate CompPoly-style optimized base-field carrier adapted to 384/512-bit representation. | Potential runtime/code-size gain later. | Very high; existing 8×32 code is unusable for `p` and does not model EVM source. **Benchmark required; selective redesign.** | Fp runtime/source implementation | Stable `toField` contract and completed naive proof. | Prove new `mul_spec`, equivalence to current source result, then compare runtime/gas/proof RSS independently. |
| 10 | Port/adapt CompElliptic Pippenger behind naive MSM spec. | Potential substantial runtime/gas improvement after correctness baseline. | High source and invariant complexity. **Deferred and benchmark required.** | G1MSM/G2MSM | Naive challenges complete; stable mathematical MSM theorem. | `optimizedMsm_eq_naiveMsm`, official vectors, gas and RSS benchmarks. |

Suggested measurement command for a narrow build, run only when no other Lean worker is active:

```sh
/usr/bin/time -v lake -Kjobs=1 build +Challenge.Bls12381.ProofSupport.Fp2SourceLawful
```

Capture the `Maximum resident set size`, elapsed time, exit status, commit, cache state, and `.olean` size. For a cold measurement, remove only the explicitly targeted artifacts in an isolated worktree or use a clean build directory; never delete the shared workspace build cache while other agents are active.

## Immediate adoption, selective ports, and rejected shortcuts

### Adopt immediately as project rules

- Hex's computational/runtime versus Mathlib bridge separation.
- Hex's conformance categories and independent-oracle provenance.
- Hex's separation of compiled runtime benchmarks from fresh proof-elaboration probes.
- CompPoly's per-round invariant culminating in one `*_spec` theorem.
- CompPoly's explicit executable-to-mathematical equivalence boundary.
- CompElliptic's focused public trust census.
- CompElliptic's optimization seam: fast implementation proves equality to one stable mathematical result.

These are process/API changes and do not require copying external source.

### Selectively port after a spike

- CompElliptic `CoordinateSystem` and compatible short-Weierstrass lemmas.
- CompElliptic generic Pippenger correctness, after naive MSM completion.
- CompElliptic curve-order lemmas where their prime/full-order premises match a specific BLS subgroup obligation.
- CompPoly's Montgomery round-proof organization generalized to the local wider carrier.
- Lean 4.33 module/public exposure conventions that are supported and beneficial on Lean 4.31 or after a separately planned toolchain upgrade.

Copied code must retain attribution and license notices. For CompElliptic, record the pinned commit and headers and resolve the absent referenced license files before distribution.

### Do not treat as reusable implementation code for current proofs

- CompPoly `BLS12_381.Fast.ScalarField` as the BLS base field.
- CompPoly's `2 * modulus < 2^256` Montgomery implementation for the 381-bit modulus.
- CompElliptic's Pasta/Vesta projective formula as a BLS formula.
- CompElliptic prime-order cardinality lemmas as a drop-in BLS cofactor proof.
- `@[extern]`, native code generation, `native_decide`, or `implemented_by` as evidence that EVM bytecode implements the specification.
- Pippenger in the first proof merely because it is asymptotically faster.
- A single giant `ProofSupport.lean` or certificate file as a way to reduce file count.

## Risks and non-goals

- This study does not prove that any external source compiles on Lean 4.31. Version compatibility is a measured migration task.
- It does not redesign pairing. Pairing was deliberately deferred; Fp6/Fp12 boundaries should remain usable without making pairing completion a prerequisite.
- It does not replace the current explicit-infinity point representation.
- It does not authorize a toolchain upgrade, new package dependency, vendoring, workflow edit, or source change.
- It does not optimize gas or runtime. It creates interfaces through which later optimizations can be substituted and proved.
- It does not recommend deleting resource firebreaks based on line count. The `fpSub` memory incident is stronger evidence than aesthetic module preferences.
- It does not treat `.olean` size as peak memory. Large artifacts flag heavy declarations; only controlled builds measure RSS.
- It does not place generic mathematics under an individual `Reference/Proofs` directory. Reusable EVM machinery belongs in `Challenge/EvmProof`; reusable BLS mathematics belongs in `Challenge/Bls12381/ProofSupport`.

## Implementation-agent checklist

Before changing a boundary:

- [ ] Identify whether it is public API, private proof stage, generated data, or closed checker.
- [ ] Record current direct/transitive imports, `.olean` size, cold/warm wall time, and peak RSS.
- [ ] State the one deep theorem downstream code should consume.
- [ ] Confirm large bodies remain opaque and no broad tactic unfolds them.
- [ ] Preserve current theorem names or add compatibility aliases.
- [ ] Build only the narrow target with one job and no competing Lean workers.
- [ ] Stop if a process approaches 6 GiB and split at a semantic intermediate result.
- [ ] Run public API/trust checks and official conformance vectors.
- [ ] Add typical, edge, and adversarial cases for a new operation.
- [ ] Record external commit, file, theorem, Lean version, and license header for any port.
- [ ] Keep naive and optimized implementations behind the same mathematical specification.
- [ ] Commit one coherent, measured change at a time.

The practical objective is not the fewest `.lean` files. It is the fewest concepts a proof author must load into their head, backed by enough opaque compilation units that Lean never has to load the entire proof into memory at once.
