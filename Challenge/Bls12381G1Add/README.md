# BLS12-381 G1ADD source challenge: audit map

This is a focused EIP-2537 experiment for the `BLS12_G1ADD` interface at
address `0x0b`. EIP-2537 defines seven BLS12-381 precompiles; this challenge
covers G1 addition only so its specification and proof remain reviewable.
BLS precompiles are not part of the current EIP-8200 proposal.

The acceptance boundary is Yul source. The checked-in EVM artifact exists so
Foundry can execute the implementation, but no theorem claims that the
compiler output or bytecode is correct.

## Auditor-facing specification

[`Spec.lean`](Spec.lean) defines `spec : ByteArray → Option ByteArray`:

1. require exactly 256 input bytes;
2. decode two 128-byte EIP-2537 G1 points;
3. reject nonzero high padding, noncanonical field values, and finite points
   outside `y² = x³ + 4` over the BLS12-381 base field;
4. add the decoded points with lawful affine field arithmetic; and
5. encode the sum as 128 bytes, using the all-zero encoding for infinity.

As EIP-2537 requires for G1ADD, ordinary point decoding does not impose a
prime-subgroup check. `None` represents exceptional precompile termination.

The pinned EVM semantics implements its affine inverse through an opaque
partial `Fin` routine, which is executable but has no usable inverse theorem.
The local high-level boundary therefore transports decoded coordinates into
`ZMod p`, proves the fixed BLS modulus prime with a Lucas certificate, and
uses ordinary field division. [`LawfulAffine.lean`](../Bls12381/ProofSupport/LawfulAffine.lean)
contains the generic short-Weierstrass formulas;
[`G1Affine.lean`](../Bls12381/ProofSupport/G1Affine.lean) instantiates them for
`y² = x³ + 4`. This keeps the mathematical operation proof-visible instead of
assuming correctness of the pinned opaque inverse.

[`YulSpec.lean`](YulSpec.lean) defines the public source predicate:

```lean
Challenge.Bls12381G1Add.Yul.Correct : Block Op → Prop
```

It requires the G1ADD result for every calldata value that fits the EVM
`calldatasize` word. Malformed input must execute `invalid()`; valid input must
return exactly the encoded sum. The source dialect provides no external calls
or contract creation at all. Neither MODEXP at `0x05` nor native G1ADD at
`0x0b` is available to the implementation.

## Reference Yul and generated artifact

[`Reference/reference.yul`](Reference/reference.yul) uses a two-limb
`128 + 256` representation for 381-bit field values. It implements field
multiplication with an exact three-word schoolbook product and fixed-modulus
Barrett reduction. Inversion is a fixed `p - 2` exponentiation built from a
two-limb CIOS Montgomery multiplication. All of this is ordinary local Yul;
the source contains no call-family or create-family operation. It handles
infinity, opposite points, vertical tangents, doubling, and unequal-point
addition explicitly.

The repository pins the current upstream `yul-compiler` main revision. This
artifact intentionally uses its automatic backend selector rather than the
legacy/classic-only path:

```sh
lake exe yulc --backend=auto \
  Challenge/Bls12381G1Add/Reference/reference.yul
```

The resulting 4,687-byte lowercase hex is stored in
[`Reference/reference.hex`](Reference/reference.hex). CI regenerates and
compares it for Foundry. This equality is a reproducibility check, not a
semantic theorem.

## Source proof

The direct theorem is:

```lean
referenceParsedBlock_correct :
  Challenge.Bls12381G1Add.Yul.Correct referenceParsedBlock
```

The proof proceeds entirely in Yul big-step semantics:

- the parser and semantics-preserving normalizer are connected to a frozen,
  readable normalized AST by two finite `native_decide` checks;
- the executable and public relational semantics both use the closed EVM
  dialect, in which external calls and contract creation are unavailable;
- a recursive parsed-AST check separately certifies that the checked-in source
  contains no call-family or create-family operation;
- codec and two-limb arithmetic lemmas refine memory and word schedules to
  lawful `ZMod p` operations;
- [`SoftwareModexpMath.lean`](../YulProof/SoftwareModexpMath.lean) states the
  implementation-free natural-number MODEXP result. The repository's existing
  [general EIP-198 Yul proof adapter](../Modexp/Reference/Proofs/Yul/SoftwareModexpMath.lean)
  certifies that property at its calldata/halting ABI, while the BLS adapter
  maps its field result to the same property without importing the large
  MODEXP proof closure into this challenge;
- a reusable local-function contract additionally states normal-return source
  execution, scratch-memory framing, and the BLS `p - 2` specialization. The
  inversion proof instantiates that contract with the reference's optimized
  Montgomery implementation, and G1ADD callers consume only the contract;
- source execution covers every validation and affine-addition branch; and
- normalization transports the universal theorem back to the parsed source.

[`Checks/Bls12381G1Add.lean`](../../Checks/Bls12381G1Add.lean) pins the axiom
footprints. The normalized universal theorem uses only `propext`,
`Classical.choice`, and `Quot.sound`; the parsed-source theorem additionally
records exactly the two finite parser/AST checks. There is no lowering,
assembly, compiler-correctness, instruction-list, or bytecode theorem.

The proof-friendly source and much of its arithmetic decomposition were
carried forward from the earlier broad BLS draft PR #24, then narrowed to the
G1ADD source-only boundary and updated for the current compiler/semantics pins.

Focused verification:

```sh
lake build Challenge.Bls12381G1Add.Reference.Proofs.Yul
lake build +Checks.Bls12381G1Add
cd foundry && forge test --match-contract Bls12381G1AddTest -vv
```

## Foundry falsification tests

[`foundry/test/Bls12381G1Add.t.sol`](../../foundry/test/Bls12381G1Add.t.sol)
etches the generated artifact at `0x820b` and compares it with native `0x0b`
for infinity identities, generator doubling, and malformed encodings. These
tests make artifact or compiler regressions visible; they are not proof input.
