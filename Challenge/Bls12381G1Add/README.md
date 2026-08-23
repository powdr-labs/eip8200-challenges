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
return exactly the encoded sum. The source dialect permits successful Osaka
MODEXP calls to `0x05` and no other external calls or creates, so an
implementation cannot delegate its result to native G1ADD at `0x0b`.

## Reference Yul and generated artifact

[`Reference/reference.yul`](Reference/reference.yul) uses a two-limb
`128 + 256` representation for 381-bit field values. Wide products are reduced
with MODEXP exponent one; inversion uses exponent `p - 2`. Its fixed Osaka
MODEXP stipends are 500 and 36,576 gas. The source handles infinity, opposite
points, vertical tangents, doubling, and unequal-point addition explicitly.

The repository pins the current upstream `yul-compiler` main revision. This
artifact intentionally uses its automatic backend selector rather than the
legacy/classic-only path:

```sh
lake exe yulc --backend=auto \
  Challenge/Bls12381G1Add/Reference/reference.yul
```

The resulting 1,723-byte lowercase hex is stored in
[`Reference/reference.hex`](Reference/reference.hex). CI regenerates and
compares it for Foundry. This equality is a reproducibility check, not a
semantic theorem.

The reference assumes native Osaka MODEXP remains available. Its exact call
stipends are not suitable for recursively replacing MODEXP with ordinary EVM
code at the same address.

## Source proof

The direct theorem is:

```lean
referenceParsedBlock_correct :
  Challenge.Bls12381G1Add.Yul.Correct referenceParsedBlock
```

The proof proceeds entirely in Yul big-step semantics:

- the parser and semantics-preserving normalizer are connected to a frozen,
  readable normalized AST by three finite `native_decide` checks;
- the MODEXP-only executable sub-dialect is proved sound for the public
  relational dialect;
- codec and two-limb arithmetic lemmas refine memory and word schedules to
  lawful `ZMod p` operations;
- source execution covers every validation and affine-addition branch; and
- normalization transports the universal theorem back to the parsed source.

[`Checks/Bls12381G1Add.lean`](../../Checks/Bls12381G1Add.lean) pins the axiom
footprints. The normalized universal theorem uses only `propext`,
`Classical.choice`, and `Quot.sound`; the parsed-source theorem additionally
records exactly the three finite parser/AST checks. There is no lowering,
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
