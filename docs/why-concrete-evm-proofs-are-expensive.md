# Why Concrete EVM Proofs Can Be Slow and Memory-Hungry

Algorithms such as SHA-256 are conceptually straightforward, but proving a
concrete EVM implementation correct is a much larger task than describing the
algorithm. The proof must connect several semantic layers while retaining
enough execution detail for the Lean kernel to check every step.

This note explains why apparently simple proof obligations can take a long
time or exhaust memory, and records the proof-engineering techniques that make
them manageable.

## The algorithm is only one layer

For SHA-256, “run 64 rounds” is a compact algorithmic description. A complete
EVM correctness proof may additionally need to show that:

- every concrete opcode executes correctly;
- the stack, memory, program counter, return data, and gas evolve correctly;
- 32-bit SHA operations embedded in 256-bit EVM words have the intended
  semantics;
- padding and block boundaries are correct for every permitted input length;
- all 64 rounds preserve the compression invariant;
- the final digest is stored and returned in the correct byte order;
- the concrete bytecode is exactly the program whose source-level behavior was
  proved;
- exceptional behavior and insufficient-gas paths are handled correctly.

The same issue appears in BLS12-381 proofs. A short statement such as “add two
curve points” can expand into field decoding, canonicality checks, curve
membership, exceptional affine branches, inversion, multi-limb arithmetic,
memory operations, external calls, encoding, and exact gas accounting.

The difficulty is therefore not necessarily the underlying mathematics. It is
the size of the refinement chain:

```text
concrete bytecode
    -> EVM execution
    -> compiled Yul or another source model
    -> word and limb arithmetic
    -> cryptographic mathematical specification
```

Every arrow requires checked refinement evidence.

## Why Lean can consume so much memory

### 1. Definitional reduction can expose an entire program

Lean uses definitional equality while elaborating theorem applications and
checking terms. A small-looking `rfl`, `simp`, rewrite, or constructor
application may cause Lean to unfold a large concrete program, nested state
transition, or arithmetic schedule.

For example, proving that one component of an Fp2 result is canonical can
accidentally unfold:

1. the complete Fp2 operation;
2. several Fp multiplications;
3. Montgomery or Barrett reduction;
4. wide-word carry calculations;
5. all intermediate result projections.

The theorem may be simple, while the expression Lean normalizes to apply it is
enormous.

This often appears as excessive time or memory in weak-head normalization
(`whnf`) or unification rather than in the mathematical tactic itself.

#### Case study: the G1ADD `fpSub` memory spike

The G1ADD source proof produced a particularly clear example. Its field
subtraction helper operates on a 381-bit value stored as two 256-bit words.
At the source level those words are Yul `BitVec 256` values. The shared BLS
proof layer represents the same words with `UInt256` fields inside
`Fp.Limbs`. The helper performs three stages:

1. subtract the low words and propagate the borrow into the high word;
2. test whether the wrapped high word indicates an underflow;
3. conditionally add the BLS modulus back, including the low-word carry.

The source evaluator for this helper was not expensive. After its control
flow was named explicitly, the exact evaluation theorem compiled in about
4.2 seconds. The first attempted refinement theorem was very different: it
asked Lean to prove the complete source result equal to the shared
`Fp.subSource` result in one step. That one declaration reached approximately
19.8 GB resident memory after 50 seconds without producing an error or proof
state, and was terminated.

The precise boundary was the proposition now named `conv_fpSubValue`. It
relates the following source and shared definitions:

| Frozen source representation | Shared proof representation |
| --- | --- |
| `fpSubRawValue` | `Fp.subRaw` |
| `fpSubNeedsRepairValue` | the `UInt256.gt` repair predicate |
| `fpSubRepairValue` | `Fp.subRepair` |
| `fpSubValue` | `Fp.subSource` |

The proposition itself is not intrinsically too large: the current staged
proof establishes the same equality. The trigger was the attempted proof
strategy, which exposed both complete implementations before their
intermediate values and branch conditions had been related. The text of that
failed attempt was not committed, so it is not possible to attribute the
spike to a surviving tactic line more precisely than this elaboration
boundary.

The spike was not caused by difficult subtraction mathematics. The combined
theorem made elaboration and definitional equality normalize all of the
following at once:

- the nested `if` selecting the repair branch;
- the source low-word subtraction and borrow test;
- the high-word underflow predicate;
- the conditional modulus addition and its carry;
- conversions from every `BitVec 256` operation to `UInt256`;
- the shared `Fp.subRaw`, `Fp.subRepair`, and final `Fp.subSource`
  definitions;
- two copies of large 381-bit modulus constants embedded in different
  representations.

Dependent branch terms made this worse. Before the branch condition was
given a small named interface, the interpreter result contained the branch
inside a dependent `do` expression. Unification therefore traversed and
normalized both the source execution term and the target limb schedule while
trying to discover that their intermediate values matched. A short-looking
conversion proof consequently materialized a large cross-product of source
syntax, interpreter state, word conversions, and target arithmetic.

The successful architecture splits the helper into explicit values:

```text
fpSubRawValue
    -> fpSubNeedsRepairValue
    -> fpSubRepairValue
    -> fpSubValue
```

The execution theorem is compiled separately from the representation
refinement. Conversion is then proved one stage at a time in small modules:

- `SourceSubRaw.lean` converts the raw high/low subtraction to `Fp.subRaw`
  and separately converts the underflow test;
- `SourceSubRepair.lean` converts only the modulus-repair result to
  `Fp.subRepair`;
- `SourceSub.lean` splits on the already named source test, translates that
  test to the target predicate, and composes the imported stage theorems.

In the final module, `fpSubValue` and `Fp.subSource` are unfolded only after
the branch has been selected. At that point exact `rw` steps use the raw,
predicate, and repair theorems. Lean no longer has to discover all of those
relationships through definitional equality.

This arrangement matters even though the final proposition is logically the
same. Once a stage has been compiled to an `.olean`, downstream elaboration
uses its theorem as an opaque boundary instead of reconstructing the source
interpreter and multi-limb arithmetic underneath it. Broad simplification is
also avoided: the proof rewrites the exact branch condition and the exact
conversion lemmas rather than asking `simp` to search through both programs.

The practical lesson is that a memory spike should be attributed to the
smallest *elaboration boundary*, not automatically to the algorithm. Here,
source execution was cheap and field subtraction was already proved. The
expensive object was the attempted all-at-once equality between two large,
reducible representations of that computation. Naming intermediates,
compiling them independently, and composing their theorems changes kernel
work from one enormous normalization problem into several bounded checks.

Focused re-elaboration on the same development machine, with dependencies
already compiled, gave the following comparison:

- the historical all-at-once attempt exceeded approximately 19.8 GB and did
  not finish in 50 seconds;
- the staged `SourceSub.lean` module completed in approximately 1.8 seconds
  with a peak resident set near 2.7 GB;
- the similarly staged full-multiplication refinement completed in
  approximately 1.8 seconds with a peak resident set near 2.7 GB.

These figures are machine- and cache-dependent, but the order-of-magnitude
difference identifies the important architectural change. The multiplication
proof follows the same pattern: `SourceMulDefs.lean` names the source graph,
`SourceMulWord.lean` proves the word and accumulator bridges, and
`SourceMul.lean` composes them into the three-word result.

There are therefore two distinct memory risks to control:

1. A single declaration can expand both sides of a representation boundary.
   Prevent this with named intermediate values, small bridge theorems,
   explicit projection lemmas, branch splitting, and targeted rewriting.
2. Several individually acceptable Lean processes can peak concurrently.
   Prevent this by compiling heavy stages serially before building the proof
   umbrella and by enforcing a measured per-module memory budget in CI.

To keep the first failure mode from returning, composite refinement theorems
should compose already compiled bridge lemmas rather than broadly simplifying
or unfolding both implementations. Large constant conversions, such as the
high and low words of the BLS modulus, should also be proved once behind an
opaque interface. Source value definitions should be separated from
interpreter execution proofs, so arithmetic bridge modules do not import more
execution machinery than they need.

### 2. Symbolic EVM states are large

An EVM state includes much more than a stack:

- memory;
- accounts and storage;
- call frames;
- gas;
- execution environment;
- calldata and return data;
- substate and access information;
- program counter and halt state.

A long trace constructs many states that differ in only a few fields. If these
states are repeatedly unfolded or copied into proof terms, the accumulated
representation becomes very large.

### 3. Concrete programs and naive certificates can be quadratic

A program containing 1,000 instructions is already a substantial Lean value.
A checker that records the complete remaining program suffix at every program
point stores approximately:

```text
1000 + 999 + 998 + ... + 1
```

instructions. This is quadratic in the original program length, even though
the underlying certificate may contain only one small fact per instruction.

Similar blow-ups occur when certificates store complete states, expressions,
or syntax trees instead of compact keys and local facts.

### 4. Branches multiply proof obligations

Cryptographic code frequently contains branches for:

- input length;
- padding;
- zero and infinity values;
- canonical field encodings;
- equal, opposite, and unequal curve points;
- memory growth;
- call success or failure;
- exceptional EVM execution.

The concrete execution may take only one branch for one test vector, but a
universal correctness theorem must justify every applicable branch.

### 5. Large numerals and bitvectors create large normalization terms

SHA-256 repeatedly uses masks, shifts, rotations, modular addition, and byte
order conversions. BLS12-381 uses 381-bit field constants and multi-word
products. Normalizing these expressions can generate large kernel terms even
when the final proposition is elementary.

A direct proof involving a concrete 381-bit prime or a wide nonlinear bound
can be much more expensive than proving a generic lemma first and applying it
through a small opaque interface.

### 6. Exact gas retains details that functional proofs can hide

A functional proof can often abstract away intermediate execution details.
An exact gas theorem cannot. It must retain information about:

- each opcode cost;
- memory expansion;
- cold and warm access charges;
- call forwarding and EIP-150 caps;
- precompile gas;
- branch-specific execution lengths.

Consequently, exact gas proofs tend to keep larger traces and stronger state
invariants alive.

### 7. Imports and parallel builds increase the peak

Large proof modules bring substantial elaboration and compiled-environment
state into memory. Broad imports such as an entire tactic umbrella also enlarge
the dependency graph.

Parallel elaboration can make the situation worse: several individually
reasonable Lean processes may peak simultaneously and exhaust system memory.
For heavy verification gates, single-job builds are usually safer.

## Typical warning signs

The following symptoms usually indicate a proof-engineering problem rather
than genuinely difficult mathematics:

- a theorem fails at `whnf` or maximum recursion depth;
- a projection theorem uses gigabytes before producing an error;
- adding an explicit type annotation dramatically changes memory use;
- a generic theorem builds quickly but its concrete large-numeral
  specialization does not;
- `simp` continues expanding definitions far below the intended abstraction
  boundary;
- a finite certificate checker becomes slower than the program it checks;
- recompiling a dependency into a separate `.olean` makes the consumer proof
  suddenly cheap.

## Techniques that keep the proofs manageable

### Establish opaque, proved boundaries

Each major layer should expose small theorems that later modules can use
without unfolding the implementation. Examples include:

- a wide multiplication value theorem;
- a canonicality theorem for one field operation;
- an execution-stage postcondition;
- a memory-region framing theorem;
- a source-operation refinement theorem.

The implementation is checked once. Consumers reason through the theorem
rather than through the definition.

### Separate executable code from proof-only semantics

Executable modules should depend only on the operations required at runtime.
Independent mathematical models, elliptic-curve group instances, certificates,
and large tactic imports should live in proof-only modules.

This reduces both generated-code risk and elaboration cost for ordinary
consumers.

### Prove generic lemmas before instantiating large constants

It is often much cheaper to prove a generic statement about bounded words or
field operations and later instantiate it through an opaque theorem than to
ask arithmetic tactics to normalize a 381-bit concrete expression directly.

Useful generic lemmas include:

- word splitting and joining;
- carry and borrow bounds;
- reconstruction from limbs;
- modular congruence transport;
- invariant preservation under recursive folds;
- generic binary scalar multiplication into an independent group action.

### Use explicit rewrite and projection lemmas

Do not rely on unification to discover that a projection of a large reducible
definition equals a smaller helper call. Export shallow equations such as:

```text
result.c0 = namedComponent ...
```

and rewrite with them explicitly. This prevents Lean from unfolding the entire
call graph merely to expose a structure field.

### Avoid broad simplification

Prefer `simp only` with a controlled list of lemmas, targeted rewrites, and
small algebraic steps. Broad `simp`, `unfold`, or `dsimp` can cross carefully
chosen abstraction boundaries and expand the complete implementation.

### Split long traces and finite checks

Large executions and certificates should be divided into independently
compiled stages or chunks. Each chunk exposes a compact postcondition that the
next chunk consumes.

For finite certificates:

- store compact indices or lengths rather than full suffixes;
- check local entries with a total kernel-visible checker;
- combine independently compiled chunks through a generic soundness theorem;
- keep parser or generator output untrusted, and prove the checked data has the
  required meaning.

### Use one program with multiple interpreters for control-flow audits

A returned trace cannot observe work whose result is discarded. When operation
order or call count matters, define one authoritative parametric program and
interpret it in two ways:

- a direct interpreter used by executable code;
- a tracing interpreter used by proofs and tests.

This makes the control-flow audit meaningful without adding trace allocation
to the runtime path.

### Compile intermediate modules before consuming them

Moving a heavy theorem into its own module and compiling it to an `.olean`
creates an effective opacity boundary. A downstream proof can use the theorem
without re-elaborating or normalizing its construction.

This is particularly helpful for:

- field arithmetic schedules;
- large algebraic identities;
- compiler simulation phases;
- certificate chunks;
- concrete constant proofs.

### Keep resource settings local and bounded

When a finite kernel computation genuinely needs a larger recursion depth or
heartbeat budget, scope the setting to the specific declaration. Avoid global
or unlimited resource settings: they obscure regressions and allow accidental
expansion to consume the machine.

### Build heavy gates single-threaded

Use single-job builds for the largest proof umbrellas. This does not reduce the
memory required by one theorem, but it prevents multiple large elaborations
from reaching their peaks at the same time.

## Practical interpretation of an OOM

An out-of-memory failure does not usually mean that the target theorem is
unprovable. It more often means that the current formulation asks Lean to
materialize too much at once.

The productive response is generally:

1. identify the smallest declaration that triggers the growth;
2. determine what Lean is unfolding or duplicating;
3. stop the process before it consumes the machine;
4. introduce a smaller generic lemma, opaque boundary, compact certificate, or
   staged trace;
5. rerun only the focused proof;
6. compile the successful boundary before continuing downstream.

Repeatedly raising global limits or rerunning the unchanged proof usually
delays the same failure rather than solving it.

## Summary

SHA-256, BLS field arithmetic, and affine curve addition are not necessarily
hard because their mathematical definitions are complicated. They become
expensive to verify because a complete proof connects concrete bytecode,
detailed EVM state transitions, source-level control flow, word arithmetic,
and abstract cryptographic semantics.

Good proof architecture ensures the kernel checks each large fact once and
that later proofs consume only compact, opaque interfaces. Without those
boundaries, a one-line theorem can accidentally ask Lean to normalize an
entire cryptographic implementation and its execution trace in memory.
