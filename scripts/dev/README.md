# Re-derivation tools for the direct-bytecode proofs

These are development aids for one specific job: re-deriving a challenge's
direct-bytecode proof corpus after the pinned compiler emits a different
artifact. They are not part of CI and nothing in `Challenge/` depends on them.
Everything they print is a *starting point* that Lean still has to accept —
they generate proof text, they do not certify anything.

## Why the corpus has to be re-derived at all

The direct proofs deliberately use no compiler soundness theorem: each one
states an exact instruction sequence at an exact index of the frozen artifact
(`Stepper.Located`) and tracks the machine state instruction by instruction.
That makes them independent of the compiler — and it makes them sensitive to
*any* change in what the compiler emits.

When `yul-compiler` moved to `8b9c5bb`, `compileSource` began preferring its
SSA-CFG backend over the classic chain for these two sources (it keeps both
candidates and emits whichever scores lower on `SsaCfg.instrCost`). That is not
an index shift. Measured against the previously proven artifacts, only 2 of 88
SHA-256 anchors and 2 of 31 RIPEMD-160 anchors can be relocated at all, even
allowing jump-target literals to be wildcarded — the backend re-schedules
instructions *inside* blocks, inlines functions that used to be called, and
inverts branch polarity. There is no remapping that recovers the old proofs.

So each block gets re-derived: find where it went, re-run it, read off the new
stack shapes.

## The tools

    artifact.py <hex> [--range=lo:hi] [--json]

Disassemble a frozen artifact into `(index, pc, instruction)` triples, in the
same view the Lean instruction list uses (`push width value` / `op`). Use it to
find where a block went — distinctive constants (`0x800`, `0xffffffff`) and
`JUMPDEST` positions are the reliable anchors, since the instruction order
inside a block is not stable.

    symtrace.py <hex> <start-index> [count] [--stack=a,b,c] [--lean]

Symbolically execute a straight-line run and print the stack after every
instruction. This is the tool that actually replaces hand-derivation: the trace
modules are transcripts of exactly this, so the new `State` definitions are read
off its output. `--lean` renders each stack entry in the corpus's vocabulary
(`UInt256.ofNat`, `UInt256.shiftLeft`, …) instead of infix shorthand. Named
symbols passed with `--stack` stand for whatever the block's entry state holds.

    emit_path.py <hex> <lo> <hi>

Emit a `Stepper.Located` path for an index range, in the corpus's convention
(`wfOp (by decide) trivial rfl` for plain ops, `by decide` for pushes).
Transcribing anchors by hand is the easiest way to introduce a mismatch that
only shows up as an opaque `rfl` failure hundreds of lines away.

    emit_jumpdests.py <hex>

Emit a `validJumpDest_<pc>` certificate for every `JUMPDEST` the artifact
contains. The full set is small (25 for RIPEMD-160, 36 for SHA-256), so
certifying all of them is cheaper than predicting which ones the re-derived
proofs will reach.

    emit_pc_table.py <hex> <lo>:<hi> [...] [--end]

Emit `instructionPC` lemmas for an index range. Generate the ranges a module
anchors on, not the whole program: each lemma is an `rfl` that folds the
instruction list up to its index, so the table is quadratic in its highest
index. A complete 847-entry RIPEMD-160 table takes over ten minutes to
elaborate; the 132 entries the initialization and padding proofs need take under
two.

## Working order

Bottom-up, in import order, verifying each module with

    lake env lean Challenge/<C>/Reference/Proofs/Bytecode/<Module>.lean

and `lake build <module>` before moving to the next, since `lake env lean` reads
the previous module's `.olean` rather than rebuilding it. Two things that bit
during this re-derivation:

  - `@[simp]` lemmas remain active in importing modules even when `private`.
    Deleting an obsolete helper can break a module that never named it —
    `Execution.addSmall`/`succSmall` outlived the trampoline chain they were
    written for because the modules above fold `pc` advances with them.
  - A missing PC-table entry surfaces as a `simp` that stalls on
    `instructionPC <n>` with no obvious cause. Extend the table first.

## Getting the new gas constants

The gas modules assert a static cost per located path. Don't recompute those by
hand from an opcode table — ask Lean, which is authoritative and takes a couple
of minutes:

    -- scratch.lean
    import Challenge.Sha256.Reference.Proofs.Bytecode.PaddingTrace
    open Challenge.Sha256.Reference.Proofs.Bytecode
    #eval show IO Unit from do
      let p := Challenge.EvmProof.Meter.runLocatedBlockStaticCost
      IO.println s!"lengthCondition = {p PaddingTrace.lengthConditionPath}"
      -- … one line per path

    lake build Challenge.Sha256.Reference.Proofs.Bytecode.PaddingTrace
    lake env lean scratch.lean

`runLocatedBlockStaticCost` is state-independent, so it gives the figure the
`_cost` theorems need for every path with no memory-expansion term. For the
memory-touching paths it gives the static part and the theorem carries the
`memCost` difference separately.

Measured for the re-derived SHA-256 padding paths, for reference:
`computePaddedLength` 23 (was 26), `lengthSetup` 75, `lengthCondition` 23
(was 25), `lengthByte` 31 (was 27), `lengthStore` 12, `lengthIncrement` 6
(was 14), `lengthBack` 11 (was 12), `lengthExit` 42, whole `lengthIteration` 83.

## Inlined helpers: two different shapes

Both challenges' Yul helpers are now inlined rather than compiled to internal
jumps, but they do not all inline the same way, and the difference decides how
the summary module can be restated.

**Uniform sites — one lemma covers all of them.** SHA-256's memory accessors
splice an identical five-instruction sequence at every use
(`PUSH1 5; SHL; PUSH2 base; ADD; MLOAD|MSTORE`); only `base` and the site index
vary. `Accessors.lean` keeps its `hmatch`-disjunction shape, one proof discharges
all eleven sites, and the consuming interface survives.

**Non-uniform sites — the conclusion itself varies.** SHA-256's `rotr` is
inlined at 16 sites (`PUSH4 0xffffffff` at instructions 237, 249, 261, 285, 323,
368, 431, 469, 564, 576, 617, 782, 794, 829, 841, 853), each an eleven
instruction run, but the `DUP` depths differ per site (`DUP5`, `DUP6`, `DUP7`, …)
because the surrounding stack differs, and the rotation amount is a per-site
literal. The operand therefore comes from a different stack slot at each site,
so a single shared conclusion is impossible: `Functions.lean` needs its summary
stated over a stack split at a parameterised depth, or one lemma per site.

Check which shape you are dealing with *before* restating a summary module —
assuming uniformity and discovering otherwise wastes a full elaboration cycle
per site.
