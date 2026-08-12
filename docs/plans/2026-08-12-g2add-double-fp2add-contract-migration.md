# G2ADD Doubling `fp2Add` Contract Migration Implementation Plan

> **For Codex:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task.

**Goal:** Remove `fp2AddFinalState` from the G2ADD finite/doubling caller layer while preserving exact source execution and measuring whether the abstraction changes peak RSS or makes production files safely removable.

**Architecture:** Keep the exact `fp2Add` execution graph behind the existing opaque, computable `fp2AddContractState`. Add only the two output-placement corollaries needed by doubling (`before/before` and `in-place-left/before`), then make the three doubling states and literal-call bridge use the contract state. Arithmetic and frame proofs consume selected projections rather than reopening the exact final state.

**Tech Stack:** Lean 4, Mathlib, YulSemantics/EvmSemantics, Lake, `/usr/bin/time -v`.

---

### Task 1: Specify the missing placement API with a failing check

**Files:**
- Modify: `Checks/Bls12381G2AddSourceFp2AddRefinement.lean`
- Modify: `Challenge/Bls12381G2Add/Reference/Proofs/SourceFp2AddPreservation.lean`

**Steps:**
1. Add checks for `fp2AddContractState_output_inputs_before` and `fp2AddContractState_output_inplace_left_before`.
2. Run `lake env lean Checks/Bls12381G2AddSourceFp2AddRefinement.lean` and confirm both names are initially unknown.
3. Derive both theorems from `fp2AddContractState_output` and the existing scheduled-input placement lemmas.
4. Re-run the check and keep the exact-state graph absent from the new theorem statements.

### Task 2: Move executable doubling states to the opaque witness

**Files:**
- Modify: `Challenge/Bls12381G2Add/Reference/Proofs/SourceMainFiniteDefs.lean`
- Modify: `Challenge/Bls12381G2Add/Reference/Proofs/SourceMainFp2Calls.lean`
- Test: an existing G2ADD check that imports the literal-call boundary

**Steps:**
1. Add a failing example requiring `step_fp2AddLiteral` to return `fp2AddContractState`.
2. Change `mainDoubleState1`, `mainDoubleState2`, and `mainDoubleState3` to use `fp2AddContractState`.
3. Change `step_fp2AddLiteral` to conclude the same state and prove it through `eval_fp2AddContractState`.
4. Re-run the focused check and `SourceMainFiniteDoubleExec.lean`.

### Task 3: Migrate arithmetic and frame consumers

**Files:**
- Modify: `Challenge/Bls12381G2Add/Reference/Proofs/SourceMainDoubleNumerator.lean`
- Modify: `Challenge/Bls12381G2Add/Reference/Proofs/SourceMainDoubleDenominator.lean`
- Modify: `Challenge/Bls12381G2Add/Reference/Proofs/SourceMainDoubleLambda.lean`
- Modify: `Challenge/Bls12381G2Add/Reference/Proofs/SourceMainFiniteLowMemory.lean`

**Steps:**
1. Replace exact-state output rewrites with the appropriate placement corollary.
2. Replace exact-state preservation proofs with `fp2AddContractState_fp2At_before_out`.
3. Confirm `rg 'fp2AddFinalState'` finds no finite/doubling caller above the contract backend.
4. Compile each modified production file independently.

### Task 4: Measure and consolidate only if justified

**Files:**
- Update: `docs/plans/precompile-proof-roadmap.md` or the existing proof-memory findings document
- Possibly consolidate: only modules proven shallow and non-protective by import/use and RSS evidence

**Steps:**
1. Re-measure Numerator, Denominator, DoubleExec, and FiniteLowMemory with `/usr/bin/time -v`.
2. Compare against the recorded baselines: 2,697,840; 2,701,336; 2,679,196; and 2,698,680 KiB respectively.
3. Scan production imports and declarations for newly dead modules; do not merge exact execution stages merely to reduce count.
4. Run the G2ADD check target and proof-policy/axiom gates.
5. Document the measured outcome, including a flat result if import closure remains the RSS floor.

## Result

The migration removed `fp2AddFinalState` from every G2ADD `SourceMain*` caller
while preserving exact sequential Yul execution through the opaque computable
state. RSS remained at the roughly 2.68--2.71 GiB imported-environment floor.
The measured private square/numerator/denominator chain was then consolidated
into `SourceMainDoubleArithmetic`, reducing the G2ADD production tree from 225
to 223 Lean files without merging the deep `fp2Add` implementation stages.
