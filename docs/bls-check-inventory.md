# Completed BLS ADD Check Inventory

## Purpose

This inventory classifies every `Checks/Bls12381G1Add*.lean` and
`Checks/Bls12381G2Add*.lean` file by the observable regression it protects.
G1MSM and G2MSM checks are outside this inventory and remain paused.

Snapshot totals:

| Challenge | Check files | Lines |
| --- | ---: | ---: |
| G1ADD | 44 | 2,827 |
| G2ADD | 176 | 1,829 |
| **Total** | **220** | **4,656** |

The classification is deterministic. A permanent named gate is classified
first, followed by an executable `#guard`, an axiom census, a typed `example`,
and finally a file containing only `#check` name lookups. These categories
cover all 220 files; there are no unclassified files.

## Classification summary

| Category | G1ADD | G2ADD | Permanent policy |
| --- | ---: | ---: | --- |
| Public/conformance/reference gates | 2 | 4 | Keep and deepen |
| Additional executable artifact guards | 1 | 2 | Keep until absorbed by reference gates |
| Internal axiom/type guards | 40 | 41 | Retain until a final-root trust census replaces them |
| Typed certificate chunk example | 1 | 0 | Keep as a certificate/resource boundary |
| Signature-only `#check` wrappers | 0 | 129 | Remove in measured clusters |
| Unclassified | 0 | 0 | — |

## Permanent gates

### G1ADD

- `Checks/Bls12381G1Add.lean`: public specification equations, official and
  adversarial vectors, invalid lengths, off-curve rejection, schedule bridge,
  and challenge configuration trust.
- `Checks/Bls12381G1AddReference.lean`: frozen bytecode identity and size,
  final correctness availability, scorer availability, and reference gas
  results.

The main gate imports the production final-correctness boundary directly and
contains the final theorem type checks and guarded axiom census. The reference
gate remains separate because it protects artifact identity, size, scorer, and
gas observations rather than proof trust.

### G2ADD

- `Checks/Bls12381G2Add.lean`: final schedule bridge and challenge
  configuration trust, plus final theorem type checks and the guarded final
  correctness axiom census. It imports production correctness directly. It
  should eventually absorb the public spec checks.
- `Checks/Bls12381G2AddSpec.lean`: public specification equations, official
  and adversarial vectors, invalid lengths, infinity/opposite/off-curve cases,
  and specification trust. This is a transitional permanent gate until its
  content moves into `Checks/Bls12381G2Add.lean`.
- `Checks/Bls12381G2AddReference.lean`: normalized/compiler/bytecode identity,
  bytecode size, final correctness availability, scorer availability, and
  reference gas results.
- `Checks/Bls12381G2AddReferenceRuntime.lean`: executable runtime conformance
  over valid, invalid-length, infinity, opposite, off-curve, and noncanonical
  inputs.

## Additional observable artifact and certificate guards

Keep these while their assertions are not present in a permanent reference or
resource gate:

- `Checks/Bls12381G1AddCompilation.lean` contains executable closed compiler
  guards.
- `Checks/Bls12381G1AddStackCertificateChunk0.lean` checks one bounded
  certificate chunk and remains a useful resource boundary.
- `Checks/Bls12381G2AddCompilation.lean` contains executable compiler guards.
- `Checks/Bls12381G2AddLowering.lean` contains executable lowering guards.

Other compiler, lowering, byte, stack, Yul, and source check files currently
fall in the axiom/type-guard category. Do not delete them until the public
trust census is deliberately rooted at final correctness and certificate
soundness.

## Internal axiom/type guards

There are 40 G1ADD and 41 G2ADD files whose strongest permanent assertion is a
guarded `#print axioms` result. They were valuable during red/green proof
development and currently detect changes to internal theorem trust sets.

These are not first-slice deletion candidates. Before consolidating them:

1. define the allowed axiom footprint for final correctness, gas, compilation,
   byte equality, and stack-certificate soundness;
2. put that census in permanent gates importing production modules directly;
3. confirm the census reaches the relevant internal proofs transitively; and
4. retain a fine-grained guard only for a known resource or trust regression.

This category includes all non-permanent completed-ADD check files containing
`#print axioms`, except the executable artifact files classified earlier.

## G2ADD signature-only wrappers

At the inventory snapshot, 129 G2ADD checks imported one production proof module and contained
only one or more `#check` commands. They assert that internal theorem names and
types still exist but do not test behavior, trust, artifact identity,
certificate validity, or resource usage.

They divide as follows. Names in the members column omit the common
`Checks/Bls12381G2Add` prefix and `.lean` suffix.

| Cluster | Count | Members |
| --- | ---: | --- |
| Fp2 add | 3 | `SourceFp2AddInputs`, `SourceFp2AddOutput`, `SourceFp2AddPreservation` |
| Fp2 sub | 3 | `SourceFp2SubInputs`, `SourceFp2SubOutput`, `SourceFp2SubPreservation` |
| Fp2 mul | 7 | `SourceFp2MulBeforeOutLawful`, `SourceFp2MulCorrect`, `SourceFp2MulHighInputs`, `SourceFp2MulHighLawful`, `SourceFp2MulLawful`, `SourceFp2MulMemory`, `SourceFp2MulRefinement` |
| Fp2 inversion | 27 | `SourceFp2InvCorrect`, `SourceFp2InvDefs`, `SourceFp2InvExec`, `SourceFp2InvImag`, `SourceFp2InvImagReadback`, `SourceFp2InvLowFinal`, `SourceFp2InvLowFinalWord`, `SourceFp2InvLowImagCall`, `SourceFp2InvLowImagReads`, `SourceFp2InvLowNeg`, `SourceFp2InvLowPreservation`, `SourceFp2InvLowReal`, `SourceFp2InvLowScalar`, `SourceFp2InvLowSquare0`, `SourceFp2InvLowSquare1`, `SourceFp2InvMemory`, `SourceFp2InvNeg`, `SourceFp2InvNorm`, `SourceFp2InvOutput`, `SourceFp2InvPreservation`, `SourceFp2InvReadback`, `SourceFp2InvReal`, `SourceFp2InvRefinement`, `SourceFp2InvScalar`, `SourceFp2InvSquare0`, `SourceFp2InvSquare1`, `SourceFp2InvStep` |
| Scalar Fp/MODEXP | 2 | `SourceFpInvMemory`, `SourceFpMulMemory` |
| Input codec | 1 | `SourceInputCodecReject` |
| Main execution | 46 | `SourceMainBothInfinity`, `SourceMainCurve1`, `SourceMainCurve2`, `SourceMainCurveLawful`, `SourceMainDecodeExec`, `SourceMainDefs`, `SourceMainDoubleDenominator`, `SourceMainDoubleInverse`, `SourceMainDoubleLambda`, `SourceMainDoubleNumerator`, `SourceMainDoubleSquare`, `SourceMainFiniteClassify`, `SourceMainFiniteDefs`, `SourceMainFiniteDispatcher`, `SourceMainFiniteDispatcherLawful`, `SourceMainFiniteDoubleExec`, `SourceMainFiniteEqualExec`, `SourceMainFiniteExceptional`, `SourceMainFiniteExceptionalLawful`, `SourceMainFiniteInputs`, `SourceMainFiniteLowMemory`, `SourceMainFinitePostExec`, `SourceMainFinitePredicates`, `SourceMainFiniteUnequalBranch`, `SourceMainFiniteUnequalExec`, `SourceMainFirstInfinity`, `SourceMainFp2Calls`, `SourceMainIdentityLawful`, `SourceMainPointDefs`, `SourceMainPointDispatcher`, `SourceMainPointExec`, `SourceMainPointPrefix`, `SourceMainPointScope`, `SourceMainPostAffine`, `SourceMainPostOutput`, `SourceMainPostX`, `SourceMainPostY`, `SourceMainPrefix`, `SourceMainSecondInfinity`, `SourceMainUnequalDifferences`, `SourceMainUnequalInverse`, `SourceMainUnequalLambda`, `SourceMainValidationAnd`, `SourceMainValidationCall1`, `SourceMainValidationCall2`, `SourceMainValidationExec` |
| On-curve execution | 23 | `SourceOnCurveAddExec`, `SourceOnCurveConstant`, `SourceOnCurveConstantMemory`, `SourceOnCurveCorrect`, `SourceOnCurveDefs`, `SourceOnCurveEqExec`, `SourceOnCurveExec`, `SourceOnCurveHighInputs`, `SourceOnCurveHighMemory`, `SourceOnCurveHighPreservation`, `SourceOnCurveLowMemory`, `SourceOnCurveMulExec`, `SourceOnCurveMulInputs`, `SourceOnCurveMulLawful`, `SourceOnCurveMulLeft`, `SourceOnCurveMulRight`, `SourceOnCurveResult`, `SourceOnCurveRhs`, `SourceOnCurveStoresExec`, `SourceOnCurveX2`, `SourceOnCurveX3`, `SourceOnCurveY2`, `SourceOnCurveY2Preservation` |
| Point helpers | 6 | `SourcePointPredicatesDefs`, `SourcePointPredicatesExec`, `SourcePointPredicatesRefinement`, `SourcePointStoresDefs`, `SourcePointStoresExec`, `SourcePointStoresMemory` |
| Source run | 2 | `SourceRun`, `SourceRunReject` |
| Source specification | 6 | `SourceSpecFiniteDouble`, `SourceSpecFiniteExceptional`, `SourceSpecFiniteUnequal`, `SourceSpecRejectCurve`, `SourceSpecRejectValidation`, `SourceSpecValid` |
| Other source resource | 1 | `SourceScalarLowMemory` |

All production modules imported by these 129 wrappers are already in the
transitive local-source import closure of G2ADD final correctness. Removing a
wrapper does not remove or merge its production `.lean`/`.olean` firebreak.

Later architecture work consolidated the private
`SourceMainDoubleSquare`/`Numerator`/`Denominator` chain into
`SourceMainDoubleArithmetic`. The table above is retained as the historical
inventory snapshot; the current production tree has two fewer modules.

A subsequent measured certificate pass grouped the ten G1ADD and fifteen
G2ADD 100-entry decision files into two and three physical units while
preserving every public theorem. This removed another eight G1ADD and twelve
G2ADD production modules; it did not change the retained check inventory.

## Import-closure evidence

A recursive scan of local source imports found:

| Final root | Local production closure | Check files importing only modules in that closure |
| --- | ---: | ---: |
| G1ADD final correctness | 197 modules | 42 of 44 |
| G2ADD final correctness | 373 modules | 172 of 176 |

The checks outside those closures are exactly the public challenge/vector,
reference/scorer, and runtime gates described above. This explains why a final
correctness rebuild covers compilation of the production modules behind the
signature-only wrappers, while the permanent gates remain necessary for
externally observable behavior.

## First deletion cluster

Remove these ten signature-only wrappers:

- `Checks/Bls12381G2AddSourceFp2InvLowFinal.lean`
- `Checks/Bls12381G2AddSourceFp2InvLowFinalWord.lean`
- `Checks/Bls12381G2AddSourceFp2InvLowImagCall.lean`
- `Checks/Bls12381G2AddSourceFp2InvLowImagReads.lean`
- `Checks/Bls12381G2AddSourceFp2InvLowNeg.lean`
- `Checks/Bls12381G2AddSourceFp2InvLowPreservation.lean`
- `Checks/Bls12381G2AddSourceFp2InvLowReal.lean`
- `Checks/Bls12381G2AddSourceFp2InvLowScalar.lean`
- `Checks/Bls12381G2AddSourceFp2InvLowSquare0.lean`
- `Checks/Bls12381G2AddSourceFp2InvLowSquare1.lean`

These files contain 11 `#check` commands and no other assertions. No check
imports them. Their production modules form an import chain ending in
`SourceMainFiniteLowMemory.lean`, which is in the final-correctness closure.

No replacement assertion is required: the internal theorem names are not a
public compatibility contract, and the permanent behavior/trust/artifact gates
remain unchanged. Verification must rebuild G2ADD final correctness and all
four permanent G2ADD gates after removal.

### Implementation status

Removed on 2026-08-12. The cluster deleted 10 files and 51 lines, reducing the
G2ADD check count from 176 to 166. Post-deletion verification rebuilt G2ADD
final correctness and all four permanent G2ADD gates successfully. The proof
policy and BLS cache-policy self-tests also passed. No production proof module
or `.olean` firebreak was removed.

## Final-root trust consolidation

On 2026-08-12, the final theorem checks and guarded axiom census from
`Checks/Bls12381G1AddFinalCorrectness.lean` and
`Checks/Bls12381G2AddFinalCorrectness.lean` were moved into the permanent main
G1ADD and G2ADD gates. Those gates now import the production
`Reference.Proofs.FinalCorrectness` modules directly. The two forwarding check
files were then removed.

The proof-policy scanner now rejects completed-ADD check-to-check imports. Its
self-test covers rejected G1ADD and G2ADD check imports and an accepted direct
production import. This keeps the permanent gates independently meaningful and
prevents coverage from being hidden behind another check file.

Current completed-ADD check totals after both deletion slices are:

| Challenge | Current check files | Change from snapshot |
| --- | ---: | ---: |
| G1ADD | 43 | -1 |
| G2ADD | 165 | -11 |
| **Total** | **208** | **-12** |

This was the intermediate count before the final signature-only cleanup below.

## Complete signature-only cleanup

On 2026-08-12, the remaining 119 G2ADD signature-only wrappers were validated
mechanically and removed. Together they contained 886 lines and no
`#print axioms`, `#guard_msgs`, executable `#guard`, `example`, or `#eval`.
Every imported production module remained in the G2ADD final-correctness
closure. No production module or `.olean` memory barrier was removed.

The BLS cache-policy test, proof-policy scanner self-test, and completed-G2ADD
policy scan passed. The CI-shaped single-job build of the G2ADD root and all 46
remaining G2ADD checks then passed 2,534 jobs in 4.24 s at 2,732,800 KiB peak
RSS. This was a warm build with a Lean language-server worker active and is
verification, not a cold performance comparison.

Current completed-ADD check totals are:

| Challenge | Current check files | Change from snapshot |
| --- | ---: | ---: |
| G1ADD | 43 | -1 |
| G2ADD | 46 | -130 |
| **Total** | **89** | **-131** |

There are no signature-only completed-ADD wrappers left. The remaining files
protect a permanent public/reference/runtime gate, an executable artifact or
certificate assertion, or a guarded internal trust/resource boundary. Further
check consolidation must migrate one of those observable purposes first.
