# P4-Q2-PZ37AMN — finite periodic Wilson time-translation / strict OS mass-gap obstruction

2026-11-16 JST. Exact-source independently certified; canonical theorem PR merged; postmerge independent push receipt is a **separate** certification gate. All statements are about the actual periodic **deterministic configuration translation**, not the physically distinct Wilson Haar-averaging one-slab transfer operator.

## Canonical source and fixed conditions

- Repository `itakura-hidetoshi/4d-mass-gap`, Formal authoritative `formal/real-hilbert-uniform-coercive-strong-limit`.
- Toolchain Lean `v4.30.0-rc2`, fixed mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`.
- Original Wilson SU2 Haar Gibbs model, lattice geometry, Gauss-law physical subspace, coefficient beta0 and upstream proof declarations unchanged; append-only / tighten-only / same-root.
- Single new 273-line (source dependent on final HEAD) file:
  `MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2RealizablePeriodicTimeGapObstructionV5_PZ37AMN.lean`.
- Five new verified theorem declarations, five explicit `#print axioms` commands, and no `sorry`/new axioms.

## Physical mathematical issue

Existing `PhysicalYangMillsGaugeInvariantOSRealizablePeriodicWraparound.lean` **already proved** that the finite periodic Wilson time-translation carrier returns in the OS seminorm after one full period `L=PeriodicHypercubicEvenSideLength(H)=2(H+1)`. It is a finite-order deterministic configuration shift on a periodic lattice. The important distinction is that the actual physically relevant one-slab Wilson transfer kernel is a Haar **integral averaging** operator, not this shift.

Suppose one adds a certificate of strict centered OS-norm decay for the same deterministic shift:

```text
   ||R_H^k(vacuumCentered F)||_OS <= q_H^k * ||vacuumCentered F||_OS
   q_H = exp(-physicalYangMillsExact3320Mass * latticeSpacing_H)
   0 < q_H < 1.
```

At `k=L`, exact periodic recurrence gives `||v|| <= q_H^L ||v||`. Because `q_H^L<1`, this forces `||v||=0` for **every** vacuum-centered carrier. The previously independently proved dense isometry `centeredPhysicalStateLinearMap_denseRange` then forces **every** vector in the complete vacuum-orthogonal OS Hilbert carrier to equal zero.

Consequently any actually established nonzero OS physical excitation at that cutoff is incompatible with such a strict gap certificate. This is a mathematically certified **obstruction**, not a proof that genuine Wilson one-slab gap is impossible.

## Five new Lean declarations

1. `MGAP4D.MathlibAnalytic.p4Q2PZ37AMN_exact3320OneStepNormFactor_lt_one`: strict `exp(-m a_n)<1`, using already proved `m>0`, `a_n>0`.
2. `MGAP4D.MathlibAnalytic.PhysicalYangMillsEvenPeriodicWilsonOSRealizableOneStepExact3320GapCertificate.p4Q2PZ37AMN_everyVacuumCenteredCarrier_norm_eq_zero`: exact periodic recurrence plus iterated strictly contractive factor yields all centered OS carrier norms zero (conditional on certificate `G`).
3. `MGAP4D.MathlibAnalytic.PhysicalYangMillsEvenPeriodicWilsonOSRealizableOneStepExact3320GapCertificate.p4Q2PZ37AMN_everyVacuumOrthogonalPhysicalState_eq_zero`: use pre-certified dense centered physical-state map; no new surjectivity/density premise.
4. `MGAP4D.MathlibAnalytic.PhysicalYangMillsEvenPeriodicWilsonOSRealizableOneStepExact3320GapCertificate.p4Q2PZ37AMN_noExact3320Certificate_of_nonzeroPhysicalExcitation`: if a specified finite physical vacuum-orthogonal vector is nonzero, refute existence of the strict gap certificate for the *deterministic periodic shift* at that scale.
5. `MGAP4D.MathlibAnalytic.PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback.p4Q2PZ37AMN_su2RawActualAnalysisWitness_excludes_realizableExact3320Gap`: specialize the no-go to the genuine SU2 normalized-trace Wilson raw-positive-half analysis witness via the existing theorem `normalizedTracePolynomial_exists_nonzero_vacuumOrthogonalPhysicalState_of_rawActualAnalysis_range`.

**All premise distinctions are essential.** The fifth theorem requires explicit `1 < halfExtent(n)`, positive finite `beta(n)`, `c≠0`, vacuum orthogonality, and actual Wilson normalized-trace open-half readout in the range of the coherent `positiveHalfL2LinearMap`, along with the source's vacuum-unit compatibility and realizable OS structures. These are **not** asserted to hold unconditionally for the original Wilson model.

## Source, edits, exact-source CI and independent evidence

- [Theorem PR #6809](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6809) MERGED into canonical Formal, two-parent theorem merge `b4201a67949c1ce0ca9aa13ea6da62438bbc69e2`. Parents previous Formal `20989c9f062582821aab672d2d384291fc1eafea` and repaired exact-source `cc6e7098eaa70842923da2d917aad68a88af7dae`.
- The first candidate `3f3f2a1c52394eba6b16f68ea9e41a0f948947c8` was **not** certified and its initial workflow #43860826808 was **cancelled** following a same-PR edit. Do not represent it as failed/passed exact-source certification. The preventive same-PR edit made the centered dense-range proof's `Set/Topology/Function` namespaces explicit and used `dsimp [L,PeriodicHypercubicEvenSideLength]; omega` for the positive periodic length, retaining all theorem statements and hypotheses. New source `cc6e7098eaa70842923da2d917aad68a88af7dae` is the only independently certified source.
- [Exact-source PR CI #43861099079](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43861099079), `event=pull_request`, `head_sha=cc6e7098eaa70842923da2d917aad68a88af7dae`, **workflow completed/SUCCESS**. Changed-Lean job `133278015402`, required `Run changed Lean fast check` step **completed/SUCCESS**. Actual pinned Lean source log `lean-fast.log`: **8,900/8,900** compiled; **5/5** explicit `#print axioms` each listed `propext`, `Classical.choice`, `Quot.sound` and no `sorryAx`; AMN direct `warning/error=0/0`. Unrelated pre-existing imported warnings are not attributed to AMN.
- Independent exact-source completion receipt job `133281695805` **completed/SUCCESS**, actual emitted:
```text
[mcp-receipt] event=pull_request exact_sha=cc6e7098eaa70842923da2d917aad68a88af7dae source_result=success run=43861099079 attempt=1
```
- Source/test-merge `27275f413b9dd664bdfca11a39d195bcee44fcce`/actual canonical Formal theorem merge share precisely the same Git tree `668866f058cbfcb1470568f372200a460c10f361`.
- Canonical independent `event=push` [CI #43862334860](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43862334860) started against `b4201a67949c1ce0ca9aa13ea6da62438bbc69e2`. At initial record creation it was **in_progress**; later success/failure requires a distinct real observation of workflow/job/required Lean step/axioms/independent completion receipt. Preserve this historical observation if a later outcome is appended.

## Physical implications and next proof obligation

AMJ/AMK/AML proved finite static genuine interacting SU2 Wilson Gibbs plaquette covariance decay/Schur L2/Gram PSD. AMM proved exact finite Wilson/OS **discrepancy** identity and sharp HS norm bound with no zero-defect assumption. AMN rejects an inappropriate deterministic periodic shift as a stand-in for the strictly decaying physical transfer on nonzero excitations, **conditional** on the explicitly certified nontrivial witness.

Next physical step: construct the **genuine** positive Haar-averaging one-slab transfer from the verified Markov/Fubini finite Wilson kernel and prove a *type-compatible* boundary/OS transfer intertwining, with correct physical lattice-spacing time calibration, rather than importing a strict gap for finite-order configuration shifts. The original Yang–Mills spectral-uniformity and 4D continuum mass gap remain **unproved**. No theorem asserts that a genuine Wilson one-slab transfer must have zero mass gap; AMN does not imply this.

## Independent canonical theorem push — later observation, separately certified

The previous `in_progress` historical observation for run #43862334860 is **retained above**. GitHub MCP subsequently verified the canonical two-parent Formal theorem merge `b4201a67949c1ce0ca9aa13ea6da62438bbc69e2` with [event=push run #43862334860](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43862334860) **workflow completed/SUCCESS**. Changed Lean job `133282057314` and its required `Run changed Lean fast check` step both **completed/SUCCESS**.

Actual integrated exact-HEAD Lean log artifact from GitHub Actions `lean-fast-check-log` (artifact ID `14224781914`, verified against canonical push commit) confirms pinned dependency build **8,900/8,900**, all five AMN `#print axioms` outputs only `propext`, `Classical.choice`, `Quot.sound`, no `sorryAx`, and AMN direct warning/error **0/0**.

The distinct independent exact-HEAD receipt job `133286619233` completed/SUCCESS and printed:

```text
[mcp-receipt] event=push exact_sha=b4201a67949c1ce0ca9aa13ea6da62438bbc69e2 source_result=success run=43862334860 attempt=1
```

The original exact source `cc6e7098eaa70842923da2d917aad68a88af7dae`, synthetic test merge `27275f413b9dd664bdfca11a39d195bcee44fcce`, and certified actual canonical theorem two-parent merge share precisely Git tree `668866f058cbfcb1470568f372200a460c10f361`.

This independent integration result **does not** strengthen any conditional premise of the SU2 range-witness theorem, nor does it transform this *finite deterministic periodic translation* no-go into a no-go for the true Haar one-slab transfer or the four-dimensional continuum Yang–Mills mass gap.
