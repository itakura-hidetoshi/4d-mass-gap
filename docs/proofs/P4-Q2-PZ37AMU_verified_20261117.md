# P4-Q2-PZ37AMU — actual infinite-dimensional SU(2) Gauss-law physical Hilbert and nonzero top-orthogonal witness

Date: 2026-11-17 JST. Authoritative Formal branch `formal/real-hilbert-uniform-coercive-strong-limit`; `main` documentation mirror separately controlled.

## Fixed original model and exact proof scope

- Pinned Lean `v4.30.0-rc2`; mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`.
- Original finite even-periodic SU(2) spatial-slice Haar Hilbert and real Gauss-law fixed submodule; original physical normalized Wilson one-slab transfer and its complete eigenvalue-one top eigenspace. Same root, same Wilson/Haar/beta0/AJA, existing theorem contracts unchanged.
- AMT #6825 first independently certified **actual** native spatial Haar Gram–Schmidt mode membership in the Gauss-law fixed carrier. The previously certified `periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace_eq_span_nonnegativeTopEigenvector` proves true finite-volume top simplicity rather than requiring it as an extra assumption. The previously certified Hilbert vacuum-orthogonal basis extension constructs vectors from a proved infinite-dimensionality premise.
- One new additive source `MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalGaussHilbertInfiniteExcitationV5_PZ37AMU.lean`, 139 lines, final certified blob SHA `1fd629c08cb1f48f02e2e3c87da991a38cff5eee`.

## Mathematical theorems (four printed-axiom declarations)

1. `p4Q2PZ37AMU_actualPhysicalGaussMode`: type-safe construction of each AMS actual spatial Wilson Gram–Schmidt mode inside `PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H 2`, using AMT's real Gauss-law membership; the definition itself is also compiled.
2. `p4Q2PZ37AMU_actualPhysicalGaussMode_orthonormal`: genuine physical gauge-fixed Hilbert family is orthonormal for all `k : ℕ`, not only as ambient Haar modes.
3. `p4Q2PZ37AMU_actualPhysicalGaussHilbert_not_finiteDimensional`: for every finite lattice half-extent `H`, the original SU(2) physical Gauss-law Hilbert carrier is not finite-dimensional; no such property is assumed.
4. `p4Q2PZ37AMU_exists_originalPhysical_unitTopOrthogonalExcitation`: for every `H`, `beta≥0`, a norm-one physical vector exists in the orthogonal complement of the **complete** eigenvalue-one top eigenspace of the normalized physical Wilson one-slab.
5. `p4Q2PZ37AMU_exists_originalPhysical_nonzeroTopOrthogonalExcitation`: same actual physical complement contains a concrete nonzero vector.

These are four explicit `#print axioms` theorem audits plus one compiled definition, not five audited theorems.

## Failure and correction — observed Lean4 structural causes, preserved

- Initial source HEAD `d7277f47ea1c293f7868a38fe7b399c6189e21e1`, [CI #44012603386](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/44012603386) **FAILURE**. Direct errors included `Unknown identifier PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert`: the defining module was not imported; `autoImplicit false` prevented silently treating it as a free variable. The final `end MGAP4D.MathlibAnalytic` incorrectly attempted to close a named namespace while the active scope was an unnamed `noncomputable section`.
- Dependent failed declarations emitted apparent `sorryAx` and unreachable tactics after the missing type, but those records were not trusted as proofs or mathematical counterexamples. The defining source was inspected: `MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryConcreteFiniteTransferWord`, where the exact physical Hilbert abbreviation is declared.
- Minimal same-PR repair: import that existing declaring module, close the anonymous section before named namespace, simplify the norm contradiction. No theorem statement weakening; no change to original physical Wilson operator/Haar/Gauss/AJA.
- Final source HEAD `5724f7fbac942194fd6091b7d51bee6f4f78427c`, blob `1fd629c08cb1f48f02e2e3c87da991a38cff5eee`.

## Independently verified exact-source proof

- [Theorem PR #6826](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6826), **MERGED**.
- [Exact-source CI #44013197469](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/44013197469), event `pull_request`, final source HEAD `5724f7fbac942194fd6091b7d51bee6f4f78427c`: completed/SUCCESS.
- Mandatory Lean job `133804827249` and `Run changed Lean fast check` step: completed/SUCCESS. Actual dependency-closed Lake log ends `Build completed successfully (8830 jobs).`.
- Four new `#print axioms` contain exactly `propext`, `Classical.choice`, `Quot.sound`; **no `sorryAx`**; changed source warning/error **0/0**.
- Independent exact-source receipt job `133807450329`: completed/SUCCESS, `[mcp-receipt] event=pull_request exact_sha=5724f7fbac942194fd6091b7d51bee6f4f78427c source_result=success run=44013197469 attempt=1`.
- Source and actual GitHub test-merge tree **`2de58c60ffdc97d69ef353e307a5bb0ec0d7344b`**.
- Canonical Formal merge commit **`6c4cd670a4502dd54c0e54f1377e3e3ddd72b416`**, with exactly the same merged Git tree `2de58c60ffdc97d69ef353e307a5bb0ec0d7344b`.

## Independent canonical push — still pending at drafting

- [Canonical push CI #44014823430](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/44014823430), event `push`, exact `head_sha=6c4cd670a4502dd54c0e54f1377e3e3ddd72b416`.
- Initial reobservation: workflow `in_progress`, required Lean step `in_progress`. This **is not a successful independent push receipt**. Append the final observed result as a new dated section, without rewriting this initial checkpoint, before treating the record as independently postmerge-push-certified.

## Boundaries still open

AMU establishes finite-volume nonzero original normalized Wilson top-orthogonal physical states, not compatibility with the abstract OS positive-time operator, nor representation of these states by genuine positive-time OS observables. The physical one-slab's nonidentity under strict contraction will be studied separately in AMV. No `C.translate=normalized Wilson one-slab`, no OS–Wilson gluing, no volume-uniform coercivity/continuum mass gap from this finite result.

This is **documentation only**; do not run Strict Lean.
