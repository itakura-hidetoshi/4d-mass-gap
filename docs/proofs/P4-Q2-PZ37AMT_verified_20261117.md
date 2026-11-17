# P4-Q2-PZ37AMT — true finite-volume Gauss-law descent of original time-zero Wilson-Haar modes

Date: 2026-11-17 JST. Authoritative Formal branch `formal/real-hilbert-uniform-coercive-strong-limit`. This is a **Lean4-certified finite-volume physical Gauss-law L² theorem**, not an OS–Wilson operator identification or continuum mass-gap result.

## Unchanged exact source and mathematical scope

- Pinned Lean `v4.30.0-rc2`; mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`; append-only / tighten-only / overwrite-forbidden / same-root.
- Original time-zero spatial-slice link Haar, SU(2) Wilson energy, spatial-lattice gauge transformations, real gauge-pullback isometries, closed Gauss-law fixed Hilbert submodule. Neither the original Wilson kernel nor its beta0, AJA, Haar, lattice, original Gauss law, normalized one-slab and physical top-eigenspace definitions were modified.
- One new additive Lean source `MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2PrimarySpatialSliceGaussLawClassModeV5_PZ37AMT.lean`. Final independently certified source blob SHA `cf681070e6057a9fe413bd019ae57a36d88b3eba`; 219 source lines.
- The existing AMS theorem establishes the **ambient** physical time-zero Haar `L²` orthonormal modes but not their typed Gauss-law membership. The existing `SpecialUnitaryTwoWilsonEnergyContinuousGramSchmidtClassFunction` separately establishes conjugacy-invariant continuous representatives. AMT closes this precise compatibility gap.

## Actual new certified theorems (6 explicit axioms audits)

1. `p4Q2PZ37AMT_spatialHolonomy_eq_orientedFourEdge`: native intrinsic primary spatial plaquette holonomy equals the physical four-edge oriented word.
2. `p4Q2PZ37AMT_spatialHolonomy_eq_conj_cyclic`: original oriented holonomy is conjugate to AMS's cyclic four-Haar representative.
3. `p4Q2PZ37AMT_continuousMode_cyclic_eq_intrinsic`: original Wilson Gram–Schmidt class function evaluates equally on these two holonomies, pointwise.
4. `p4Q2PZ37AMT_continuousMode_cyclic_gaugeInvariant`: the actual cyclic mode observable is invariant under every native physical spatial gauge transformation, pointwise.
5. `p4Q2PZ37AMT_spatialMode_coeFn`: exact `Lp` a.e. representative of each AMS Haar mode by the continuous cyclic observable, proved through `Lp.coeFn_compMeasurePreserving`, `ContinuousMap.coeFn_toLp` and the original Haar pushforward.
6. `p4Q2PZ37AMT_spatialMode_mem_closedGaussLaw`: each actual AMS mode is in `periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2ClosedSubmodule H 2`, for every `H,k`. This is not the result of projecting arbitrary ambient modes and claiming their orthonormality survives.

## Exact-source failure/success provenance, retained append-only

- Initial AMT source HEAD `29a8196d297f1a0268ea2f7b6dc2c2d94a0f3907`, [CI #44011305050](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/44011305050): exact-source compilation **completed/SUCCESS**, 8,792/8,792, 6 axiom prints standard-three-only, `sorryAx` absent, source errors 0. The changed source had **two direct warnings**, since `first | rfl | simp[...]` succeeded immediately by `rfl` and rendered the fallback branch unreachable.
- Same PR warning-only repair removed unreachable `simp` and retained the original theorem statement and physics source: source HEAD `b78fadc565bb94202c31b5a1eb24670f9249a1d9`, blob `cf681070e6057a9fe413bd019ae57a36d88b3eba`.
- [Final exact-source PR CI #44011793081](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/44011793081): event `pull_request`, exact HEAD `b78fadc565bb94202c31b5a1eb24670f9249a1d9`, completed/SUCCESS, mandatory Lean job `133800297797` and `Run changed Lean fast check` step completed/SUCCESS. Full log: **8,792/8,792**. Six printed declarations use only `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx`; changed source warning/error **0/0**.
- Exact-source independent receipt job `133801275373` completed/SUCCESS, output: `[mcp-receipt] event=pull_request exact_sha=b78fadc565bb94202c31b5a1eb24670f9249a1d9 source_result=success run=44011793081 attempt=1`.
- Source, test-merge and actual Formal integration Git tree all **`ef845ebbf361c3fc6cb9533a93d19457db17a597`**.
- [Theorem PR #6825](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6825): MERGED at canonical Formal commit `34779a57ed589abb83436b39b1722c3902e48576`.
- [Independent canonical push CI #44012172971](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/44012172971): event `push`, exact merge HEAD `34779a57ed589abb83436b39b1722c3902e48576`, completed/SUCCESS. Mandatory Lean job `133801528994` and Lean step completed/SUCCESS, 8,792/8,792, six standard-three-only audits, no `sorryAx`, changed warning/error 0/0.
- Independent push receipt output: `[mcp-receipt] event=push exact_sha=34779a57ed589abb83436b39b1722c3902e48576 source_result=success run=44012172971 attempt=1`.

## Frontier retained

AMT is an actual physical Gauss-law membership result for the finite original time-zero Haar Hilbert sector, not an infinite-dimensionality theorem by itself. Its successor AMU separately constructs the nonzero physical normalized Wilson top-eigenspace-orthogonal vector and tests this step in the correct physical Hilbert type.

This record asserts neither a typed positive-time OS boundary realization of an arbitrary physical endpoint nor that `C.translate` of AMR is the normalized Wilson one-slab, nor any OS–Wilson operator equality, nor a four-dimensional continuum Yang–Mills mass gap. Documentation-only, **no Strict Lean request**.
