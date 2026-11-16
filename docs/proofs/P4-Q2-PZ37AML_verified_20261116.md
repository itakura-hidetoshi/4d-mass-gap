# P4-Q2-PZ37AML — genuine original SU(2) Wilson all-plaquette covariance Gram PSD

Date: 2026-11-16 JST. **Theorem independently exact-source certified and merged into Formal.** Postmerge push is a distinct independent certification gate.

## Physical model and exact result

- Authoritative Formal branch: `formal/real-hilbert-uniform-coercive-strong-limit`.
- Pinned Lean `v4.30.0-rc2` and mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`.
- Original unchanged interacting full `SU(2)` compact-Haar Wilson Gibbs probability law `mu[H,beta0]`, `beta0=log(3/2)/64`; all genuine four-edge oriented physical plaquette fundamental characters `chi_p`.
- For any finite original `H>0` and any arbitrary real coefficient vector `a : PhysicalPlaquette(H) -> Real`, the following identity and nonnegativity are proved by Lean, with no postulated covariance PSD:

```text
sum_p a[p] * (sum_q Cov_(actual Wilson Gibbs mu[H,beta0])(chi[q],chi[p]) * a[q])
 = Var_(actual Wilson Gibbs mu[H,beta0])(sum_p a[p] * chi[p])
 = norm(vacuumCenteredL2(sum_p a[p] * chi[p]))^2
 >= 0.
```

The finite covariance matrix is therefore symmetric (AMK) and **positive semidefinite** (AML) on every actual physical plaquette coefficient vector. AMJ's all-plaquette covariance `ell1` bound and AMK's signed Schur `ell2` operator bound are preserved. PSD is not strict positive definiteness and does not provide any lower spectral gap.

## Six new Lean theorem declarations

Single additive source `MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalFixedBeta0GibbsPlaquetteCovarianceGramV5_PZ37AML.lean`.

1. `compactOrientedGibbsCovarianceReal_self_eq_varianceBCF`: actual compact-Haar Gibbs covariance self-pairing equals real Gibbs variance.
2. `compactOrientedGibbsCovarianceReal_finiteFamily_quadratic_eq_variance`: expand finite weighted covariance in both slots and identify actual variance.
3. `compactOrientedGibbsCovarianceReal_finiteFamily_quadratic_eq_centered_norm_sq`: genuine Gibbs-centered Hilbert `L²` Gram identity.
4. `compactOrientedGibbsCovarianceReal_finiteFamily_quadratic_nonneg`: derive PSD from squared norm without assumptions.
5. `GroundStatePosteriorJoint.p4Q2PZ37AML_originalFixedBeta0PhysicalPlaquetteGibbsCovariance_quadratic_eq_variance`: exact true original four-edge SU2 physical specialization.
6. `GroundStatePosteriorJoint.p4Q2PZ37AML_originalFixedBeta0PhysicalPlaquetteGibbsCovariance_quadratic_nonneg`: unconditional physical finite-volume PSD at the original fixed coupling.

Each declaration has an explicit `#print axioms` command. The actual Gibbs covariance and variance are the existing source definitions. No source/physics/pin weakening.

## First source failed — failure history retained

The initial source `c9cd0946a49073badd6fd9e3a07a225d98abe3a3` in [CI #43850793239](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43850793239) had a required Lean step **FAILURE**, direct at line 40 in the self-covariance/variance identity. Under `ProbabilityTheory.variance_eq_sub`, the integrand on the right retained the function-power `(⇑O ^ 2) x`, while the left was a pointwise `(O x)^2`. The tactic `ring` cannot normalize `Pi.pow` function application under an integral. Initial incomplete declarations consequently printed `sorryAx` and are **not certified**.

Append-only [PR #6803](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6803) comment ID `6914244111` records the version-bound typed failure provenance. In repaired source `3e5e763a94f290bb6495618024320b45d6748135`, added `simp only [Pi.pow_apply]` between `rw [hSq]` and `ring`. No change to any theorem statement or physical parameters.

## Exact-source independent success

- [Repaired PR CI #43851750255](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43851750255): event `pull_request`, source `3e5e763a94f290bb6495618024320b45d6748135`, workflow completed/**SUCCESS**.
- Changed-Lean job `133245767142`, required `Run changed Lean fast check` step completed/**SUCCESS**.
- Exact pinned Lean build **11,515/11,515**; all six distinct AML theorem `#print axioms` **6/6** only `propext`, `Classical.choice`, `Quot.sound`. **No `sorryAx`**; AML direct warnings/errors **0/0**.
- Independent exact-source receipt job `133248630117` completed/SUCCESS:
  ```text
  [mcp-receipt] event=pull_request exact_sha=3e5e763a94f290bb6495618024320b45d6748135 source_result=success run=43851750255 attempt=1
  ```
- Actual Formal two-parent theorem MERGE commit `62d9cb29f5f3dcc35ee314b2c07427a2aaccc764`, parents prior Formal `74b0af06f624a7d4cbdc8979df73ccb80e587368` and exact certified source `3e5e763a94f290bb6495618024320b45d6748135`.
- Source/test-merge `7450c096e2a8ecd2ac93fe3dd915f58990ff0277`/canonical theorem Git tree identical: `2210c4ff8b9fe0190ca15341b9c762cec83cd590`.
- Actual independent canonical postmerge [event=push CI #43852665286](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43852665286) started against merged Formal theorem HEAD. Initial status **in_progress**. Do not retroactively claim SUCCESS until reobserving exact HEAD, workflow/Lean job/required step, actual six axiom prints, and independent completion receipt. Append those later as a separate observation.

## Exact physical obstruction retained

AML is a **finite-volume static Gibbs covariance Gram positivity** statement. This does NOT identify the Gibbs plaquette covariance Hilbert carrier with the gauge-invariant OS reflection-positive boundary Hilbert space, nor does it assert an actual OS one-slab transfer, physical Hamiltonian or continuum four-dimensional Yang–Mills mass gap.

The existing true finite one-slab pair Wilson Haar kernel is already constructed in `PeriodicHypercubicEvenSpecialUnitaryOneSlabPairHaarL2Transfer.lean`. The distinct **model-facing gluing conditions** remain explicitly exposed by `PhysicalYangMillsGaugeInvariantOSCommonRealizableOneStepCoherence.lean` (`CommonSemigroupOneStepCoherentAt`, identifying common semigroup translation with actual realizable integer lattice step) and `PhysicalYangMillsWilsonSU2CompletedBoundaryTransferRealizableOneStepRawKernelLimit.lean` (`RealizableOneStepPhysicalTopRawKernelLimitAtFor`, actual translated Wilson synthesis scalar-limit matching normalized one-slab kernel on arbitrary pair-Haar tests). Neither is discharged by AML's Gram identity; no unobserved CodeAI/Lean MCP receipt is claimed.

## Independent canonical postmerge push — later exact-HEAD reobservation

The original "in_progress" observation for canonical push run #43852665286 above remains a historical observation, not overwritten. GitHub MCP subsequently observed the **actual canonical Formal theorem merge** `62d9cb29f5f3dcc35ee314b2c07427a2aaccc764`: [event=push CI #43852665286](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43852665286) **workflow completed/SUCCESS**. Changed-Lean job `133248922004` and required `Run changed Lean fast check` step **completed/SUCCESS**, exact pinned build **11,515/11,515**, all **six AML `#print axioms` outputs** only `propext`, `Classical.choice`, `Quot.sound`, no `sorryAx`, direct AML warning/error **0/0**. This was independently rechecked against the downloadable exact-HEAD Lean log artifact rather than assuming source CI transfers to the merged HEAD.

The distinct independent exact-HEAD completion receipt job `133251970501` completed/SUCCESS and actually printed:

```text
[mcp-receipt] event=push exact_sha=62d9cb29f5f3dcc35ee314b2c07427a2aaccc764 source_result=success run=43852665286 attempt=1
```

The exact source head `3e5e763a94f290bb6495618024320b45d6748135`, synthetic test-merge `7450c096e2a8ecd2ac93fe3dd915f58990ff0277` and canonical Formal theorem merge `62d9cb29f5f3dcc35ee314b2c07427a2aaccc764` have the same verified Git tree `2210c4ff8b9fe0190ca15341b9c762cec83cd590`. This authenticates original fixed-beta0 **finite-volume full interacting Gibbs plaquette covariance Gram PSD only**. The OS boundary/time-one intertwining, physical Hamiltonian and continuum Yang–Mills mass gap remain open.
