# P4-Q2-PZ37ANA — original normalized interacting Wilson positive-time nonzero real L² cylinder

Date: 2026-11-17 JST. Authoritative Formal branch `formal/real-hilbert-uniform-coercive-strong-limit`; `main` is an exact but separately maintained documentation mirror. Pinned Lean `v4.30.0-rc2`, mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`. Append-only/tighten-only/overwrite-forbidden/same-root.

## Mathematical scope and actual original source

AMW #6830 independently certifies a genuine two-mode SU(2) native physical Gauss-law state in the **complete normalized Wilson one-slab top-orthogonal subspace**. AMX #6833 lifts its exact pointwise spatial Wilson cylinder to original positive-half time one under product spatial Haar. AMY #6836 proves this cylinder nonzero a.e. under original **unnormalized interacting** temporal-gauge Wilson positive-half path law. AMZ #6837 proves the actual original finite Wilson half-path partition mass `0<Z_half≤1`, constructs the **normalized interacting positive-half probability**, and proves the same literal cylinder remains nonzero a.e.

ANA adds actual **real `Lp ℝ 2` membership and a nonzero physical-mode-based Hilbert vector**, not a mere formal a.e.-nonzero observation:

- `p4Q2PZ37ANA_timeOneTwoModeWilsonObservable`: exact literal unchanged time-one two-Wilson-mode class-function cylinder on original spatial positive-half path.
- `p4Q2PZ37ANA_timeOneTwoModeWilsonObservable_measurable`: measurable using real original time-one eval and primary plaquette cyclic holonomy measure-preserving maps.
- `p4Q2PZ37ANA_timeOneTwoModeWilsonObservable_norm_le`: exact uniform bound in terms of two canonical continuous SU(2) Gram–Schmidt mode norms, via `ContinuousMap.norm_coe_le_norm`.
- `p4Q2PZ37ANA_timeOneTwoModeWilsonObservable_memLp`: square-integrability over AMZ's exact original normalized interacting half-path **probability** via pinned `MemLp.of_bound`.
- `p4Q2PZ37ANA_normalizedWilsonTimeOneTwoModeL2`: constructs literal real `Lp ℝ 2` vector with no changed source model.
- `p4Q2PZ37ANA_normalizedWilsonTimeOneTwoModeL2_coeFn`: exact almost-everywhere representative of this L² vector.
- `p4Q2PZ37ANA_exists_nonzero_normalizedInteractingWilsonTimeOneL2`: chooses AMZ's original two-mode Gauss/top-orthogonal physical state, proves corresponding normalized interacting positive-time `L²` vector **nonzero** while matching its exact original pointwise cylinder.

Five explicit theorem `#print axioms`, plus two compiled definitions.

One additive Lean file `MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2NormalizedInteractingPositiveTimeL2CylinderV5_PZ37ANA.lean`, 184 source lines. Final source HEAD `3954ba41fb7cc3963285d0ac85da3b3e50f00703`, blob `9850fec935b7eb5856a53ac431d2d992c8705d4e`.

## Failure and repair retained append-only

- Initial exact-source source HEAD `0fbf49eceedf49c150c7199d43795c45ad7467c8`; [CI #44028545805](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/44028545805) **FAILURE**, one direct error at final nonzero L² theorem, line 169:45. After `ψ=0`, Lean left a goal equating the zero `Lp` representative a.e. to the zero function; `rw [hzero]; simp` was not enough. First four printed theorem axioms were standard-three; failed fifth `#print axioms` showed `sorryAx` as a failed elaboration consequence, **not** as accepted proof.
- The actual pinned `Lp.coeFn_zero` API and identical canonical usage in `PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferStrictlyPositiveTopEigenvector.lean` were inspected. Source-local fix replaces the residual `simp` with `simpa only [Pi.zero_apply] using (Lp.coeFn_zero ℝ 2 ν)`.
- Same PR repair, source HEAD `3954ba41fb7cc3963285d0ac85da3b3e50f00703`; no changed theorem statements, assumptions, original lattice, Wilson kernel, half-path normalization or imports. Failed and successful HEADs remain distinct.

## Independent exact-source machine certification

- Theorem [PR #6840](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6840) **MERGED**.
- [Exact-source CI #44029016434](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/44029016434): `event=pull_request`, exact source HEAD `3954ba41fb7cc3963285d0ac85da3b3e50f00703`, workflow completed/SUCCESS.
- Required Lean job `133856158200`, `Run changed Lean fast check` step completed/SUCCESS, full decoded log ends `Build completed successfully (8842 jobs).`.
- Five theorem `#print axioms` outputs: **5/5 exactly** `propext`, `Classical.choice`, `Quot.sound`; **no `sorryAx`**, changed source warning/error **0/0**.
- Exact-source independent receipt job `133857331714` completed/SUCCESS: `[mcp-receipt] event=pull_request exact_sha=3954ba41fb7cc3963285d0ac85da3b3e50f00703 source_result=success run=44029016434 attempt=1`.
- Exact source, GitHub PR test-merge and actual canonical Formal merged Git tree all **`a7187e806fb2feccccd4311acbbeed9cd6442f1c`**.
- Canonical Formal theorem integration HEAD **`b6454679748b8074e6ff9fa2d41ed8e3a017cc88`**.

## Independent canonical push — separate checkpoint pending final receipt

- Canonical [push CI #44029571978](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/44029571978), event `push`, exactly `head_sha=b6454679748b8074e6ff9fa2d41ed8e3a017cc88` was `in_progress` at this record's drafting.
- **Do not** treat pending or cancelled push as successful independent certification. Reobserve workflow, mandatory Lean step, decoded logs, full five theorem axiom audit, and exact HEAD receipt, then append a separately dated successor section, not overwrite this checkpoint.

## Explicit physical/OS obstruction

ANA proves only a **finite original, precisely normalized positive-half temporal-gauge Wilson path** real L² state. This path law is not proven equal to the **full-periodic Wilson Gibbs probability** on original finite even-periodic SU(2) configurations; it is not automatically a `D.positiveTimeSubalgebra` state for arbitrary given coherent OS data `Q`, nor the range of `Q.physicalHilbertBoundaryMomentLinearIsometry`. No mathematical equality between genuine normalized physical Wilson one-slab and abstract `C.translate`, and no 4D continuum Yang–Mills mass gap, is asserted.

This record is Markdown-only; Strict Lean must not run.

## 2026-11-17 JST independent canonical push SUCCESS

The earlier observed push `in_progress` checkpoint remains historically valid. The later independent GitHub MCP observation establishes **completion on the exact merged ANA Formal source**:

- [Canonical push CI #44029571978](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/44029571978): event `push`, exact `head_sha=b6454679748b8074e6ff9fa2d41ed8e3a017cc88`, attempt 1, workflow **completed/SUCCESS**.
- Required Lean job `133857962074` and mandatory `Run changed Lean fast check` step both completed/SUCCESS; full decoded log ends `Build completed successfully (8842 jobs).`.
- All five ANA `#print axioms` use only `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx`; direct ANA warning/error `0/0`.
- Independent receipt job `133859097654` completed/SUCCESS. Exact emitted receipt: `[mcp-receipt] event=push exact_sha=b6454679748b8074e6ff9fa2d41ed8e3a017cc88 source_result=success run=44029571978 attempt=1`.
- Certified source `3954ba41fb7cc3963285d0ac85da3b3e50f00703`, test-merge and actual merged Formal Git trees all equal `a7187e806fb2feccccd4311acbbeed9cd6442f1c`.

Result state: **FORMAL_INTEGRATED_INDEPENDENT_PUSH_CERTIFIED** within ANA's original normalized finite interacting Wilson positive-time half-path `Lp ℝ 2` scope. Not a certification of arbitrary abstract OS-positive-time carrier realization, full-periodic Gibbs law identity, OS–Wilson one-slab equivalence, or continuum 4D YM mass gap.

This is documentation only; no Strict Lean is run.
