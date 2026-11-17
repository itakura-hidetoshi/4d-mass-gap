# P4-Q2-PZ37AMS — original time-zero spatial-slice Haar modes and gauge-invariant plaquette powers

Date: 2026-11-17 JST. **Exact-source Lean4 certified and independently canonical-push certified at a specific Formal HEAD.** This is an ambient spatial-slice Haar `L²` theorem with a separate pointwise gauge-invariance theorem, **not yet a typed Gauss-law physical Hilbert-space orthonormal sequence**.

## Root and fixed inputs

- Repository: `itakura-hidetoshi/4d-mass-gap`. Authoritative branch: `formal/real-hilbert-uniform-coercive-strong-limit`. `main` is a separately maintained documentation mirror.
- Lean `v4.30.0-rc2`, pinned mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`. Append-only / tighten-only / overwrite-forbidden / same-root.
- Original periodic physical three-dimensional time-zero spatial-slice link carrier, original SU(N) normalized product Haar, existing Gauss action, original Wilson plaquette energies. No changes to the original physical Wilson system, its beta0, half-weight, transfer kernel, Gauss law or AJA.
- New theorem source: `MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2PrimarySpatialSliceHaarPhysicalGaugeModeV5_PZ37AMS.lean` (228 source lines at the exact certified source). Its Formal-merged blob SHA is `49980bf9ccbbc870b5c9b9048dc53e854b4c9f04`.

## What is proved in Lean

1. `p4Q2PZ37AMS_primarySpatialSliceEdge_full`: the four native spatial-slice edges project back to the four actual original 4D canonical plaquette edges. The resulting `Fin 4 ↪ PeriodicHypercubicEvenSpatialSliceLink H` is injective.
2. `p4Q2PZ37AMS_measurePreserving_primarySpatialSliceFourEdges`: restriction of the original full spatial-slice product Haar to these four physical links is exactly the independent four-coordinate normalized Haar product.
3. `p4Q2PZ37AMS_measurePreserving_primarySpatialSliceCyclicHolonomy`: the actual cyclic four-Haar plaquette word has normalized Haar pushforward. The resulting `p4Q2PZ37AMS_primarySpatialSliceHolonomyL2Pullback` is a **real linear isometry** from one SU(N) Haar `L²` to the **ambient** native spatial-slice Haar `L²`.
4. `p4Q2PZ37AMS_primarySpatialSliceWilsonEnergy_orthonormal`: the concrete SU(2) energy-power Gram–Schmidt family is orthonormal after that ambient spatial-slice isometry.
5. `p4Q2PZ37AMS_primarySpatialPlaquetteEnergyPower_gaugeInvariant`: each actual intrinsic time-zero plaquette Wilson-energy power is **pointwise invariant** under every original native spatial-lattice gauge transformation.

The five explicit `#print axioms` commands correspond to five named theorem declarations listed above. Importantly, pointwise gauge invariance of the intrinsic energy powers is **not automatically** a proof that the independently constructed cyclic-holonomy `Lp` Gram–Schmidt representatives belong to the Gauss-law fixed submodule.

## Failure and correction — append-only repair memory

- First AMS source HEAD: `3094e50a9cea0f1d17c1ffbbd246197018e38035`. [Exact-source CI #43990850574](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43990850574) **FAILED**, reporting at source line 126 a failure to synthesize `Fintype (PeriodicHypercubicEvenSpatialSliceLink H)`.
- Structural diagnosis: an available `Finite` instance does not itself give the explicit `Fintype` expected by finite-coordinate product-Haar elaboration. A `local instance` from another imported module is not exported to the consumer's elaboration context.
- Tight source-local repair: add `local instance p4Q2PZ37AMS_spatialLinkFintype (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) := Fintype.ofFinite _`, without modifying theorem statements, physical model, or imports. Former downstream axiom audit noise from failed elaboration disappeared following the correction.
- Failure and success observations remain distinct; no red CI is retroactively changed.

## Exact-source and independent postmerge CI evidence

- Theorem [PR #6823](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6823) **MERGED**.
- Certified exact-source HEAD: `bc4849f41a8dda8837a371d676800f5a3f077b1a`; [exact-source PR CI #43999383904](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43999383904), event `pull_request`, workflow completed/SUCCESS, required `Changed Lean fast check` job `133759347350` and `Run changed Lean fast check` step completed/SUCCESS; independent receipt job `133760539235` completed/SUCCESS.
- Canonical Formal merge SHA: `522c1db41644ec843b4dcbeb706b8f115f985367`.
- [Independent postmerge **push CI #43999959747**](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43999959747): event `push`, `head_sha=522c1db41644ec843b4dcbeb706b8f115f985367`, attempt 1, workflow completed/SUCCESS.
- Its required Lean job `133761399798`, mandatory `Run changed Lean fast check` step completed/SUCCESS. The decoded log ends with `Build completed successfully (8789 jobs).` AMS direct warning/error: `0/0`; older unchanged files may have their own warnings.
- All five AMS `#print axioms` results rely only on the standard `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx`.
- Its independent receipt job `133771333946` completed/SUCCESS and emitted exactly:

  ```text
  [mcp-receipt] event=push exact_sha=522c1db41644ec843b4dcbeb706b8f115f985367 source_result=success run=43999959747 attempt=1
  ```

- **Distinct historical provenance:** the earlier AMR-only Formal merge HEAD `30551be0570d66e63c03b2ac04b4f7552fcf97bb` had independent [push CI #43989916990](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43989916990) completed/CANCELLED. AMS's independent success establishes the later merged source, not historical success of the earlier cancelled run.

## Frontier: actual finite-volume Gauss-law descent

Existing sources define
`periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2ClosedSubmodule`
and prove membership iff invariance under every spatial gauge `Lp` pullback. Existing `SpecialUnitaryTwoWilsonEnergyContinuousGramSchmidtClassFunction` proves the canonical continuous SU(2) Gram–Schmidt representatives are conjugacy-invariant.

A further **new** typed proof must connect the AMS cyclic-holonomy pullback to these actual pointwise class-function representatives (including the intrinsic plaquette/cyclic conjugacy) and show equality of the corresponding `Lp` vectors. Only then may the infinite orthonormal sequence descend to the actual Gauss-law fixed Hilbert carrier.

After a genuinely infinite orthonormal physical family, one must still construct a nonzero vector in the orthogonal complement of the normalized Wilson top eigenspace, show physical one-slab contraction acts on it, construct its actual OS boundary representative and prove genuine one-slab compatibility. Neither the abstract identity OS semigroup from AMR nor these ambient slice modes identify the physical one-slab evolution. A continuum 4D Yang–Mills mass gap remains unproved.

This documentation-only certification record does **not** request a new Strict Lean run.
