# P4-Q2-PZ37ANJ — original full-periodic SU(2) Wilson positive-closure Haar time-one mean

2026-11-18 JST. Canonical theorem root `itakura-hidetoshi/4d-mass-gap`; authoritative branch `formal/real-hilbert-uniform-coercive-strong-limit`. Fixed Lean `v4.30.0-rc2` and mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`. Append-only / tighten-only / overwrite-forbidden / same-root. No docs-only Strict Lean rerun.

## Precise certified mathematical result

The **unchanged original** finite-volume normalized full-periodic SU(2) Wilson Gibbs model and ANC/ANF genuine time-one Wilson two-mode cylinder `F(c0,c1)(b,x)` are retained. This ANJ leaf is specifically a **product Haar coordinate theorem**, NOT an identification of Gibbs and Haar expectations.

The actual original shared-boundary Haar `λ_boundary` times positive-open-half Haar `λ_open` is transported measure-preservingly along:
1. the exact ANC positive-closure spatial-path map;
2. the exact AMX time-one spatial slice;
3. the exact AMS original four-link spatial-plaquette cyclic holonomy.

The resulting group law is the original **normalized SU(2) Haar**; no independent or separately normalized half-path Wilson law is substituted. ANI's genuine Gram–Schmidt base mode identifies the first chosen continuous Wilson mode with constant one in Haar L2, while the second chosen continuous Wilson mode is Haar-centered. Hence for **all H : ℕ, including H=0**,

```text
∫_SU2 φ0(U) dHaar(U) = 1,
∫_SU2 φ1(U) dHaar(U) = 0,
∫_(boundary × open) F(c0,c1)(b,x) d(λ_boundary ⊗ λ_open) = c0.
```

Combining exact ANG0 β=0 original Wilson boundary-Gram kernel and Fubini using the **original normalized Wilson partition function** gives the new certified identity

```text
∫_boundary M_{H,0,c0,c1}(b) dλ_boundary(b)
  = sqrt(Z_H(0)⁻¹) * c0.
```

This is the **first boundary-Haar moment**, not the squared norm of `M`. A globally zero mean is not the same as a boundary-a.e. vanishing fiber mean. The β=0 H=0 antipodal fixed slice differs geometrically from H>0 positive interior; no unconditional fixed-boundary fiber formula is inferred, and no positivity of the original OS squared boundary-moment integral for the selected top-orthogonal coefficients is claimed.

## Original new Lean source and theorem inventory

`MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonFullPeriodicTimeOneClosureHaarMeanV5_PZ37ANJ.lean`: one additive new Lean file (291 added lines; no changes or deletions to original Wilson model or earlier theorems). Eight proved theorems:

1. `p4Q2PZ37ANJ_originalPositiveClosureTimeOneHolonomy_measurePreserving`
2. `p4Q2PZ37ANJ_originalWilsonContinuousModeZero_haarMean_one`
3. `p4Q2PZ37ANJ_originalPositiveClosureTimeOneMode_integral_eq_Haar`
4. `p4Q2PZ37ANJ_originalPositiveClosureTimeOneModeZero_integral_one`
5. `p4Q2PZ37ANJ_originalPositiveClosureTimeOneModeOne_integral_zero`
6. `p4Q2PZ37ANJ_originalPositiveClosureTimeOneMode_integrable`
7. `p4Q2PZ37ANJ_originalTimeOneTwoMode_closureHaarMean_eq_c0`
8. `p4Q2PZ37ANJ_originalBetaZeroBoundaryGramMoment_boundaryHaarMean`

All eight printed `#print axioms` outputs contain **only** `propext`, `Classical.choice`, `Quot.sound`, with **no `sorryAx`**. New file warning/error 0/0 in source and independent push logs.

## Full repair provenance: two rejected candidates, one certified candidate

- **Initial** source `329c1f9e1e5f1c821be7f720259b9ebe249cc849`: [source run #44149784895](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/44149784895) completed/FAILURE. First seven theorem outputs printed standard three axioms; last theorem **not** certified because pinned `MeasureTheory.integral_prod` could not synthesize `SFinite nu` for local `nu := periodicHypercubicEvenOpenHalfHaarMeasure H 2`. The automatic downstream `sorryAx` printout was not accepted.
- **Second** source `1833d0296fc325b1b55dc6c961f67f78a775c543`: [run #44150545444](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/44150545444) completed/FAILURE. Explicit original open-half Haar finite measure resolved `SFinite nu`; identical final Fubini theorem then required `SFinite mu` for the other named local original boundary Haar measure `mu`. All earlier theorems were unchanged and successful.
- **Final certified** source `b1198958e4a5078adac9010e171c21af604e7067`: add exactly local finite-measure instances for **both** named original Haar factors via their native existing finite Pi Haar definitions, no changed function, law, assumption, or normalization. [Exact-source PR CI #44151196885](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/44151196885) event=`pull_request` completed/SUCCESS, changed Lean job `134279692256` and required Lean step SUCCESS, `8,879/8,879` build, 8/8 standard-three axioms, zero `sorryAx` and direct-file warnings/errors. Independent source receipt job `134281284000` completed/SUCCESS:

```text
[mcp-receipt] event=pull_request exact_sha=b1198958e4a5078adac9010e171c21af604e7067 source_result=success run=44151196885 attempt=1
```

## Exact source, synthetic test-merge, actual Formal integration, independent push

- Theorem [PR #6868](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6868) **MERGED**; parent Formal HEAD `7f2b6ed066e45c3c3a60fff889c08ef6cebb41ea`.
- Verified source HEAD `b1198958e4a5078adac9010e171c21af604e7067`, source Git tree `43c4526c5e140bea0e2b33298a328a91b6f124ac`.
- Synthetic PR test-merge commit `8dfc28d2a57ae1b4504bd1f15398186a5e62f588`, its exact two parents (Formal base, certified source), Git tree `43c4526c5e140bea0e2b33298a328a91b6f124ac`.
- Actual theorem integrated **Formal HEAD** `0e4fc7d20f3a02c3f97688a74c3f054192766ae0`, integrated tree `43c4526c5e140bea0e2b33298a328a91b6f124ac`: source/test-merge/integrated trees exactly equal.
- [Independent canonical Formal event=push CI #44151835940](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/44151835940) completed/SUCCESS. Lean job `134281967628` and required Lean step completed/SUCCESS, `8,879/8,879` jobs; 8 standard-three-only #print axioms; no sorryAx; changed warning/error 0/0. Distinct push receipt job `134284124991` completed/SUCCESS:

```text
[mcp-receipt] event=push exact_sha=0e4fc7d20f3a02c3f97688a74c3f054192766ae0 source_result=success run=44151835940 attempt=1
```

**Status**: `FORMAL_INTEGRATED_INDEPENDENT_PUSH_CERTIFIED` for the eight ANJ finite-volume theorems only. The record is a historical receipt, not a substitute for kernel verification. CodeAI and independent direct Lean MCP executor were unavailable in this session: `NOT_RUN` (GitHub Actions was the actual verifier).

## Unresolved explicit analytic obligations / no invalid global promotion

- The β=0 **fixed-boundary fiber** mean of the unchanged ANC/AMW physical top-eigenspace-orthogonal coefficient pair, for H>0 interior versus H=0 antipodal, is still undetermined. A globally centered product-Haar average does not prove fiberwise a.e. cancellation.
- The original full-periodic Gibbs Wilson OS reflection norm strict positivity of that same physical top-orthogonal two-mode observable, or an explicit nontrivial Wilson OS null vector, remains unproved at β>0.
- Even at β=0, a nonzero first boundary moment for **c0 ≠ 0** is not yet promoted here to a positive OS squared norm or to the physical-top-orthogonal coefficient witness without a separately checked boundary-moment L² / null-space argument.
- Physical OS Hilbert quotient nonzero class, original Wilson one-slab ↔ completed OS boundary operator intertwining, a volume-uniform gap, continuum 4D Yang–Mills construction and mass gap all remain **NO_DATA / obstruction**. Ordinary Gibbs/Haar L² nonzero ⇒ OS positive is an invalid inference.

No existing theorem or model was changed. Failed candidate observations are retained with their exact CI and repair histories.
