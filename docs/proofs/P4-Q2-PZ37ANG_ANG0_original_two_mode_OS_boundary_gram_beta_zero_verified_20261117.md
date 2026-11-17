# P4-Q2-PZ37ANG / ANG0 — original Wilson two-mode OS boundary Gram and beta-zero Haar-mean obstruction

Date: 2026-11-17 JST. Repository: `itakura-hidetoshi/4d-mass-gap`.
Authoritative theorem branch: `formal/real-hilbert-uniform-coercive-strong-limit`.
Pinned Lean `v4.30.0-rc2`; mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`.
Protocol: append-only / tighten-only / overwrite-forbidden / same-root; no docs-only Strict Lean rerun.

## Exact certified mathematical scope

This is the **original** normalized finite four-dimensional even-periodic SU(2) full-periodic Wilson Gibbs measure and the unchanged ANF/ANC original positive-time-one two-Wilson-mode observable on the **reflection-fixed shared boundary and positive open half**. No ANA temporal-gauge half-path probability substitutes for this measure, and the original partition function is not changed.

Write `F(c0,c1)(b,x)` for the unchanged time-one cylinder, and `G(H,beta)(b,x)` for the original normalized Wilson completed-positive boundary Gram feature. ANG proves exact **pointwise** coefficient linearity and linearity of the actual boundary moment:

```text
M(c0,c1)(b) = ∫_open G(H,beta)(b,x) F(c0,c1)(b,x) dHaar_open(x)
            = c0 * M(1,0)(b) + c1 * M(0,1)(b).
Q_OS(c0,c1) = ∫_boundary |c0*M(1,0)(b) + c1*M(0,1)(b)|² dHaar_boundary(b).
```

ANG also proves that **boundary-a.e. cancellation** of the displayed moment implies `Q_OS=0`. This is a **sufficient obstruction** only; no nontrivial cancellation coefficients or physical-top-orthogonal coefficients have been shown to satisfy it unconditionally.

ANG0 invokes the existing precisely zero-coupled physical Wilson Gram feature identity `G(H,0)(b,x) = sqrt(Z_H(0)⁻¹)` and proves the exact formula for the **same original time-one cylinder**, retaining any actual dependence of `F` on the boundary:

```text
M_0(c0,c1)(b) = sqrt(Z_H(0)⁻¹) * ∫_open F(c0,c1)(b,x) dHaar_open(x).
```

If the latter open-half Haar mean vanishes for **boundary-Haar almost every b**, ANG0 proves the original time-one Wilson `Q_OS=0` at beta=0. Boundary independence of **G** alone is not used to assert zero mean of **F**. In particular, ordinary nonzero Gibbs/Haar L² of F does **not** imply positive OS seminorm.

## Exact changed Lean sources and declarations

Both are newly added files, with no edits or deletions to existing Wilson model or hypotheses:

1. `MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonFullPeriodicTwoModeOSGramKernelV5_PZ37ANG.lean` (five theorems)
   - `p4Q2PZ37ANG_originalTimeOneObservable_twoMode_linear`
   - `p4Q2PZ37ANG_originalTimeOneBoundaryGramFeature_integrable`
   - `p4Q2PZ37ANG_originalTimeOneBoundaryGramMoment_twoMode_linear`
   - `p4Q2PZ37ANG_originalTimeOneWilsonOSQuadratic_eq_twoModeMoment_sq`
   - `p4Q2PZ37ANG_originalTimeOneWilsonOSQuadratic_zero_of_modeCancellation`
2. `MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonFullPeriodicTwoModeOSGramBetaZeroV5_PZ37ANG0.lean` (two theorems)
   - `p4Q2PZ37ANG0_originalTimeOneBoundaryMoment_eq_openHaarMean`
   - `p4Q2PZ37ANG0_originalTimeOneOSQuadratic_zero_of_openHaarMean_ae_zero`

All seven `#print axioms` outputs contain **only** `propext`, `Classical.choice` and `Quot.sound`; no `sorryAx`. Changed-file warning/error 0/0. Complete source, local imports and dependency signatures were inspected at the exact source HEAD. Local direct Lean MCP and repository CodeAI runtime were not exposed to this session: `NOT_RUN`. The actual independent verifier is GitHub Actions' pinned Lean environment.

## Exact-source, test-merge and independent Formal integrated-head evidence

- [Theorem PR #6863](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6863): **MERGED**.
- Source parent Formal HEAD before the new theorem PR: `dc9bb958df77ff75eebf25f7a645ff6f95fa30e6`.
- Tested source HEAD: `1e58efb2935a9be4a7f7161ce6c17663fe595822`.
- Source Git tree: `93a0b400f629590481ca584a6604c5f54f44c726`.
- PR synthetic test-merge commit: `936ddb88d1efd662f50c6289793f04316f7df733`; test-merge tree: `93a0b400f629590481ca584a6604c5f54f44c726`.
- [Source CI #44081246060](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/44081246060): event=`pull_request`, completed/SUCCESS, changed Lean job `134032099796` completed/SUCCESS, `8876/8876` actual Lean jobs built; independent exact-head receipt job `134034867136` completed/SUCCESS:

```text
[mcp-receipt] event=pull_request exact_sha=1e58efb2935a9be4a7f7161ce6c17663fe595822 source_result=success run=44081246060 attempt=1
```

- Theorem integrated **Formal HEAD**: `de5b2d769706c99470ece2746b42e3ac1e6306d7`, exact integrated tree `93a0b400f629590481ca584a6604c5f54f44c726` (**identical** to source and test-merge).
- [Independent actual Formal push CI #44082674307](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/44082674307): event=`push`, completed/SUCCESS. Changed Lean job `134036982380` and its required Lean step completed/SUCCESS. `8876/8876` built; seven new standard-three-only axioms; no `sorryAx`; changed warning/error 0/0. Independent push receipt job `134038528131` completed/SUCCESS:

```text
[mcp-receipt] event=push exact_sha=de5b2d769706c99470ece2746b42e3ac1e6306d7 source_result=success run=44082674307 attempt=1
```

Status: `FORMAL_INTEGRATED_INDEPENDENT_PUSH_CERTIFIED` **for these seven theorems alone**. This document is a historical audit receipt and is not Lean proof authority by itself.

## Explicit next obstruction (NO_DATA retained)

1. **beta=0:** Compute the true fiber open-half Haar mean of the **unchanged original physical top-eigenspace-orthogonal** ANC/AMW coefficient pair. The old general beta-zero Gram-feature rank-one theorem does not itself prove this particular `F` has zero moment.
2. **beta>0:** Directly prove nonzero original Wilson boundary Gram moment for that same physical two-mode coefficient pair, or exhibit a concrete nontrivial a.e.-moment-cancellation null vector. Need explicit Wilson/Haar/Fubini and actual boundary-fibered kernel control.
3. Only after strictly positive OS seminorm is established may one construct the nonzero physical OS quotient class, and independently address original Wilson one-slab ↔ completed OS boundary operator intertwining.
4. Neither volume-uniform spectral gap nor continuum four-dimensional Yang–Mills construction / mass gap follows. Ordinary nonzero Gibbs L² ⇒ OS strict positivity is **forbidden**.

All seven finite-volume theorems are certified; the four remaining analytical questions are **unproved**, not impossible.
