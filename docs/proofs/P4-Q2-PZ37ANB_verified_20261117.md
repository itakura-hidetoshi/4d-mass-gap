# P4-Q2-PZ37ANB — exact full-periodic SU(N) Wilson positive-half Gibbs fiber law

Date: 2026-11-17 JST. Authoritative Formal branch: `formal/real-hilbert-uniform-coercive-strong-limit`. Canonical pinned Lean: `v4.30.0-rc2`; mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`. Research rules: append-only / tighten-only / overwrite-forbidden / same-root.

## Exact certified mathematics

For any finite even-periodic 4D Wilson lattice parameter H, rank N>0 with a nontrivial SU(N) group, beta >= 0, boundary configuration b and positive open-half configuration x, let d_full(b,x,y) be the **original normalized full-periodic Gibbs density** in the certified boundary-fibered coordinates, with the original full-periodic partition function retained.

Theorem `p4Q2PZ37ANB_fullPeriodicPositiveHalfFiber_eq_vacuum_mul_feature` establishes the exact real-valued negative-half fiber identity:

```text
∫_y d_full(b,x,y) dHaar_negative(y)
  = boundaryVacuumMoment(b) * completedPositiveGramFeature(b,x).
```

Theorem `p4Q2PZ37ANB_fullPeriodicPositiveHalfFiber_pos` proves this fiber integral is **strictly positive**, using the already certified pointwise positive boundary vacuum and completed positive Gram feature. There is no assumption of equality with ANA's normalized temporal-gauge spatial-path law.

Proof route: original full-periodic Gibbs density -> orientation-corrected exact Gram kernel -> original negative-open-half normalized Haar transport -> scalar real Hilbert inner product -> definition of the genuine boundary vacuum moment. The fixed boundary, full original Wilson interactions, original reflection, SU(N) Haar, and full-periodic partition function are preserved.

This is **not** a statement that every full-periodic positive-time marginal equals the ANA normalized half-path probability. The exact marginal pushforward, temporal gauge transport with terminal boundary residual, conditional density and OS realization are future separate proofs.

## Single additive formal source

- Lean: `MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonFullPeriodicPositiveHalfFiberV5_PZ37ANB.lean`
- [Theorem PR #6843](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6843): MERGED.
- Exact-source HEAD: `d6d0552c5cb7c2726cdd7bf5ebfc0a4dd41620bd`.
- Source Lean blob: `71f8583dda10841ac6984ec4d078d65b4d466fff`.
- Source, actual GitHub PR test-merge, and Formal squash tree: `d9d13cb1d393fa0055c3bfa4d1415420bd373742` — three-way exact equality.
- GitHub PR test-merge commit: `978a073959931ac7dcd57c417c63434d9d5fac67`.
- Formal theorem integration HEAD: `b302fc29610ca4b4d2764fac0b92208ed3f6cf16`.

## Independent exact-source CI

- [GitHub Actions #44044663034](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/44044663034): `pull_request` event, exact source `d6d0552c...`, completed / SUCCESS.
- Mandatory Changed Lean fast check job `133907277386`: completed / SUCCESS; its required `Run changed Lean fast check` step completed / SUCCESS.
- Decoded log: `Build completed successfully (8550 jobs).`
- Exactly 2 new theorem `#print axioms`: both only `propext`, `Classical.choice`, `Quot.sound`. No `sorryAx`. Direct changed-source warning/error: 0/0.
- Independent source receipt job `133908719589`: completed / SUCCESS; emitted:

```text
[mcp-receipt] event=pull_request exact_sha=d6d0552c5cb7c2726cdd7bf5ebfc0a4dd41620bd source_result=success run=44044663034 attempt=1
```

## Independent canonical Formal push CI

- [GitHub Actions #44045273155](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/44045273155): `push` event, exact Formal integrated HEAD `b302fc29610ca4b4d2764fac0b92208ed3f6cf16`, attempt 1, completed / SUCCESS.
- Required Lean job `133909289295` and `Run changed Lean fast check` step: completed / SUCCESS.
- Decoded log: `Build completed successfully (8550 jobs).`; two explicit axiom audits: only the same standard three. No `sorryAx`; changed direct warning/error: 0/0.
- Distinct independent push receipt job `133910683085`: completed / SUCCESS; emitted:

```text
[mcp-receipt] event=push exact_sha=b302fc29610ca4b4d2764fac0b92208ed3f6cf16 source_result=success run=44045273155 attempt=1
```

**Certification: FORMAL_INTEGRATED_INDEPENDENT_PUSH_CERTIFIED**, scoped only to ANB's two exact finite-periodic Gibbs negative-half fiber theorems.

## Open mathematical boundary

1. Exact measure-map of the full-periodic Gibbs probability to the **positive closure** `(boundary,positive open-half)`; the certified ANB fiber theorem is an integrand-level result, not yet this pushforward identity.
2. Measurable conditional positive-open-half law at fixed boundary; its density must retain the boundary vacuum and correct `Z_full`.
3. Exact temporal-gauge pushforward onto the ANA spatial half-path, including primary/antipodal boundary compatibility and the residual terminal gauge field, `Z_half` versus `Z_full`.
4. Typed realization of the same concrete time-one Wilson cylinder inside the actual OS positive-time observable algebra; completed OS boundary moment and normalized physical one-slab intertwining.
5. Any positive volume-uniform spectral lower bound or continuous four-dimensional Yang–Mills mass gap.

None of these are certified by the two ANB theorems, and no equivalence is presumed. A separately prepared terminal-gauge extension remains a proposal until its own Lean/CI certification.

This file is Markdown-only. No Strict Lean run is required for its addition or main mirror.
