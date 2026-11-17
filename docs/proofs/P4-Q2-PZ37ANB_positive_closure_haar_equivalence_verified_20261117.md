# P4-Q2-PZ37ANB — genuine original periodic Wilson positive-closure and Haar measure equivalence

Date: 2026-11-17 JST. Canonical theorem branch: `formal/real-hilbert-uniform-coercive-strong-limit`. Pinned Lean `v4.30.0-rc2`; mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`. Rules: append-only, tighten-only, overwrite-forbidden, same-root, GitHub MCP.

## Certified mathematical statement

Let H be any finite even-periodic original Wilson lattice parameter, N > 0 such that the original SU(N) carrier is nontrivial, and beta >= 0. Write `μ_full` for the actual normalized full-periodic Wilson Gibbs probability, `R_plus` for the original boundary-plus-positive-open-half restriction, and `λ_plus` for the product of the unchanged boundary Haar and positive-open-half Haar probabilities.

The prior independently certified ANB #6849 established the **exact measure identity**

```text
(R_plus)_* μ_full =
  λ_plus.withDensity
    (fun (b,x) => ENNReal.ofReal
      (boundaryVacuumMoment(b) * completedPositiveGramFeature(b,x))).
```

The preceding canonical source separately proved that both the vacuum wavefunction and positive Gram feature are strictly positive pointwise, not merely almost everywhere.

In this step the three newly Lean-certified theorems prove:

1. `p4Q2PZ37ANB_fullPeriodicPositiveClosureGibbs_ac_productHaar`: `(R_plus)_* μ_full ≪ λ_plus`, directly from the exact withDensity identity.
2. `p4Q2PZ37ANB_positiveClosureProductHaar_ac_fullPeriodicGibbs`: `λ_plus ≪ (R_plus)_* μ_full`, from the correctly typed measurable positive ENNReal density and fixed mathlib `withDensity_absolutelyContinuous'`.
3. `p4Q2PZ37ANB_fullPeriodicPositiveClosureGibbs_mutuallyAC_productHaar`: the explicit conjunction, i.e. **exact equality of null sets** at each finite volume.

This is not an equality of the measures themselves, is not a uniform density upper/lower bound in H, and does not identify this full-periodic marginal with ANA's separate normalized temporal-gauge half-path probability or an abstract OS Hilbert state.

## Source file and exact Git trees

- One additive Lean module: `MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonFullPeriodicPositiveClosureHaarEquivalenceV5_PZ37ANB.lean`, 160 lines, 3 theorem `#print axioms`.
- [Theorem PR #6852](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6852): MERGED.
- First candidate source HEAD `73811fd973c67c8a68d36fe04700f798337df6e9`, blob `86e14c665a25a3a5022c8256cd2b19a0fdb6243f`.
- Corrected exact-source HEAD `39c4a8c0972016ca8e3665c02501c218e9942547`, blob `92e081af2e4769d55274b39bd9e5080dd9e526cb`.
- Test-merge commit `ba5eee755db1c33ea2f3d68a30d3fd07d50b722f`.
- Original corrected source, test-merge and actual Formal squash **Git trees are identical**: `d8a2a116f29c6f7053e0931642b5a18e331f7753`.
- Formal theorem merged HEAD: `5bb800c4a0f074671e8f75d9e7a081cf5f5a3694`.

## First failed Lean run — keep the failure and repair distinct

- [First CI #44055656583](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/44055656583): pull_request, completed/FAILURE, mandatory Lean job `133944224368`.
- In the reverse absolute-continuity proof, the `have hb := ... .comp measurable_fst` term was elaborated without an expected source product carrier. The second factor of `Boundary × ?β` was unresolved, causing 6 related Lean errors near lines 92–94. The first theorem alone printed only the standard three axioms; second and third declarations showed `sorryAx` as a **failed elaboration consequence**, never accepted as certified declarations.
- Same-PR repair: give `hb` and `hx` explicit measurable-function types with precisely `BoundaryConfiguration H N × OpenHalfConfiguration H N` as their domain. This repaired the implicit parameter of `measurable_fst` without changing any theorem statement, assumption, original Wilson/Haar definition, normalizer, pinned environment or prior source file.
- Corrected HEAD: `39c4a8c0972016ca8e3665c02501c218e9942547`. Failure and repair remain separate append-only observations for CodeAI/MemoryOS.

## Independent successful exact-source CI

- [Corrected source CI #44056320194](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/44056320194): event `pull_request`, exact corrected HEAD `39c4a8c0972016ca8e3665c02501c218e9942547`, attempt 1, completed/SUCCESS.
- Required `Changed Lean fast check` job `133946517658`, mandatory `Run changed Lean fast check` step completed/SUCCESS.
- Actual decoded log: `Build completed successfully (8565 jobs).`
- Three explicit theorem `#print axioms` outputs: only `propext`, `Classical.choice`, `Quot.sound`. No `sorryAx`. New source warning/error 0/0.
- Distinct exact-source completion receipt job `133948069930` completed/SUCCESS, emitted:

```text
[mcp-receipt] event=pull_request exact_sha=39c4a8c0972016ca8e3665c02501c218e9942547 source_result=success run=44056320194 attempt=1
```

## Independent canonical Formal push

- [Canonical push CI #44057074202](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/44057074202): event `push`, exact integrated HEAD `5bb800c4a0f074671e8f75d9e7a081cf5f5a3694`, attempt 1, completed/SUCCESS.
- Required `Changed Lean fast check` job `133949066159` and mandatory `Run changed Lean fast check` step completed/SUCCESS.
- Decoded log: `Build completed successfully (8565 jobs).`; 3/3 standard axiom audits, no `sorryAx`; changed-source warning/error 0/0.
- Distinct exact-push receipt job `133950447009` completed/SUCCESS:

```text
[mcp-receipt] event=push exact_sha=5bb800c4a0f074671e8f75d9e7a081cf5f5a3694 source_result=success run=44057074202 attempt=1
```

**Certification: FORMAL_INTEGRATED_INDEPENDENT_PUSH_CERTIFIED**, precisely for the stated finite original full-periodic SU(N) positive-closure/Haar absolute-continuity results.

## Still-open independent mathematical barriers

- Turn mutually absolutely continuous positive-closure carriers into typed almost-everywhere observables and actual nonzero original time-one SU(2) Wilson cylinder on that carrier. Absolute continuity alone does not assert a nonzero ANA cylinder in the full-periodic law without a correct measurable transport.
- The original full-periodic Gibbs marginal is not yet identified with ANA's independently normalized temporal-gauge half-path. A typed gauge-fixed pushforward must preserve both original reflection-fixed boundaries, the antipodal terminal residual gauge, `Z_full`, and `Z_half`.
- Completing the actual OS positive-time observable realization, proper boundary moment, original physical one-slab intertwining and all-H gap are separately needed.
- No uniform spectral gap, Euclidean continuum limit or continuous four-dimensional Yang–Mills mass gap is proved.

Documentation only; Strict Lean is not re-run for this record or its main mirror.
