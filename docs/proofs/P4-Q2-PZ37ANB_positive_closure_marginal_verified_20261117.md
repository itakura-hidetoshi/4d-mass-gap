# P4-Q2-PZ37ANB — genuine full-periodic Wilson positive-closure marginal

Date: 2026-11-17 JST. Authoritative branch: `formal/real-hilbert-uniform-coercive-strong-limit`. Lean `v4.30.0-rc2`; mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`. Append-only / tighten-only / overwrite-forbidden / same-root.

## Original-model theorem scope

This step follows the independently source/push-certified two ANB fiber theorems in [P4-Q2-PZ37ANB_verified_20261117.md](P4-Q2-PZ37ANB_verified_20261117.md), and does not alter their source.

For original even-periodic four-dimensional `SU(N)` Wilson Gibbs probability `μ_full`, let `R_+` be the explicit positive-closure map retaining BOTH the common reflection-fixed boundary `b` and the positive open-half physical-link configuration `x`, discarding only the negative open-half configuration `y`. The theorem constructs the exact equality of measures

```text
(R_+)_* μ_full
  = (Haar_boundary ⊗ Haar_positive).withDensity
      (fun (b,x) => ∫⁻ y, ρ_full(b,x,y) ∂Haar_negative)
```

where `ρ_full` is the **original full-periodic normalized** Wilson Gibbs density, including the true full-periodic partition function. The theorem is NOT equality with ANA's separately normalized interacting temporal-gauge spatial positive-half path probability. The pre-existing ANB real-valued fiber theorem can be combined with this result after a separate ENNReal conversion proof; that conversion is not part of this exact-source theorem.

Three declarations, all kernel-audited independently:

1. `p4Q2PZ37ANB_map_withDensity_measurableEquiv`: transport measurable densities through an actual measurable equivalence.
2. `p4Q2PZ37ANB_map_positiveClosure_prod_withDensity`: preserve the boundary-plus-positive pair under the pushforward of a density on boundary × (positive × negative), integrating only the last coordinate via the pinned `Measure.prodAssoc_prod`, `setLIntegral_map`, and `measure_map_fst_prod_withDensity` APIs.
3. `p4Q2PZ37ANB_fullPeriodicGibbs_positiveClosure_marginal`: the literal original finite Wilson Gibbs law, with exact boundary and positive restrictions.

Source file: `MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonFullPeriodicPositiveClosureMarginalV5_PZ37ANB.lean`; 207 source lines, three `#print axioms`.

## Failed first source and exact minimal repair

- [Theorem PR #6846](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6846) initial HEAD `88b602b8eda3e8b4865ab33ac4fadc0c3ac897ad`, source blob `05070fd302681c24352c4d3bb2546ff8fa3b97cc`.
- [Initial exact-source CI #44046432046](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/44046432046): `pull_request`, completed/FAILURE. One **direct Lean elaboration error**, source line 188:82, final theorem `unsolved goals`. After `rw [hcomp]`, Lean showed an identical measure-map expression on both sides but had not closed the reflexive goal. The first two theorem `#print axioms` audits displayed only the standard three; the third showed `sorryAx` from the failed elaboration, **not an accepted proof**.
- In the **same PR**, insert only `rfl` after `rw [hcomp]` in the final theorem. No theorem statement, physical hypothesis, Wilson/Haar geometry, normalization, model or toolchain was weakened or modified.
- Repaired exact source HEAD `2a0c2db3232f489997bad3eedb8001d3d258e67b`; repaired blob `e556ca85d2ee5c5ea5612a0fa2b3ab5e02b8ed0e`.

## Exact-source independent CI

- [Corrected source CI #44047088998](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/44047088998), event `pull_request`, exact HEAD `2a0c2db3232f489997bad3eedb8001d3d258e67b`, attempt 1, completed/SUCCESS.
- Required Lean job `133915364432` and `Run changed Lean fast check` step completed/SUCCESS. Decoded log: `Build completed successfully (8562 jobs).`
- Three theorem `#print axioms` are exactly the standard `propext`, `Classical.choice`, `Quot.sound` only, **no `sorryAx`**, changed-source warning/error **0/0**.
- Independent completion receipt job `133916648572` completed/SUCCESS, emitted:

```text
[mcp-receipt] event=pull_request exact_sha=2a0c2db3232f489997bad3eedb8001d3d258e67b source_result=success run=44047088998 attempt=1
```

- Actual corrected source Git tree, GitHub test-merge tree, and Formal squash tree are identical: `0fdb5c2b02fbeb52269013ad6b8835e2d4ad7d1e`.
- Corrected test-merge commit: `66bd6f9de92f735b94f88e965d78da936d2cab39`.
- Formal theorem merged HEAD: `fcde2ab4648a9df0c9b9a3165e10c682cde04e18`.

## Independent Formal post-merge push

- [Canonical push CI #44047592307](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/44047592307), event `push`, exact Formal merged HEAD `fcde2ab4648a9df0c9b9a3165e10c682cde04e18`, completed/SUCCESS.
- Required Lean job `133917054193` and required `Run changed Lean fast check` step completed/SUCCESS. Decoded log: `Build completed successfully (8562 jobs).`
- Three theorem `#print axioms` use only the standard three; no `sorryAx`; changed direct warning/error `0/0`.
- Independent completion receipt job `133918861349` completed/SUCCESS, emitted:

```text
[mcp-receipt] event=push exact_sha=fcde2ab4648a9df0c9b9a3165e10c682cde04e18 source_result=success run=44047592307 attempt=1
```

**Certification: FORMAL_INTEGRATED_INDEPENDENT_PUSH_CERTIFIED** for exactly the three finite original full-periodic positive-closure measure pushforward theorems.

## Remaining independent obstructions

1. Convert the positive-closure marginal's **ENNReal** fiber density to the original pointwise real-valued `boundaryVacuumMoment(b) × completedPositiveGramFeature(b,x)` from the first ANB source, with actual positivity, finiteness and integrability, and construct the exact normalized boundary conditional measure.
2. Perform actual temporal gauge fixing on positive-half path and temporal-link Haar coordinates, including the primary and antipodal boundary gauge compatibility and the nontrivial terminal residual; identify the resulting measure with ANA's exact normalized temporal-gauge half-path only by an established Radon–Nikodym density that retains **both** `Z_full` and `Z_half`.
3. Realize the same time-one Wilson cylinder inside the chosen abstract OS positive-time observable algebra; identify its completed boundary moment with the genuine physical Wilson one-slab transfer via a typed intertwining.
4. Prove any nonzero volume-uniform spectral gap and the continuum four-dimensional Yang–Mills mass gap.

No such subsequent claim follows from this marginal theorem alone. In particular `(R_+)_* μ_full` is not the ANA half-path law simply by preference, and `L²(ANA)` is not an abstract OS Hilbert state by construction.

Docs only. Strict Lean is not re-run for this record or a main mirror.
