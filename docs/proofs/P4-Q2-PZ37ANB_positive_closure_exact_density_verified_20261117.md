# P4-Q2-PZ37ANB — exact original full-periodic positive-closure Wilson density

Date: 2026-11-17 JST. Authoritative Formal branch: `formal/real-hilbert-uniform-coercive-strong-limit`. Lean `v4.30.0-rc2`, mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`. Operations: append-only / tighten-only / overwrite-forbidden / same-root, GitHub MCP, exact-source and independent push CI.

## Precisely certified theorem scope

This additive step combines two **previously independently certified** ANB results without weakening or redefining them:

- ANB [#6843](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6843) — the original normalized even-periodic SU(N) Wilson Gibbs density, integrated over the negative open-half Haar law, equals the genuine boundary vacuum `Ψ_boundary(b)` times the completed positive-half Gram feature `G_plus(b,x)`; the fiber integral is strictly positive.
- ANB [#6846](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6846) — the exact original full-periodic Wilson Gibbs probability pushes forward under `(boundaryRestriction, positiveRestriction)` to the unchanged product boundary/positive-open-half Haar law weighted by the negative-half Gibbs fiber `lintegral`.

The new theorem `p4Q2PZ37ANB_fullPeriodicPositiveHalfFiber_lintegral_eq_ofReal_vacuum_mul_feature` proves the exact missing **ENNReal / real integral** bridge, with integrability from the certified pointwise original Gibbs-density bound `ρ_full.toReal ≤ 1 / Z_full` and the original finite product Haar law:

```text
∫⁻ y, ρ_full(b,x,y) dHaar_negative
   = ENNReal.ofReal (Ψ_boundary(b) * G_plus(b,x)).
```

The new theorem `p4Q2PZ37ANB_fullPeriodicGibbs_positiveClosure_marginal_eq_vacuum_mul_feature` gives the genuine probability-measure equality:

```text
map (boundaryRestriction, positiveRestriction) μ_full_Gibbs
   = (Haar_boundary ⊗ Haar_positive).withDensity
       (fun (b,x) => ENNReal.ofReal (Ψ_boundary(b) * G_plus(b,x))).
```

This holds for every finite H, N>0 with nontrivial SU(N), and beta≥0, within the existing precisely normalized original periodic Wilson system. The original `Z_full` remains inside the certified boundary Gram feature and vacuum; it is never substituted by ANA's `Z_half`. The new explicit density is strictly positive by the original ANB fiber/Gram positivity. These theorems do **NOT** identify the original Gibbs positive-time marginal with ANA's normalized temporal-gauge spatial-path law, any arbitrary OS positive-time algebra, physical one-slab transfer, or a 4D continuum mass gap.

## Single additive Lean source

- `MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonFullPeriodicPositiveClosureExactVacuumFeatureDensityV5_PZ37ANB.lean` — 161 source lines, 2 new theorems, 2 explicit `#print axioms`; imports certified ANB #6843 and #6846 theorem modules.
- [PR #6849](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6849): **MERGED**.
- Initial source HEAD `b38ac7fd7f87ec74aa83a2ecbf828fcd13251db3`, blob `af161caa22735a54a098927bc26a9cbfd2f70730`.
- Corrected exact-source HEAD `9f495de098a93acbc6e592d9ec80e60fe0a8d163`, blob `fab7ebd147af5ce4e9ea570c672d6fd7250d1b7e`.
- Corrected source, actual GitHub PR test-merge, and Formal squash Git tree: **`1f5cb9c267f290ae398615643500d3e5ab6e8ec2`**, exact three-way equality.
- Formal theorem merge HEAD `ab2d7e56a7cabda5b65dd0e2b3e20e2732132e84`.

## Append-only failure / repair provenance

- Initial [CI #44052283780](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/44052283780) `pull_request` event: **completed / FAILURE**. Source-local direct Lean error at line 88:8 — `rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]` attempted to rewrite a real norm after `dsimp [f]` had already normalized the expression to `|ρ.toReal|`. Thus no norm pattern remained. Subsequent `sorryAx` printouts were consequences of failed elaboration, never valid certificates.
- Same-PR exact minimal repair: remove redundant `Real.norm_eq_abs` from that `rw`, retaining `rw [abs_of_nonneg ENNReal.toReal_nonneg]`. No theorem statement, assumption, model, Wilson action, Haar law, partition normalizer, prior import, pin or root was changed.
- Both failed and corrected heads are retained in the research workbench as distinct observations, not overwritten.

## Independent corrected Exact-source CI

- [Corrected CI #44053015102](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/44053015102): `pull_request` event, exact corrected HEAD `9f495de098a93acbc6e592d9ec80e60fe0a8d163`, attempt 1, workflow **completed / SUCCESS**.
- Required `Changed Lean fast check` job `133935249249`, and its `Run changed Lean fast check` step: **completed / SUCCESS**.
- Decoded full log: `Build completed successfully (8564 jobs).`
- Both new theorem `#print axioms` outputs: exactly `propext`, `Classical.choice`, `Quot.sound`. No `sorryAx`. Changed-source warning/error **0/0**.
- Distinct exact-source receipt job `133936967654`: **completed / SUCCESS**, emitted:

```text
[mcp-receipt] event=pull_request exact_sha=9f495de098a93acbc6e592d9ec80e60fe0a8d163 source_result=success run=44053015102 attempt=1
```

## Independent canonical Formal push CI

- [CI #44053827415](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/44053827415): event `push`, exact merged Formal HEAD `ab2d7e56a7cabda5b65dd0e2b3e20e2732132e84`, attempt 1, workflow **completed / SUCCESS**.
- Required `Changed Lean fast check` job `133937961335` and required `Run changed Lean fast check` step **completed / SUCCESS**.
- Decoded log: `Build completed successfully (8564 jobs).`; two theorem axiom audits standard-three only; `sorryAx` absent, changed warning/error `0/0`.
- Independent receipt job `133939514285` completed/SUCCESS, emitted:

```text
[mcp-receipt] event=push exact_sha=ab2d7e56a7cabda5b65dd0e2b3e20e2732132e84 source_result=success run=44053827415 attempt=1
```

Result: **FORMAL_INTEGRATED_INDEPENDENT_PUSH_CERTIFIED**, limited to the two finite-volume original periodic Wilson positive-closure density theorems.

## Remaining mathematical obstructions

1. The explicit positive full-periodic marginal density yields an exact null-set comparison with boundary/open-half product Haar, but its **mutual absolute continuity as a typed measure theorem** is the next distinct Lean target.
2. Establish an exact measurable temporal-gauge pushforward into the ANA spatial half-path law, retaining the primary and antipodal boundary gauges and nontrivial terminal residual, and distinguishing `Z_full` from `Z_half`. Do not assert measure equality without this comparison.
3. Carry the unchanged original time-one Wilson cylinder into a typed OS positive-time observable algebra and establish its true completed OS boundary moment and physical Wilson one-slab intertwining. The AMR identity semigroup is not the nonidentity physical Wilson transfer by assumption.
4. No positive volume-uniform spectral-gap bound nor continuum 4D Yang–Mills mass gap follows from this finite-density identity.

This PR is documentation-only; **do not run Strict Lean** on the record or on the exact main mirror.
