# P4-Q2-PZ37ANC — original periodic Wilson positive-closure time-one nonzero cylinder

Date: 2026-11-17 JST. Canonical theorem branch: `formal/real-hilbert-uniform-coercive-strong-limit`. Lean `v4.30.0-rc2`; mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`. Rules: append-only, tighten-only, overwrite-forbidden, same-root, GitHub MCP; docs-only changes do not rerun Strict Lean.

## Certified mathematical scope

Let `H : ℕ`, `beta : ℝ` with `0 ≤ beta`, and the genuine nontrivial `SU(2)` carrier. Denote the normalized full-periodic original Wilson Gibbs probability by `μ_full`, its shared boundary/positive-open-half marginal by `μ_plus`, and unchanged boundary/open-half product Haar by `λ_plus`.

ANB #6852 certified `μ_plus ≪ λ_plus` and `λ_plus ≪ μ_plus`, hence equality of all null sets. ANA/AMY, separately, certified nonzero time-one two-mode Wilson cylinders on the genuine spatial positive-half path under the original temporal-gauge Wilson law, with the same specific finite physical top-eigenspace-orthogonal combination.

ANC constructs the **exact same pointwise time-one cylinder**, without changing its time index, coefficients, holonomy or Wilson class functions, on the literal periodic positive-closure carrier `BoundaryConfiguration H 2 × OpenHalfConfiguration H 2` by applying the already certified measurable positive-closure transfer coordinate equivalence and spatial-path projection. The existing product Haar transport and `MeasureTheory.measurePreserving_fst` prove that this projection sends `λ_plus` to original spatial path Haar. AMY's nonzero cylinder under original temporal-gauge weighted law and its absolute continuity with respect to spatial path Haar give nonzero a.e. on `λ_plus`. ANB's direction `λ_plus ≪ μ_plus` transports that nonzero result to the **true full-periodic interacting Gibbs marginal**.

### Five exactly audited Lean theorems

1. `p4Q2PZ37ANC_timeOneTwoModePositiveClosureObservable_measurable`: the typed original cylinder is measurable on actual positive-closure coordinates.
2. `p4Q2PZ37ANC_positiveClosureSpatialPath_measurePreserving`: closure product Haar maps to the unchanged original positive-half spatial-path Haar.
3. `p4Q2PZ37ANC_exists_nonzero_positiveClosureHaar_timeOneCylinder`: an actual two-mode physical top-orthogonal time-one witness has nonzero Haar-a.e. class on the closure.
4. `p4Q2PZ37ANC_fullPeriodicPositiveClosure_ae_zero_iff_productHaar`: any real cylinder is zero a.e. for genuine periodic marginal iff zero a.e. for closure product Haar.
5. `p4Q2PZ37ANC_exists_nonzero_truePeriodicGibbsPositiveClosureTimeOneCylinder`: an actual top-orthogonal two-mode time-one witness is **not** zero a.e. under genuine full-periodic Gibbs positive-closure marginal.

One additive file: `MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonFullPeriodicPositiveClosureTimeOneNonzeroV5_PZ37ANC.lean` (221 lines, five theorem `#print axioms` audits). Neither any original Wilson model/measure/partition function nor any existing theorem source or pin was altered.

## Append-only first failure and repair evidence

- Initial candidate HEAD `038d70c583f9d48d0f991699b9f9f30c45fd1233`, file blob `fa27e8ce72ec23afda851ad3351e780d82945977`; [initial CI #44060383992](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/44060383992) completed FAILURE, mandatory Lean job `133960438934`.
- Actual elaboration log: missing normalization for `PeriodicHypercubicEvenSideLength` / `periodicHypercubicEvenPositiveHalfCylinderSlabCount` in local `NeZero` (line 34); the reserved Lean token `λ` incorrectly used as `let λ := ...` (line 132), with secondary unsolved theorem goal at line 117. Erroneous `sorryAx` audit outputs were **failed elaboration artifacts**, not verified theorems.
- Same PR #6855 repaired both without weakening hypotheses: explicitly unfold the positive-half slab count in `simp`; rename the reserved token to `haarClosure`. Corrected exact-source HEAD `5bb3457db452975c0b0c13f7955615714cc35d04`, blob `640249284ad699a799a633ae2ede0cdf78c37061`.
- Failure and corrected success are kept distinct for future CodeAI/MemoryOS classification, not rewritten into an earlier green state.

## Exact-source Lean/axiom/receipt audit

- [Theorem PR #6855](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6855): MERGED.
- [Exact-source CI #44061158470](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/44061158470): event `pull_request`, exact corrected source `5bb3457db452975c0b0c13f7955615714cc35d04`, attempt 1, workflow completed/SUCCESS; required Lean job `133963089814` and `Run changed Lean fast check` step completed/SUCCESS.
- Exact Lean log: `Build completed successfully (8858 jobs)`. Five/five `#print axioms` outputs contain only `propext`, `Classical.choice`, `Quot.sound`. No `sorryAx`, changed ANC source warning/error 0/0.
- Independent source receipt job `133964402405` completed/SUCCESS and emitted:

```text
[mcp-receipt] event=pull_request exact_sha=5bb3457db452975c0b0c13f7955615714cc35d04 source_result=success run=44061158470 attempt=1
```

## Source/test-merge/Formal identity and independent push

- Original base Formal HEAD `55924d797ae1371c4ac0667b21f23135a833a7d9`.
- Test-merge SHA `7f819c68c9202a2556e63fac01c9b57b7731f9b4` has exact parents (base, corrected source). Source tree, test-merge tree and **actual Formal squash tree** are identical: `ff821b2f3d4d772f48a2377c2be93194be1db874`.
- Formal theorem integrated HEAD: `aee4012c1735327385859c093663cc76fcae7471`. Squash merger explicitly checked corrected source SHA.
- Independent [canonical Formal push #44061714947](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/44061714947): `event=push`, exact integrated HEAD `aee4012c1735327385859c093663cc76fcae7471`, attempt 1; workflow, mandatory Lean job `133964990156`, `Run changed Lean fast check` step all completed/SUCCESS.
- Independent push Lean log `Build completed successfully (8858 jobs)`, five theorem audits standard three axioms only, no `sorryAx`, ANC changed warning/error 0/0.
- Separate exact-push receipt job `133966550305` completed/SUCCESS:

```text
[mcp-receipt] event=push exact_sha=aee4012c1735327385859c093663cc76fcae7471 source_result=success run=44061714947 attempt=1
```

**Status: FORMAL_INTEGRATED_INDEPENDENT_PUSH_CERTIFIED**, restricted precisely to these finite-volume true-original-periodic-Gibbs positive-closure time-one nonzero results.

## Open independent mathematical obstacles (NO_DATA retained)

1. The original full-periodic Gibbs positive-closure measure `μ_plus` is *not identified* with ANA's separately normalized temporal-gauge positive-half measure. Equality would require true compatible boundary/gauge and normalization evidence; only null-set transport is used here.
2. No real `Lp ℝ 2 μ_plus` vector for this true periodic cylinder is constructed in ANC yet (though boundedness and measurability suggest the next direct finite-volume unit).
3. No identification with the completed reflection-positive OS physical Hilbert quotient, no explicit genuine Wilson physical one-slab/completed OS `C.translate` intertwining, and no volume-uniform contraction/gap lower bound.
4. No continuum four-dimensional Yang–Mills field reconstruction or continuum mass-gap proof.

This record is documentation-only. Strict Lean is not rerun for its Formal integration or main mirror.
