# Continuous-vacuum Ground-state One-link Normalized Minorization Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Normalize the exact complete continuous-vacuum ground-state one-link weight and prove sharp `exp (±16 * beta)` Haar density/measure comparison.

**Architecture:** Build directly on the complete pairwise Harnack theorem merged in PR #3894. First package the complete weight against normalized compact Haar, then integrate pairwise Harnack to control the normalization denominator, and finally use Mathlib `ENNReal` division and `withDensity` order lemmas to obtain normalized density and measure bounds without an `R^2` loss.

**Tech Stack:** Lean 4, mathlib pinned by repository `lake-manifest.json`, existing MGAP4D Doob-weighted measure API, GitHub Actions `PR Lean Fast Check`.

**Spec:** `docs/superpowers/specs/2026-09-12-continuous-vacuum-ground-state-one-link-normalized-minorization-design.md`

## Global Constraints

- Exact canonical base: `70c3807698e5353eb58ef90c31be491886cf54ff`.
- Do not weaken assumptions.
- Do not evaluate quotient representatives pointwise.
- Do not introduce global Poincare, spectral-gap, continuum-gap, or RCD claims.
- Preserve the sharp single Harnack factor `R = ENNReal.ofReal (Real.exp (16 * beta))`; do not replace it by an anchored `m/M` argument with `R^2` loss.
- During CI, keep write-freeze; after a failure inspect only the first genuine Lean error.
- Completion requires exact-head `PR Lean Fast Check = completed / success`.

---

### Task 1: RED compile probe for the intended public API

**Files:**
- Create temporarily: `MGAP4D/MathlibAnalytic/PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumGroundStateOneLinkNormalizedMinorizationTest.lean`

**Interfaces:**
- Consumes: PR #3894 complete one-link weight and pairwise Harnack.
- Produces: a compile-level specification requiring the new normalized-density and normalized-measure lower bounds.

- [ ] **Step 1: Write the failing compile probe**

```lean
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumGroundStateOneLinkNormalizedMinorization

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped ENNReal

noncomputable section

example
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (left right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    (ENNReal.ofReal (Real.exp (16 * beta)))⁻¹ ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkNormalizedFiberDensity
        H N hN beta hbeta left right target g := by
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkNormalizedFiberDensity_lower_bound
      H N hN beta hbeta left right target g

end
end MathlibAnalytic
end MGAP4D
```

- [ ] **Step 2: Open a Draft PR and run the changed-Lean check**

Expected: FAIL because the imported production module/theorem does not yet exist. Confirm the first genuine Lean error is the missing module/API, not an unrelated baseline failure.

### Task 2: Implement normalization denominator control

**Files:**
- Create: `MGAP4D/MathlibAnalytic/PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumGroundStateOneLinkNormalizedMinorization.lean`

**Interfaces:**
- Consumes: `periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkFiberWeight_pos` and `..._pairwise_harnack` from PR #3894; normalized compact Haar; `doobWeightMass`, `doobWeightedDensity`, and `doobWeightedMeasure`.
- Produces: complete-weight normalization mass, normalized density, normalized fiber measure, AEMeasurability, denominator upper/lower bounds, positive finite mass.

- [ ] **Step 1: Define `mu`, weight wrappers, mass, density, and measure using the existing generic Doob API.**
- [ ] **Step 2: Prove the complete weight is continuous/AEMeasurable in the target `SU(N)` coordinate.**
- [ ] **Step 3: For fixed `h`, integrate `w g <= R * w h` to prove `Z <= R * w h`.**
- [ ] **Step 4: Integrate `w h <= R * w g` to prove `w h <= R * Z`.**
- [ ] **Step 5: Use pointwise positivity/finiteness plus Steps 3–4 to prove `0 < Z` and `Z < ∞`.**
- [ ] **Step 6: Run `PR Lean Fast Check`; if it fails, inspect only the first genuine Lean error and minimally adjust the proof.**

### Task 3: Prove sharp normalized density and measure comparison

**Files:**
- Modify: `MGAP4D/MathlibAnalytic/PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumGroundStateOneLinkNormalizedMinorization.lean`

**Interfaces:**
- Consumes: Task 2 denominator inequalities and mass nonzero/non-top receipts.
- Produces: pointwise `R⁻¹ <= rho g <= R`, probability instance/receipt, and measure inequalities `R⁻¹ • Haar <= normalizedFiber <= R • Haar`.

- [ ] **Step 1: Use `ENNReal.div_le_iff` and exact mass bounds to prove the density lower bound `R⁻¹ <= w g / Z`.**
- [ ] **Step 2: Use `ENNReal.div_le_iff` and exact mass bounds to prove `w g / Z <= R`.**
- [ ] **Step 3: Use `doobWeightedMeasure_measure_univ` or the existing bounded normalization theorem to prove the normalized fiber is a probability measure.**
- [ ] **Step 4: Lift pointwise density bounds through `withDensity_mono` to the measure minorization/majorization statements.**
- [ ] **Step 5: Run exact-head `PR Lean Fast Check` and require terminal success.**

### Task 4: Remove temporary planning/probe artifacts and final verification

**Files:**
- Delete: `MGAP4D/MathlibAnalytic/PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumGroundStateOneLinkNormalizedMinorizationTest.lean`
- Delete: `docs/superpowers/specs/2026-09-12-continuous-vacuum-ground-state-one-link-normalized-minorization-design.md`
- Delete: `docs/superpowers/plans/2026-09-12-continuous-vacuum-ground-state-one-link-normalized-minorization.md`

**Interfaces:**
- Produces: a one-file theorem PR with no planning/probe artifacts in the final diff.

- [ ] **Step 1: Delete the temporary compile probe only after it has demonstrated RED and the implementation has demonstrated GREEN.**
- [ ] **Step 2: Delete planning artifacts so the final PR contains only the mathematical Lean unit.**
- [ ] **Step 3: Compare exact base to head and confirm no unrelated files changed.**
- [ ] **Step 4: Run/fresh-check exact-head PR CI after the cleanup commit.**
- [ ] **Step 5: Keep Draft until exact-head CI is terminal success; only then consider ready/merge according to repository policy.**
