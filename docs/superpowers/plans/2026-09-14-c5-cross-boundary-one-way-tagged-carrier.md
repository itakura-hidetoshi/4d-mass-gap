# C5 Cross-Boundary One-Way Tagged Carrier Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Package the already-proved C5 right-boundary-source to left-boundary-target influence as a `FiniteNonnegativeInfluenceKernelData` on a disjoint `Sum` index, preserving one-way semantics and proving the left-target row contracts with the existing scalar coefficient.

**Architecture:** Use `Sum Link Link` as the global index, with `Sum.inl` for left targets and `Sum.inr` for right sources. Only the `(Sum.inl fiber, Sum.inr source)` block is populated by the existing C5 cross-boundary bounded-test majorant; every other block is zero because it lies outside this one-way carrier, not because reverse physical influence has been proved to vanish.

**Tech Stack:** Lean 4, Mathlib, existing MGAP4D finite influence-kernel abstractions, GitHub Actions `PR Lean Fast Check`.

**Spec:** `docs/superpowers/specs/2026-09-14-c5-cross-boundary-one-way-tagged-carrier-design.md`

## Global Constraints

- Canonical base SHA: `ba063aec4cd8f17383c6f5b347ebb334e3886061`.
- Authoritative theorem-carrier branch: `formal/real-hilbert-uniform-coercive-strong-limit`.
- GitHub/repository operations use the GitHub connector only.
- No new physical assumptions.
- Do not infer or claim reverse left-source to right-target influence.
- Do not introduce distance decay or spatial-volume factors.
- Preserve `Sum.inl = left target`, `Sum.inr = right source` semantics.
- No `sorry`, `admit`, new `axiom`, heartbeat increase, or theorem weakening.

---

### Task 1: Define the tagged one-way influence and prove nonnegativity

**Files:**
- Create: `MGAP4D/MathlibAnalytic/PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceCrossBoundaryOneWayTaggedCarrier.lean`

**Interfaces:**
- Consumes: `periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBoundedTestMajorant` and the existing scalar contraction theorem unit.
- Produces: `periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTaggedInfluence` and its nonnegativity theorem.

- [ ] **Step 1: Write the failing theorem**

Define the tagged influence by pattern matching and intentionally prove nonnegativity with `rfl`:

```lean
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTaggedInfluence
    (H : ℕ) (beta : ℝ) :
    Sum (PeriodicHypercubicEvenSpatialSliceLink H)
        (PeriodicHypercubicEvenSpatialSliceLink H) →
    Sum (PeriodicHypercubicEvenSpatialSliceLink H)
        (PeriodicHypercubicEvenSpatialSliceLink H) → ℝ
  | Sum.inl fiber, Sum.inr source =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBoundedTestMajorant
        beta fiber source
  | _, _ => 0

theorem ..._nonneg
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (target source : Sum ... ...) :
    0 ≤ ...OneWayTaggedInfluence H beta target source := by
  rfl
```

- [ ] **Step 2: Run CI to verify RED**

Create a Draft PR to `formal/real-hilbert-uniform-coercive-strong-limit` and require `PR Lean Fast Check` to fail at the nonnegativity theorem, not during checkout or static audit.

- [ ] **Step 3: Prove nonnegativity by cases**

Case-split on `target` and `source`. Three blocks close by `simp`; the `Sum.inl fiber, Sum.inr source` block uses the existing bounded-test-majorant nonnegativity theorem or unfolds the majorant and uses coefficient nonnegativity if that is the actual available API.

- [ ] **Step 4: Run CI to verify GREEN**

Require exact-head `PR Lean Fast Check = completed / success`.

### Task 2: Package the tagged function as `FiniteNonnegativeInfluenceKernelData`

**Files:**
- Modify: `MGAP4D/MathlibAnalytic/PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceCrossBoundaryOneWayTaggedCarrier.lean`

**Interfaces:**
- Consumes: Task 1 tagged influence and nonnegativity.
- Produces: `...OneWayTaggedKernelData` with structural diagonal zero.

- [ ] **Step 1: Write a failing carrier proof**

Attempt the diagonal proof with `rfl` on an arbitrary tagged index so CI demonstrates that the structural case split is required.

- [ ] **Step 2: Verify RED**

Require Lean failure at the diagonal-zero proof.

- [ ] **Step 3: Implement the carrier**

```lean
noncomputable def ...OneWayTaggedKernelData
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) :
    FiniteNonnegativeInfluenceKernelData
      (Sum (PeriodicHypercubicEvenSpatialSliceLink H)
           (PeriodicHypercubicEvenSpatialSliceLink H)) :=
  { influence := ...OneWayTaggedInfluence H beta
    influence_nonneg := ..._nonneg H beta hbeta
    influence_diagonal_zero := by
      intro e
      cases e <;> rfl }
```

The diagonal proof must use only tag structure and must not invoke any physical vanishing claim.

- [ ] **Step 4: Verify GREEN**

Require exact-head CI success.

### Task 3: Prove exact block semantics

**Files:**
- Modify: same Lean file.

**Interfaces:**
- Produces four explicit block theorems.

- [ ] **Step 1: Prove the populated block**

```lean
theorem ..._leftTarget_rightSource
    (fiber source : PeriodicHypercubicEvenSpatialSliceLink H) :
    (...OneWayTaggedKernelData H beta hbeta).influence
      (Sum.inl fiber) (Sum.inr source) =
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBoundedTestMajorant
      beta fiber source := by
  rfl
```

- [ ] **Step 2: Prove the three zero blocks**

Prove left-left, right-left, and right-right blocks equal zero by `rfl`/`simp`. Docstrings must state that these zeros encode the scope of the one-way carrier only.

- [ ] **Step 3: Verify CI**

Require exact-head success.

### Task 4: Prove the left-target row sum equals the existing scalar coefficient

**Files:**
- Modify: same Lean file.

**Interfaces:**
- Consumes: `finiteInfluenceKernelRowSum`, the exact block theorems, and the existing C5 row/scalar theorem.
- Produces: exact tagged row identity with no volume factor.

- [ ] **Step 1: Write a RED row theorem with `rfl`**

Target:

```lean
finiteInfluenceKernelRowSum
  (...OneWayTaggedKernelData H beta hbeta)
  (Sum.inl fiber)
=
periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryContractionCoefficient beta
```

- [ ] **Step 2: Verify RED**

Require failure at finite-sum reduction.

- [ ] **Step 3: Prove exact row identity**

Reduce the `Sum`-indexed finite sum into the left and right copies. The left-source block is zero; the right-source block is exactly the existing cross-boundary majorant row. Reuse the existing theorem that its finite source sum equals the scalar coefficient rather than re-proving coefficient algebra.

- [ ] **Step 4: Verify GREEN**

Require exact-head CI success.

### Task 5: Prove strict small-coupling row contraction

**Files:**
- Modify: same Lean file.

**Interfaces:**
- Consumes: Task 4 row identity and `...CrossBoundaryContractionCoefficient_lt_one_of_beta_lt`.
- Produces: tagged left-target row `< 1` theorem.

- [ ] **Step 1: Prove strict row contraction**

```lean
theorem ..._leftTarget_rowSum_lt_one_of_beta_lt
    (H : ℕ) (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hBetaLt : beta < ...CrossBoundaryBetaThreshold)
    (fiber : PeriodicHypercubicEvenSpatialSliceLink H) :
    finiteInfluenceKernelRowSum
      (...OneWayTaggedKernelData H beta hbeta)
      (Sum.inl fiber) < 1 := by
  rw [..._leftTarget_rowSum_eq_coefficient]
  exact ...CrossBoundaryContractionCoefficient_lt_one_of_beta_lt beta hBetaLt
```

- [ ] **Step 2: Verify final exact head**

Require `PR Lean Fast Check` completed/success and inspect forbidden-token/static-audit output.

- [ ] **Step 3: Review the PR diff**

Confirm only the spec, plan, and focused Lean file changed; no earlier theorem-carrier files or physical assumptions were modified.

- [ ] **Step 4: Merge by exact head SHA**

Mark Ready only after final GREEN. Merge with `expected_head_sha`, then re-read the authoritative branch pointer and record the new canonical merge SHA, tree SHA, and parents.
