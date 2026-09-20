import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceResponseControlledRandomScanVariation
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumRemoteKernelSectionRestrictedRandomScanIterate
import Mathlib.Tactic

/-!
# Finite-step response-controlled random-scan recurrence

This file iterates the one-step response-controlled physical bounds without
reintroducing the coarse all-to-all left-left tagged carrier.

For a fixed distinguished target and a uniform fixed-right response profile
`R`, the physical left variation evolves by the configuration-independent
kernel from the preceding units:

  v_(n+1) = Q_R v_n.

The represented right-boundary discrepancy is tracked separately.  One scan
step transforms a current discrepancy `d` and left variation `v` into the
uniform average of

  d + beta_cross(fiber, source) * v(fiber).

Thus the right-source recurrence only uses the proved cross-boundary forcing;
the volume-growing coarse left-left coefficient never enters.

The main theorem proves simultaneously that every physical random-scan
observable has left variation bounded by `v_n`, and that two boundary-value
orbits differ pointwise by the accumulated source discrepancy.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory BigOperators

noncomputable section

local instance responseControlledRandomScanFiniteStepSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance responseControlledRandomScanFiniteStepSpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance responseControlledRandomScanFiniteStepSpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance responseControlledRandomScanFiniteStepSpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance responseControlledRandomScanFiniteStepSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance responseControlledRandomScanFiniteStepSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Iterated response-controlled physical left-variation profile. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetResponseControlledRandomScanVariationIterate
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (distinguishedTarget : PeriodicHypercubicEvenSpatialSliceLink H)
    (R :
      PeriodicHypercubicEvenSpatialSliceLink H →
        PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hRNonneg : ∀ target source, 0 ≤ R target source)
    (variation : PeriodicHypercubicEvenSpatialSliceLink H → ℝ) :
    ℕ → PeriodicHypercubicEvenSpatialSliceLink H → ℝ
  | 0 => variation
  | n + 1 =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetResponseControlledRandomScanUpdatedVariation
        H beta hbeta distinguishedTarget R hRNonneg
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetResponseControlledRandomScanVariationIterate
          H beta hbeta distinguishedTarget R hRNonneg variation n)

@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetResponseControlledRandomScanVariationIterate_zero
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (distinguishedTarget : PeriodicHypercubicEvenSpatialSliceLink H)
    (R :
      PeriodicHypercubicEvenSpatialSliceLink H →
        PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hRNonneg : ∀ target source, 0 ≤ R target source)
    (variation : PeriodicHypercubicEvenSpatialSliceLink H → ℝ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetResponseControlledRandomScanVariationIterate
        H beta hbeta distinguishedTarget R hRNonneg variation 0 =
      variation := by
  rfl

@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetResponseControlledRandomScanVariationIterate_succ
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (distinguishedTarget : PeriodicHypercubicEvenSpatialSliceLink H)
    (R :
      PeriodicHypercubicEvenSpatialSliceLink H →
        PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hRNonneg : ∀ target source, 0 ≤ R target source)
    (variation : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (n : ℕ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetResponseControlledRandomScanVariationIterate
        H beta hbeta distinguishedTarget R hRNonneg variation (n + 1) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetResponseControlledRandomScanUpdatedVariation
        H beta hbeta distinguishedTarget R hRNonneg
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetResponseControlledRandomScanVariationIterate
          H beta hbeta distinguishedTarget R hRNonneg variation n) := by
  rfl

theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetResponseControlledRandomScanVariationIterate_nonneg
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (distinguishedTarget : PeriodicHypercubicEvenSpatialSliceLink H)
    (R :
      PeriodicHypercubicEvenSpatialSliceLink H →
        PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hRNonneg : ∀ target source, 0 ≤ R target source)
    (variation : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hVariationNonneg : ∀ source, 0 ≤ variation source)
    (n : ℕ)
    (source : PeriodicHypercubicEvenSpatialSliceLink H) :
    0 ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetResponseControlledRandomScanVariationIterate
        H beta hbeta distinguishedTarget R hRNonneg variation n source := by
  induction n generalizing source with
  | zero =>
      simpa using hVariationNonneg source
  | succ n ih =>
      rw [
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetResponseControlledRandomScanVariationIterate_succ]
      exact
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetResponseControlledRandomScanUpdatedVariation_nonneg
          H beta hbeta distinguishedTarget R hRNonneg
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetResponseControlledRandomScanVariationIterate
            H beta hbeta distinguishedTarget R hRNonneg variation n)
          (fun e => ih e) source

/-- One right-source discrepancy step, kept separate from the left kernel. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryRandomScanSourceDiscrepancyStep
    (H : ℕ)
    (beta : ℝ)
    (source : PeriodicHypercubicEvenSpatialSliceLink H)
    (variation : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (discrepancy : ℝ) : ℝ :=
  (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ)⁻¹ *
    ∑ fiber : PeriodicHypercubicEvenSpatialSliceLink H,
      (discrepancy +
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBoundedTestMajorant
          beta fiber source * variation fiber)

/-- Accumulated right-source discrepancy along the response-controlled left
variation orbit. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetResponseControlledAccumulatedSourceDiscrepancy
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (distinguishedTarget source : PeriodicHypercubicEvenSpatialSliceLink H)
    (R :
      PeriodicHypercubicEvenSpatialSliceLink H →
        PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hRNonneg : ∀ target source, 0 ≤ R target source)
    (variation : PeriodicHypercubicEvenSpatialSliceLink H → ℝ) :
    ℕ → ℝ
  | 0 => 0
  | n + 1 =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryRandomScanSourceDiscrepancyStep
        H beta source
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetResponseControlledRandomScanVariationIterate
          H beta hbeta distinguishedTarget R hRNonneg variation n)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetResponseControlledAccumulatedSourceDiscrepancy
          H beta hbeta distinguishedTarget source R hRNonneg variation n)

@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetResponseControlledAccumulatedSourceDiscrepancy_zero
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (distinguishedTarget source : PeriodicHypercubicEvenSpatialSliceLink H)
    (R :
      PeriodicHypercubicEvenSpatialSliceLink H →
        PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hRNonneg : ∀ target source, 0 ≤ R target source)
    (variation : PeriodicHypercubicEvenSpatialSliceLink H → ℝ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetResponseControlledAccumulatedSourceDiscrepancy
        H beta hbeta distinguishedTarget source R hRNonneg variation 0 = 0 := by
  rfl

@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetResponseControlledAccumulatedSourceDiscrepancy_succ
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (distinguishedTarget source : PeriodicHypercubicEvenSpatialSliceLink H)
    (R :
      PeriodicHypercubicEvenSpatialSliceLink H →
        PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hRNonneg : ∀ target source, 0 ≤ R target source)
    (variation : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (n : ℕ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetResponseControlledAccumulatedSourceDiscrepancy
        H beta hbeta distinguishedTarget source R hRNonneg variation (n + 1) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryRandomScanSourceDiscrepancyStep
        H beta source
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetResponseControlledRandomScanVariationIterate
          H beta hbeta distinguishedTarget R hRNonneg variation n)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetResponseControlledAccumulatedSourceDiscrepancy
          H beta hbeta distinguishedTarget source R hRNonneg variation n) := by
  rfl

theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryRandomScanSourceDiscrepancyStep_nonneg
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (source : PeriodicHypercubicEvenSpatialSliceLink H)
    (variation : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hVariationNonneg : ∀ fiber, 0 ≤ variation fiber)
    (discrepancy : ℝ)
    (hDiscrepancy : 0 ≤ discrepancy) :
    0 ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryRandomScanSourceDiscrepancyStep
        H beta source variation discrepancy := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryRandomScanSourceDiscrepancyStep
  apply mul_nonneg
  · exact inv_nonneg.mpr (Nat.cast_nonneg _)
  · apply Finset.sum_nonneg
    intro fiber _hFiber
    have hMajorant :
        0 ≤
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBoundedTestMajorant
            beta fiber source := by
      have hTagged :=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTaggedInfluence_nonneg
          H beta hbeta (Sum.inl fiber) (Sum.inr source)
      simpa [
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTaggedInfluence] using hTagged
    exact add_nonneg hDiscrepancy
      (mul_nonneg hMajorant (hVariationNonneg fiber))

theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetResponseControlledAccumulatedSourceDiscrepancy_nonneg
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (distinguishedTarget source : PeriodicHypercubicEvenSpatialSliceLink H)
    (R :
      PeriodicHypercubicEvenSpatialSliceLink H →
        PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hRNonneg : ∀ target source, 0 ≤ R target source)
    (variation : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hVariationNonneg : ∀ fiber, 0 ≤ variation fiber)
    (n : ℕ) :
    0 ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetResponseControlledAccumulatedSourceDiscrepancy
        H beta hbeta distinguishedTarget source R hRNonneg variation n := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetResponseControlledAccumulatedSourceDiscrepancy_succ]
      exact
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryRandomScanSourceDiscrepancyStep_nonneg
          H beta hbeta source
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetResponseControlledRandomScanVariationIterate
            H beta hbeta distinguishedTarget R hRNonneg variation n)
          (fun fiber =>
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetResponseControlledRandomScanVariationIterate_nonneg
              H beta hbeta distinguishedTarget R hRNonneg variation hVariationNonneg n fiber)
          _ ih

/-- Every finite physical random-scan iterate has left-fiber variation bounded
by the response-controlled orbit `v_n`. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate_fiberVariation_le_responseControlled
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (R :
      PeriodicHypercubicEvenSpatialSliceLink H →
        PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hRNonneg : ∀ target source, 0 ≤ R target source)
    (hResponse :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioUniformResponseProfileBound
        H N hN beta hbeta R)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (g₂ k : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (F : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ)
    (hF : StronglyMeasurable F)
    (variation : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hVariationNonneg : ∀ e, 0 ≤ variation e)
    (hVariation :
      ∀ (e : PeriodicHypercubicEvenSpatialSliceLink H)
        (C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
        (u v : Matrix.specialUnitaryGroup (Fin N) ℂ),
        |F (Function.update C e u) - F (Function.update C e v)| ≤ variation e)
    (n : ℕ)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (u v : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    |periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate
        H N hN beta hbeta B target source g₂ k F n (Function.update A e u) -
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate
        H N hN beta hbeta B target source g₂ k F n (Function.update A e v)| ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetResponseControlledRandomScanVariationIterate
        H beta hbeta target R hRNonneg variation n e := by
  induction n generalizing e A u v with
  | zero =>
      simpa using hVariation e A u v
  | succ n ih =>
      rw [
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate_succ,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetResponseControlledRandomScanVariationIterate_succ]
      exact
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectation_fiberVariation_le_responseControlled
          H N hN beta hbeta R hRNonneg hResponse
          B target source g₂ k
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate
            H N hN beta hbeta B target source g₂ k F n)
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate_stronglyMeasurable
            H N hN beta hbeta B target source g₂ k F hF n)
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetResponseControlledRandomScanVariationIterate
            H beta hbeta target R hRNonneg variation n)
          (fun background =>
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetResponseControlledRandomScanVariationIterate_nonneg
              H beta hbeta target R hRNonneg variation hVariationNonneg n background)
          (fun background C a b => ih C background a b)
          e A u v

/-- Two physical restricted random-scan orbits with distinct represented
right-boundary values differ pointwise by the accumulated source discrepancy.
The left orbit is propagated exclusively by the response-controlled physical
kernel; the augmented tagged carrier is used only as a proof device for the
right-source one-step affine identity. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate_boundarySource_difference_le_responseControlledAccumulated
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (R :
      PeriodicHypercubicEvenSpatialSliceLink H →
        PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hRNonneg : ∀ target source, 0 ≤ R target source)
    (hResponse :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioUniformResponseProfileBound
        H N hN beta hbeta R)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (g₂ k₁ k₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (F : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ)
    (hF : StronglyMeasurable F)
    (variation : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hVariationNonneg : ∀ e, 0 ≤ variation e)
    (hVariation :
      ∀ (e : PeriodicHypercubicEvenSpatialSliceLink H)
        (C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
        (u v : Matrix.specialUnitaryGroup (Fin N) ℂ),
        |F (Function.update C e u) - F (Function.update C e v)| ≤ variation e)
    (n : ℕ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    |periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate
        H N hN beta hbeta B target source g₂ k₁ F n A -
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate
        H N hN beta hbeta B target source g₂ k₂ F n A| ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetResponseControlledAccumulatedSourceDiscrepancy
        H beta hbeta target source R hRNonneg variation n := by
  induction n generalizing A with
  | zero =>
      simp
  | succ n ih =>
      let F₁ :=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate
          H N hN beta hbeta B target source g₂ k₁ F n
      let F₂ :=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate
          H N hN beta hbeta B target source g₂ k₂ F n
      let vN :=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetResponseControlledRandomScanVariationIterate
          H beta hbeta target R hRNonneg variation n
      let dN :=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetResponseControlledAccumulatedSourceDiscrepancy
          H beta hbeta target source R hRNonneg variation n
      let profile :
          Sum
            (PeriodicHypercubicEvenSpatialSliceLink H)
            (PeriodicHypercubicEvenSpatialSliceLink H) → ℝ :=
        fun x =>
          match x with
          | Sum.inl e => vN e
          | Sum.inr _ => dN
      have hF₁ : StronglyMeasurable F₁ := by
        dsimp [F₁]
        exact
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate_stronglyMeasurable
            H N hN beta hbeta B target source g₂ k₁ F hF n
      have hF₂ : StronglyMeasurable F₂ := by
        dsimp [F₂]
        exact
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate_stronglyMeasurable
            H N hN beta hbeta B target source g₂ k₂ F hF n
      have hVNNonneg : ∀ e, 0 ≤ vN e := by
        intro e
        dsimp [vN]
        exact
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetResponseControlledRandomScanVariationIterate_nonneg
            H beta hbeta target R hRNonneg variation hVariationNonneg n e
      have hDNNonneg : 0 ≤ dN := by
        dsimp [dN]
        exact
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetResponseControlledAccumulatedSourceDiscrepancy_nonneg
            H beta hbeta target source R hRNonneg variation hVariationNonneg n
      have hProfileNonneg : ∀ x, 0 ≤ profile x := by
        intro x
        cases x with
        | inl e => simpa [profile] using hVNNonneg e
        | inr e => simpa [profile] using hDNNonneg
      have hVariation₁ :
          ∀ (e : PeriodicHypercubicEvenSpatialSliceLink H)
            (C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
            (u v : Matrix.specialUnitaryGroup (Fin N) ℂ),
            |F₁ (Function.update C e u) - F₁ (Function.update C e v)| ≤
              profile (Sum.inl e) := by
        intro e C u v
        dsimp [F₁, profile, vN]
        exact
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate_fiberVariation_le_responseControlled
            H N hN beta hbeta R hRNonneg hResponse B target source g₂ k₁
            F hF variation hVariationNonneg hVariation n e C u v
      have hVariation₂ :
          ∀ (e : PeriodicHypercubicEvenSpatialSliceLink H)
            (C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
            (u v : Matrix.specialUnitaryGroup (Fin N) ℂ),
            |F₂ (Function.update C e u) - F₂ (Function.update C e v)| ≤
              profile (Sum.inl e) := by
        intro e C u v
        dsimp [F₂, profile, vN]
        exact
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate_fiberVariation_le_responseControlled
            H N hN beta hbeta R hRNonneg hResponse B target source g₂ k₂
            F hF variation hVariationNonneg hVariation n e C u v
      have hPoint : ∀ C, |F₁ C - F₂ C| ≤ profile (Sum.inr source) := by
        intro C
        dsimp [F₁, F₂, profile, dN]
        exact ih C
      have hAffine :=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectation_affineTransport_le
          H N hN beta hbeta B target source g₂ k₁ k₂ A
          F₁ F₂ hF₁ hF₂ profile hProfileNonneg
          hVariation₁ hVariation₂ hPoint
      rw [
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate_succ,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate_succ,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetResponseControlledAccumulatedSourceDiscrepancy_succ]
      simpa [
        F₁, F₂, vN, dN, profile,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryRandomScanSourceDiscrepancyStep,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanUpdatedVariation,
        finiteInfluenceKernelRestrictedTargetRandomScanUpdatedVariation,
        finiteInfluenceKernelUpdatedVariation,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedKernel_left_right] using hAffine

end

end MathlibAnalytic
end MGAP4D
