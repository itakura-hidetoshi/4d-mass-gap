import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumRemoteKernelSectionRestrictedRandomScanIterate
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory BigOperators

noncomputable section

local instance referenceDistinctFiberRestrictedRandomScanIterateSpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance referenceDistinctFiberRestrictedRandomScanIterateSpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance referenceDistinctFiberRestrictedRandomScanIterateSpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance referenceDistinctFiberRestrictedRandomScanIterateSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance referenceDistinctFiberRestrictedRandomScanIterateSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance referenceDistinctFiberRestrictedRandomScanIterateSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/- The one-step strong-measurability theorem is provided by
`PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumRemoteKernelSectionRestrictedRandomScanIterate`.
This compatibility layer keeps the affine two-boundary transport theorem
without redeclaring the shared public API. -/
/-- Affine one-step transport: if two input observables already differ by the
right-source component of a nonnegative tagged profile, and both have left-fiber
variation controlled by that profile, then updating them with boundary values
`k₁` and `k₂` is dominated by one restricted tagged random-scan update. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectation_affineTransport_le
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (g₂ k₁ k₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (F₁ F₂ : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ)
    (hF₁ : StronglyMeasurable F₁)
    (hF₂ : StronglyMeasurable F₂)
    (profile : Sum
      (PeriodicHypercubicEvenSpatialSliceLink H)
      (PeriodicHypercubicEvenSpatialSliceLink H) → ℝ)
    (hProfileNonneg : ∀ x, 0 ≤ profile x)
    (hVariation₁ :
      ∀ (e : PeriodicHypercubicEvenSpatialSliceLink H)
        (C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
        (u v : Matrix.specialUnitaryGroup (Fin N) ℂ),
        |F₁ (Function.update C e u) - F₁ (Function.update C e v)| ≤
          profile (Sum.inl e))
    (hVariation₂ :
      ∀ (e : PeriodicHypercubicEvenSpatialSliceLink H)
        (C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
        (u v : Matrix.specialUnitaryGroup (Fin N) ℂ),
        |F₂ (Function.update C e u) - F₂ (Function.update C e v)| ≤
          profile (Sum.inl e))
    (hPoint : ∀ C, |F₁ C - F₂ C| ≤ profile (Sum.inr source)) :
    |periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectation
        H N hN beta hbeta B target source g₂ k₁ A F₁ -
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectation
        H N hN beta hbeta B target source g₂ k₂ A F₂| ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanUpdatedVariation
        H beta hbeta profile (Sum.inr source) := by
  let physicalVariation : PeriodicHypercubicEvenSpatialSliceLink H → ℝ :=
    fun background => profile (Sum.inl background)
  have hPhysicalNonneg : ∀ background, 0 ≤ physicalVariation background := by
    intro background
    exact hProfileNonneg (Sum.inl background)
  have hInvNonneg :
      0 ≤ (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ)⁻¹ :=
    inv_nonneg.mpr (Nat.cast_nonneg _)
  have hTarget (fiber : PeriodicHypercubicEvenSpatialSliceLink H) :
      |periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberDeterministicScheduleExpectation
          H N hN beta hbeta B target source g₂ [fiber] k₁ A F₁ -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberDeterministicScheduleExpectation
          H N hN beta hbeta B target source g₂ [fiber] k₂ A F₂| ≤
        finiteInfluenceKernelUpdatedVariation
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedKernel
            H beta hbeta)
          profile (Sum.inl fiber) (Sum.inr source) := by
    have hDirectRaw :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberDeterministicScheduleExpectation_transport_le
        H N hN beta hbeta B target source g₂ k₁ k₂ A F₁ hF₁
        physicalVariation hPhysicalNonneg hVariation₁ [fiber]
    rw [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedDeterministicScheduleVariation_cons_right] at hDirectRaw
    have hDirect :
        |periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberDeterministicScheduleExpectation
            H N hN beta hbeta B target source g₂ [fiber] k₁ A F₁ -
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberDeterministicScheduleExpectation
            H N hN beta hbeta B target source g₂ [fiber] k₂ A F₁| ≤
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBoundedTestMajorant
              beta fiber source * profile (Sum.inl fiber) := by
      simpa [
        physicalVariation,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTaggedLeftVariation] using hDirectRaw
    let K₂ :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel
        H N hN beta hbeta B target source fiber k₂ g₂
    have hF₁Int : Integrable F₁ (K₂ A) := by
      dsimp [K₂]
      exact
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel_integrable_of_fiberVariation
          H N hN beta hbeta B target source fiber k₂ g₂ A F₁ hF₁
          (profile (Sum.inl fiber)) (hProfileNonneg (Sum.inl fiber))
          (hVariation₁ fiber A)
    have hF₂Int : Integrable F₂ (K₂ A) := by
      dsimp [K₂]
      exact
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel_integrable_of_fiberVariation
          H N hN beta hbeta B target source fiber k₂ g₂ A F₂ hF₂
          (profile (Sum.inl fiber)) (hProfileNonneg (Sum.inl fiber))
          (hVariation₂ fiber A)
    have hDiffInt : Integrable (fun C => F₁ C - F₂ C) (K₂ A) :=
      hF₁Int.sub hF₂Int
    have hAverage :
        |(∫ C, F₁ C ∂K₂ A) - (∫ C, F₂ C ∂K₂ A)| ≤
          profile (Sum.inr source) := by
      calc
        |(∫ C, F₁ C ∂K₂ A) - (∫ C, F₂ C ∂K₂ A)| =
            |∫ C, (F₁ C - F₂ C) ∂K₂ A| := by
          rw [integral_sub hF₁Int hF₂Int]
        _ = ‖∫ C, (F₁ C - F₂ C) ∂K₂ A‖ := by
          rw [Real.norm_eq_abs]
        _ ≤ ∫ C, ‖F₁ C - F₂ C‖ ∂K₂ A :=
          norm_integral_le_integral_norm _
        _ ≤ ∫ _C, profile (Sum.inr source) ∂K₂ A := by
          apply integral_mono_ae hDiffInt.norm
            (integrable_const (profile (Sum.inr source)))
          filter_upwards with C
          simpa [Real.norm_eq_abs] using hPoint C
        _ = profile (Sum.inr source) := by
          simp
    let x :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberDeterministicScheduleExpectation
        H N hN beta hbeta B target source g₂ [fiber] k₁ A F₁
    let y :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberDeterministicScheduleExpectation
        H N hN beta hbeta B target source g₂ [fiber] k₂ A F₁
    let z :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberDeterministicScheduleExpectation
        H N hN beta hbeta B target source g₂ [fiber] k₂ A F₂
    have hAverage' : |y - z| ≤ profile (Sum.inr source) := by
      simpa [x, y, z, K₂,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberDeterministicScheduleExpectation] using hAverage
    have hEq : x - z = (x - y) + (y - z) := by ring
    unfold finiteInfluenceKernelUpdatedVariation
    simp only [reduceCtorEq, if_false]
    rw [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedKernel_left_right]
    change |x - z| ≤ profile (Sum.inr source) +
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBoundedTestMajorant
        beta fiber source * profile (Sum.inl fiber)
    rw [hEq]
    calc
      |(x - y) + (y - z)| ≤ |x - y| + |y - z| := by
        simpa [Real.norm_eq_abs] using norm_add_le (x - y) (y - z)
      _ ≤
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBoundedTestMajorant
              beta fiber source * profile (Sum.inl fiber) +
            profile (Sum.inr source) := by
        exact add_le_add (by simpa [x, y] using hDirect) hAverage'
      _ = profile (Sum.inr source) +
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBoundedTestMajorant
            beta fiber source * profile (Sum.inl fiber) := by
        ring
  have hSum :
      |∑ fiber : PeriodicHypercubicEvenSpatialSliceLink H,
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberDeterministicScheduleExpectation
              H N hN beta hbeta B target source g₂ [fiber] k₁ A F₁ -
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberDeterministicScheduleExpectation
              H N hN beta hbeta B target source g₂ [fiber] k₂ A F₂)| ≤
        ∑ fiber : PeriodicHypercubicEvenSpatialSliceLink H,
          finiteInfluenceKernelUpdatedVariation
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedKernel
              H beta hbeta)
            profile (Sum.inl fiber) (Sum.inr source) := by
    calc
      |∑ fiber : PeriodicHypercubicEvenSpatialSliceLink H,
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberDeterministicScheduleExpectation
              H N hN beta hbeta B target source g₂ [fiber] k₁ A F₁ -
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberDeterministicScheduleExpectation
              H N hN beta hbeta B target source g₂ [fiber] k₂ A F₂)| ≤
        ∑ fiber : PeriodicHypercubicEvenSpatialSliceLink H,
          |periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberDeterministicScheduleExpectation
              H N hN beta hbeta B target source g₂ [fiber] k₁ A F₁ -
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberDeterministicScheduleExpectation
              H N hN beta hbeta B target source g₂ [fiber] k₂ A F₂| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ fiber : PeriodicHypercubicEvenSpatialSliceLink H,
          finiteInfluenceKernelUpdatedVariation
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedKernel
              H beta hbeta)
            profile (Sum.inl fiber) (Sum.inr source) := by
        apply Finset.sum_le_sum
        intro fiber _
        exact hTarget fiber
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectation
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanUpdatedVariation
  unfold finiteInfluenceKernelRestrictedTargetRandomScanUpdatedVariation
  calc
    |(Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ)⁻¹ *
          (∑ fiber : PeriodicHypercubicEvenSpatialSliceLink H,
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberDeterministicScheduleExpectation
              H N hN beta hbeta B target source g₂ [fiber] k₁ A F₁) -
        (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ)⁻¹ *
          (∑ fiber : PeriodicHypercubicEvenSpatialSliceLink H,
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberDeterministicScheduleExpectation
              H N hN beta hbeta B target source g₂ [fiber] k₂ A F₂)| =
      (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ)⁻¹ *
        |∑ fiber : PeriodicHypercubicEvenSpatialSliceLink H,
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberDeterministicScheduleExpectation
              H N hN beta hbeta B target source g₂ [fiber] k₁ A F₁ -
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberDeterministicScheduleExpectation
              H N hN beta hbeta B target source g₂ [fiber] k₂ A F₂)| := by
      rw [← mul_sub, ← Finset.sum_sub_distrib, abs_mul,
        abs_of_nonneg hInvNonneg]
    _ ≤ (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ)⁻¹ *
        ∑ fiber : PeriodicHypercubicEvenSpatialSliceLink H,
          finiteInfluenceKernelUpdatedVariation
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedKernel
              H beta hbeta)
            profile (Sum.inl fiber) (Sum.inr source) :=
      mul_le_mul_of_nonneg_left hSum hInvNonneg

end

end MathlibAnalytic
end MGAP4D