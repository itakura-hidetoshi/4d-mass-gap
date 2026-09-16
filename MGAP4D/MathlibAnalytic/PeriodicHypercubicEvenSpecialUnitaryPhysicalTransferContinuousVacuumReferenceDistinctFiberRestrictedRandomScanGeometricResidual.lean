import MGAP4D.MathlibAnalytic.FiniteInfluenceKernelRestrictedTargetRandomScanGeometricResidual
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceDistinctFiberRestrictedRandomScanFiniteStepTransport
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory BigOperators

noncomputable section

local instance referenceDistinctFiberRestrictedRandomScanGeometricResidualSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- The physical time-zero spatial link carrier is nonempty for every `H`.
This closes the positive-cardinality hypothesis needed by the generic reciprocal
random-scan estimate without adding a geometric assumption. -/
theorem periodicHypercubicEvenSpatialSliceLink_card_pos
    (H : ℕ) :
    0 < Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) := by
  classical
  exact Fintype.card_pos_iff.mpr ⟨
    (⟨(fun _ => 0), by
        simp [periodicHypercubicEvenOnPrimaryReflectionPlane]⟩,
      ⟨1, by norm_num⟩)⟩

/-- On the physical left carrier, every off-diagonal tagged influence is the
same literal-C5 coefficient and the diagonal is exactly zero.  Hence each
column sum is `(card - 1) * offFiberInfluence`. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedLeftRestriction_columnSum_eq
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (source : PeriodicHypercubicEvenSpatialSliceLink H) :
    finiteInfluenceKernelColumnSum
        (finiteInfluenceKernelSumLeftRestriction
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedKernel
            H beta hbeta))
        source =
      ((Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) - 1) *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberOffFiberInfluence
          beta := by
  classical
  change
    (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedKernel
        H beta hbeta).influence (Sum.inl target) (Sum.inl source)) = _
  have hPointwise
      (target : PeriodicHypercubicEvenSpatialSliceLink H) :
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedKernel
          H beta hbeta).influence (Sum.inl target) (Sum.inl source) =
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberOffFiberInfluence
            beta -
          (if target = source then
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberOffFiberInfluence
              beta
          else 0) := by
    by_cases hEq : target = source
    · subst target
      rw [
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedKernel
          H beta hbeta).influence_diagonal_zero (Sum.inl source)]
      simp
    · rw [
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedKernel_left_left_of_ne
          H beta hbeta target source hEq]
      simp [hEq]
  calc
    (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedKernel
        H beta hbeta).influence (Sum.inl target) (Sum.inl source)) =
      ∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberOffFiberInfluence
            beta -
          (if target = source then
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberOffFiberInfluence
              beta
          else 0)) := by
        apply Finset.sum_congr rfl
        intro target _
        exact hPointwise target
    _ =
      (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberOffFiberInfluence
            beta -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberOffFiberInfluence
          beta := by
      rw [Finset.sum_sub_distrib]
      simp [nsmul_eq_mul]
    _ =
      ((Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) - 1) *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberOffFiberInfluence
          beta := by ring

/-- The explicit physical tagged restricted scan inherits the generic geometric
forcing residual.  The represented right-source coordinate is never scanned;
its initial tagged value is zero and it only accumulates forcing from shrinking
physical left coordinates. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanVariationIterate_inr_le_geometricResidual
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (variation : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hVariationNonneg : ∀ e, 0 ≤ variation e)
    (bound : ℝ)
    (hBoundNonneg : 0 ≤ bound)
    (hVariationBound : ∀ e, variation e ≤ bound)
    (source : PeriodicHypercubicEvenSpatialSliceLink H)
    (n : ℕ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanVariationIterate
        H beta hbeta variation n (Sum.inr source) ≤
      (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ)⁻¹ *
        (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBoundedTestMajorant
            beta target source) *
        bound *
        Finset.sum (Finset.range n)
          (fun j =>
            finiteInfluenceKernelReciprocalRandomScanRate
              (PeriodicHypercubicEvenSpatialSliceLink H)
              (((Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) - 1) *
                periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberOffFiberInfluence
                  beta) ^ j) := by
  classical
  let Link := PeriodicHypercubicEvenSpatialSliceLink H
  let K :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedKernel
      H beta hbeta
  let initial :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTaggedLeftVariation
      H variation
  let columnCoefficient : ℝ :=
    ((Fintype.card Link : ℝ) - 1) *
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberOffFiberInfluence
        beta
  let sourceCoefficient : ℝ :=
    ∑ target : Link,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBoundedTestMajorant
        beta target source
  have hCard : 0 < Fintype.card Link := by
    simpa [Link] using periodicHypercubicEvenSpatialSliceLink_card_pos H
  have hCardOneReal : (1 : ℝ) ≤ (Fintype.card Link : ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.mpr hCard)
  have hColumnNonneg : 0 ≤ columnCoefficient := by
    dsimp [columnCoefficient]
    exact mul_nonneg
      (sub_nonneg.mpr hCardOneReal)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberOffFiberInfluence_nonneg
        beta hbeta)
  have hColumnSum :
      ∀ src : Link,
        finiteInfluenceKernelColumnSum
          (finiteInfluenceKernelSumLeftRestriction K) src ≤ columnCoefficient := by
    intro src
    dsimp [K, columnCoefficient]
    rw [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedLeftRestriction_columnSum_eq
        H beta hbeta src]
  have hInitialNonneg : ∀ e : Link, 0 ≤ initial (Sum.inl e) := by
    intro e
    dsimp [initial]
    simpa [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTaggedLeftVariation] using
      hVariationNonneg e
  have hInitialBound : ∀ e : Link, initial (Sum.inl e) ≤ bound := by
    intro e
    dsimp [initial]
    simpa [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTaggedLeftVariation] using
      hVariationBound e
  have hSourceSum :
      (∑ target : Link, K.influence (Sum.inl target) (Sum.inr source)) ≤
        sourceCoefficient := by
    dsimp [K, sourceCoefficient]
    apply le_of_eq
    apply Finset.sum_congr rfl
    intro target _
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedKernel_left_right
        H beta hbeta target source
  have hGeneric :=
    finiteInfluenceKernelSumRestrictedTargetRandomScanVariationIterate_inr_le_geometricResidual
      K hCard columnCoefficient hColumnNonneg hColumnSum initial
      hInitialNonneg bound hBoundNonneg hInitialBound source sourceCoefficient
      hSourceSum n
  simpa [
    Link, K, initial, columnCoefficient, sourceCoefficient,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanVariationIterate,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTaggedLeftVariation] using
    hGeneric

/-- Therefore the actual finite-step physical continuous-C5 boundary response is
bounded by the same geometric forcing residual.  This theorem is the bridge
from the physical expectation iterate to the generic contraction machinery. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate_transport_le_geometricResidual
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
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
    (bound : ℝ)
    (hBoundNonneg : 0 ≤ bound)
    (hVariationBound : ∀ e, variation e ≤ bound)
    (n : ℕ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    |periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate
        H N hN beta hbeta B target source g₂ k₁ F n A -
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate
        H N hN beta hbeta B target source g₂ k₂ F n A| ≤
      (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ)⁻¹ *
        (∑ fiber : PeriodicHypercubicEvenSpatialSliceLink H,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBoundedTestMajorant
            beta fiber source) *
        bound *
        Finset.sum (Finset.range n)
          (fun j =>
            finiteInfluenceKernelReciprocalRandomScanRate
              (PeriodicHypercubicEvenSpatialSliceLink H)
              (((Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) - 1) *
                periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberOffFiberInfluence
                  beta) ^ j) := by
  have hTransport :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate_transport_le
      H N hN beta hbeta B target source g₂ k₁ k₂ F hF variation
      hVariationNonneg hVariation n A
  have hResidual :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanVariationIterate_inr_le_geometricResidual
      H beta hbeta variation hVariationNonneg bound hBoundNonneg
      hVariationBound source n
  exact hTransport.trans hResidual

end

end MathlibAnalytic
end MGAP4D
