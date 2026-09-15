import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceCrossBoundaryHeatBathTwoStepVariationPropagation
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

local instance referenceCrossBoundaryHeatBathDistinctFiberTransportCriterionSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Augment the already-proved one-way cross-boundary carrier by an explicit
left-left off-fiber influence.  The left-left entry is deliberately supplied
as data rather than inferred from the structurally-zero block of the old
one-way carrier. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryDistinctFiberTaggedInfluence
    (H : ℕ)
    (beta : ℝ)
    (offFiberInfluence :
      PeriodicHypercubicEvenSpatialSliceLink H →
        PeriodicHypercubicEvenSpatialSliceLink H → ℝ) :
    Sum
        (PeriodicHypercubicEvenSpatialSliceLink H)
        (PeriodicHypercubicEvenSpatialSliceLink H) →
      Sum
        (PeriodicHypercubicEvenSpatialSliceLink H)
        (PeriodicHypercubicEvenSpatialSliceLink H) → ℝ
  | Sum.inl target, Sum.inl source =>
      if target = source then 0 else offFiberInfluence target source
  | Sum.inl target, Sum.inr source =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBoundedTestMajorant
        beta target source
  | _, _ => 0

/-- The augmented carrier is a genuine nonnegative influence kernel whenever
the supplied off-fiber influence is nonnegative. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryDistinctFiberTaggedKernelData
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (offFiberInfluence :
      PeriodicHypercubicEvenSpatialSliceLink H →
        PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hOffFiberInfluenceNonneg :
      ∀ target source, 0 ≤ offFiberInfluence target source) :
    FiniteNonnegativeInfluenceKernelData
      (Sum
        (PeriodicHypercubicEvenSpatialSliceLink H)
        (PeriodicHypercubicEvenSpatialSliceLink H)) :=
  { influence :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryDistinctFiberTaggedInfluence
        H beta offFiberInfluence
    influence_nonneg := by
      intro target source
      cases target with
      | inl target =>
          cases source with
          | inl source =>
              by_cases hEq : target = source
              · simp [
                  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryDistinctFiberTaggedInfluence,
                  hEq]
              · simpa [
                  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryDistinctFiberTaggedInfluence,
                  hEq] using hOffFiberInfluenceNonneg target source
          | inr source =>
              simpa [
                periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryDistinctFiberTaggedInfluence,
                periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTaggedInfluence] using
                periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTaggedInfluence_nonneg
                  H beta hbeta (Sum.inl target) (Sum.inr source)
      | inr target =>
          cases source <;>
            simp [
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryDistinctFiberTaggedInfluence]
    influence_diagonal_zero := by
      intro e
      cases e with
      | inl e =>
          simp [
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryDistinctFiberTaggedInfluence]
      | inr e =>
          rfl }

/-- On distinct physical fibers, the new left-left block is exactly the
explicit off-fiber transport coefficient. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryDistinctFiberTaggedKernelData_left_left
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (offFiberInfluence :
      PeriodicHypercubicEvenSpatialSliceLink H →
        PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hOffFiberInfluenceNonneg :
      ∀ target source, 0 ≤ offFiberInfluence target source)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (hDistinct : target ≠ source) :
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryDistinctFiberTaggedKernelData
        H beta hbeta offFiberInfluence hOffFiberInfluenceNonneg).influence
        (Sum.inl target) (Sum.inl source) =
      offFiberInfluence target source := by
  simp [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryDistinctFiberTaggedKernelData,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryDistinctFiberTaggedInfluence,
    hDistinct]

/-- The represented left-target/right-source block is unchanged from the
already-proved continuous C5 cross-boundary majorant. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryDistinctFiberTaggedKernelData_left_right
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (offFiberInfluence :
      PeriodicHypercubicEvenSpatialSliceLink H →
        PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hOffFiberInfluenceNonneg :
      ∀ target source, 0 ≤ offFiberInfluence target source)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H) :
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryDistinctFiberTaggedKernelData
        H beta hbeta offFiberInfluence hOffFiberInfluenceNonneg).influence
        (Sum.inl target) (Sum.inr source) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBoundedTestMajorant
        beta target source := by
  rfl

/-- Exact algebraic content of two distinct target updates.  The first update
at `fiber₂` transports its variation into `fiber₁` through the explicit
left-left coefficient; the second update at `fiber₁` then exports that enlarged
variation to the represented right source. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryDistinctFiberTagged_twoTargetUpdatedVariation_rightSource_eq
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (offFiberInfluence :
      PeriodicHypercubicEvenSpatialSliceLink H →
        PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hOffFiberInfluenceNonneg :
      ∀ target source, 0 ≤ offFiberInfluence target source)
    (variation : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (fiber₁ fiber₂ source : PeriodicHypercubicEvenSpatialSliceLink H)
    (hDistinct : fiber₁ ≠ fiber₂) :
    finiteInfluenceKernelUpdatedVariation
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryDistinctFiberTaggedKernelData
          H beta hbeta offFiberInfluence hOffFiberInfluenceNonneg)
        (fun e =>
          finiteInfluenceKernelUpdatedVariation
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryDistinctFiberTaggedKernelData
              H beta hbeta offFiberInfluence hOffFiberInfluenceNonneg)
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTaggedLeftVariation
              H variation)
            (Sum.inl fiber₂)
            e)
        (Sum.inl fiber₁)
        (Sum.inr source) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBoundedTestMajorant
          beta fiber₂ source * variation fiber₂ +
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBoundedTestMajorant
          beta fiber₁ source *
          (variation fiber₁ + offFiberInfluence fiber₂ fiber₁ * variation fiber₂) := by
  simp [
    finiteInfluenceKernelUpdatedVariation,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryDistinctFiberTaggedKernelData,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryDistinctFiberTaggedInfluence,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTaggedLeftVariation,
    hDistinct,
    Ne.symm hDistinct]

/-- Literal two-step physical heat-bath expectation with independently chosen
boundary-source parameters for the first and second updates.  This is only a
notation layer: no unproved invariance between the two physical kernels is
inserted. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryDistinctFiberTwoStepExpectation
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source fiber₁ fiber₂ : PeriodicHypercubicEvenSpatialSliceLink H)
    (kFirst kSecond g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (F : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ) : ℝ :=
  ∫ C, F C
    ∂((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel
          H N hN beta hbeta B target source fiber₂ kSecond g₂) ∘ₖ
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel
          H N hN beta hbeta B target source fiber₁ kFirst g₂)) A

/-- Distinct-fiber two-step transport criterion.  The physical proof obligation
is split at the mixed intermediate law.  `hFirstBoundary` controls changing the
boundary parameter of the first update after the second-step observable has
been transported back to `fiber₁`; `hSecondBoundary` controls changing the
second update with the first parameter already fixed at `k₂`.

The conclusion is exactly two target updates of the augmented tagged carrier.
Thus no left-left zero from the old one-way carrier is used as a physical
statement.  A later density theorem may discharge the explicit off-fiber
transport hypothesis encoded by the first bound. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryDistinctFiber_twoStepHeatBath_transportCriterion
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source fiber₁ fiber₂ : PeriodicHypercubicEvenSpatialSliceLink H)
    (hDistinct : fiber₁ ≠ fiber₂)
    (k₁ k₂ g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (F : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ)
    (variation : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (offFiberInfluence :
      PeriodicHypercubicEvenSpatialSliceLink H →
        PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hOffFiberInfluenceNonneg :
      ∀ target source, 0 ≤ offFiberInfluence target source)
    (hFirstBoundary :
      |periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryDistinctFiberTwoStepExpectation
          H N hN beta hbeta B target source fiber₁ fiber₂ k₁ k₁ g₂ A F -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryDistinctFiberTwoStepExpectation
          H N hN beta hbeta B target source fiber₁ fiber₂ k₂ k₁ g₂ A F| ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBoundedTestMajorant
            beta fiber₁ source *
          (variation fiber₁ + offFiberInfluence fiber₂ fiber₁ * variation fiber₂))
    (hSecondBoundary :
      |periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryDistinctFiberTwoStepExpectation
          H N hN beta hbeta B target source fiber₁ fiber₂ k₂ k₁ g₂ A F -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryDistinctFiberTwoStepExpectation
          H N hN beta hbeta B target source fiber₁ fiber₂ k₂ k₂ g₂ A F| ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBoundedTestMajorant
            beta fiber₂ source * variation fiber₂) :
    |periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryDistinctFiberTwoStepExpectation
        H N hN beta hbeta B target source fiber₁ fiber₂ k₁ k₁ g₂ A F -
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryDistinctFiberTwoStepExpectation
        H N hN beta hbeta B target source fiber₁ fiber₂ k₂ k₂ g₂ A F| ≤
      finiteInfluenceKernelUpdatedVariation
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryDistinctFiberTaggedKernelData
          H beta hbeta offFiberInfluence hOffFiberInfluenceNonneg)
        (fun e =>
          finiteInfluenceKernelUpdatedVariation
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryDistinctFiberTaggedKernelData
              H beta hbeta offFiberInfluence hOffFiberInfluenceNonneg)
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTaggedLeftVariation
              H variation)
            (Sum.inl fiber₂)
            e)
        (Sum.inl fiber₁)
        (Sum.inr source) := by
  let x :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryDistinctFiberTwoStepExpectation
      H N hN beta hbeta B target source fiber₁ fiber₂ k₁ k₁ g₂ A F
  let y :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryDistinctFiberTwoStepExpectation
      H N hN beta hbeta B target source fiber₁ fiber₂ k₂ k₁ g₂ A F
  let z :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryDistinctFiberTwoStepExpectation
      H N hN beta hbeta B target source fiber₁ fiber₂ k₂ k₂ g₂ A F
  have hEq : x - z = (x - y) + (y - z) := by ring
  change |x - z| ≤ _
  rw [hEq]
  calc
    |(x - y) + (y - z)| ≤ |x - y| + |y - z| := by
      simpa [Real.norm_eq_abs] using norm_add_le (x - y) (y - z)
    _ ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBoundedTestMajorant
            beta fiber₁ source *
          (variation fiber₁ + offFiberInfluence fiber₂ fiber₁ * variation fiber₂) +
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBoundedTestMajorant
            beta fiber₂ source * variation fiber₂ := by
      exact add_le_add hFirstBoundary hSecondBoundary
    _ =
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBoundedTestMajorant
            beta fiber₂ source * variation fiber₂ +
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBoundedTestMajorant
            beta fiber₁ source *
          (variation fiber₁ + offFiberInfluence fiber₂ fiber₁ * variation fiber₂) := by
      ring
    _ =
      finiteInfluenceKernelUpdatedVariation
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryDistinctFiberTaggedKernelData
          H beta hbeta offFiberInfluence hOffFiberInfluenceNonneg)
        (fun e =>
          finiteInfluenceKernelUpdatedVariation
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryDistinctFiberTaggedKernelData
              H beta hbeta offFiberInfluence hOffFiberInfluenceNonneg)
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTaggedLeftVariation
              H variation)
            (Sum.inl fiber₂)
            e)
        (Sum.inl fiber₁)
        (Sum.inr source) := by
      symm
      exact
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryDistinctFiberTagged_twoTargetUpdatedVariation_rightSource_eq
          H beta hbeta offFiberInfluence hOffFiberInfluenceNonneg variation
          fiber₁ fiber₂ source hDistinct

end

end MathlibAnalytic
end MGAP4D