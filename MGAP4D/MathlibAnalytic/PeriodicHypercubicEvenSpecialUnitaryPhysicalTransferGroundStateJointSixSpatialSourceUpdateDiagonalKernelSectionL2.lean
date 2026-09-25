import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateKernelSectionGenuineOneLinkFiberBridge
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSixSpatialSweepStageSourceUpdateLocalMeanKernelSectionL2
import Mathlib.Tactic

/-!
# Diagonal outer-boundary specialization of the source local-mean section L2 carrier

PRs #4740--#4747 identify the genuine two-boundary ground-state joint law with
the physical vacuum outer law and an explicit fixed-right kernel-section Markov
kernel, and identify the one-link law inside each section with the genuine
ground-state one-link fiber law.

The local-mean L2 vector from PR #4738 was stated with a general reference
background `B`, two inserted reference values, and an independent left
boundary.  To glue those section energies back to the genuine joint residual we
need the canonical diagonal specialization attached to one outer boundary
`C`:

- `B = C`,
- `left = C`,
- `k = C distinguishedSource`,
- `g2 = C link`.

Both updates then restore exactly `C`.  This file transports the existing PR
#4738 vector, a.e. representative, fluctuation identification, and norm-square
identity to the literal section carrier `L2(kappa_C)`.

No new estimate is introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal

noncomputable section

local instance groundStateJointSourceDiagonalKernelSectionTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance groundStateJointSourceDiagonalKernelSectionCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance groundStateJointSourceDiagonalKernelSectionSecondCountable
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance groundStateJointSourceDiagonalKernelSectionMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance groundStateJointSourceDiagonalKernelSectionBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance groundStateJointSourceDiagonalKernelSectionSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Updating two coordinates by the values already present in the same
configuration leaves the retained boundary unchanged. -/
@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceDiagonalRetainedBoundary_eq
    (H N : ℕ)
    (C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (link distinguishedSource : PeriodicHypercubicEvenSpatialSliceLink H) :
    Function.update
        (Function.update C distinguishedSource (C distinguishedSource))
        link (C link) = C := by
  simp

/-- Canonical local-mean section L2 vector at one outer vacuum boundary. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateDiagonalLocalMeanKernelSectionL2
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (link distinguishedSource : PeriodicHypercubicEvenSpatialSliceLink H)
    (hRefNe : link ≠ distinguishedSource)
    (hNoShare :
      ¬ periodicHypercubicEvenSpatialSliceLinksSharePlaquette
        H link distinguishedSource)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound) :
    Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
        H N hN beta hbeta C) := by
  simpa only [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceDiagonalRetainedBoundary_eq] using
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateLocalMeanKernelSectionL2
      H N hN beta hbeta C link distinguishedSource hRefNe hNoShare
      (C distinguishedSource) (C link) F hF bound hbound C)

/-- On the canonical diagonal section, the physical diagonal local mean is
a.e. the existing remote one-link fluctuation of the right section
`A ↦ F(C,A)`. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateDiagonalLocalMean_ae_eq_kernelSectionFluctuation_of_remote
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (link distinguishedSource : PeriodicHypercubicEvenSpatialSliceLink H)
    (hRefNe : link ≠ distinguishedSource)
    (hNoShare :
      ¬ periodicHypercubicEvenSpatialSliceLinksSharePlaquette
        H link distinguishedSource)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound) :
    (fun A =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateDiagonalLocalMean
        H N hN beta hbeta link F C C distinguishedSource
        (C distinguishedSource) (C link) A) =ᵐ[
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
        H N hN beta hbeta C]
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkFluctuation
        H N hN beta hbeta C link distinguishedSource link
        (C distinguishedSource) (C link)
        (fun A => F (C, A)) := by
  simpa only [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceDiagonalRetainedBoundary_eq] using
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateDiagonalLocalMean_ae_eq_kernelSectionFluctuation_of_remote
      H N hN beta hbeta C link distinguishedSource hRefNe hNoShare
      (C distinguishedSource) (C link) F hF bound hbound C)

/-- The canonical diagonal section L2 vector has the diagonal local mean as an
a.e. representative on the literal section probability law. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateDiagonalLocalMeanKernelSectionL2_coeFn
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (link distinguishedSource : PeriodicHypercubicEvenSpatialSliceLink H)
    (hRefNe : link ≠ distinguishedSource)
    (hNoShare :
      ¬ periodicHypercubicEvenSpatialSliceLinksSharePlaquette
        H link distinguishedSource)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateDiagonalLocalMeanKernelSectionL2
        H N hN beta hbeta C link distinguishedSource hRefNe hNoShare
        F hF bound hbound =ᵐ[
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
        H N hN beta hbeta C]
      (fun A =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateDiagonalLocalMean
          H N hN beta hbeta link F C C distinguishedSource
          (C distinguishedSource) (C link) A) := by
  simpa only [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateDiagonalLocalMeanKernelSectionL2,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceDiagonalRetainedBoundary_eq] using
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateLocalMeanKernelSectionL2_coeFn
      H N hN beta hbeta C link distinguishedSource hRefNe hNoShare
      (C distinguishedSource) (C link) F hF bound hbound C)

/-- Exact norm-square formula for the canonical diagonal section vector. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateDiagonalLocalMeanKernelSectionL2_norm_sq_eq_integral_sq
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (link distinguishedSource : PeriodicHypercubicEvenSpatialSliceLink H)
    (hRefNe : link ≠ distinguishedSource)
    (hNoShare :
      ¬ periodicHypercubicEvenSpatialSliceLinksSharePlaquette
        H link distinguishedSource)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateDiagonalLocalMeanKernelSectionL2
        H N hN beta hbeta C link distinguishedSource hRefNe hNoShare
        F hF bound hbound‖ ^ 2 =
      ∫ A,
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateDiagonalLocalMean
          H N hN beta hbeta link F C C distinguishedSource
          (C distinguishedSource) (C link) A) ^ 2
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
          H N hN beta hbeta C := by
  simpa only [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateDiagonalLocalMeanKernelSectionL2,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceDiagonalRetainedBoundary_eq] using
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateLocalMeanKernelSectionL2_norm_sq_eq_integral_sq
      H N hN beta hbeta C link distinguishedSource hRefNe hNoShare
      (C distinguishedSource) (C link) F hF bound hbound C)

end

end MathlibAnalytic
end MGAP4D
