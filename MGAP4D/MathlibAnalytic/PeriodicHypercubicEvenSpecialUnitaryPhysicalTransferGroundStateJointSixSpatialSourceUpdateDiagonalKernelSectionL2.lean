import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSixSpatialSweepStageSourceUpdateLocalMeanKernelSectionL2
import Mathlib.Tactic

/-!
# Diagonal outer-boundary specialization of the source local-mean section L2 carrier

The local-mean L2 vector from PR #4738 was stated with a general reference
background `B`, two inserted reference values, and an independent left
boundary.  To glue section energies back to the genuine joint residual we need
the canonical diagonal specialization attached to one outer boundary `C`:

- `B = C`,
- `left = C`,
- `k = C distinguishedSource`,
- `g2 = C link`.

Both current-value updates restore exactly `C`.  Rather than transporting an
existing dependent `Lp` term across an equality of measures, this file first
specializes the already-proved fluctuation `MemLp 2` theorem and constructs
the canonical `Lp` vector directly on the literal section probability law.

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

/-- Updating coordinates by their values already present in the same
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

/-- The diagonal remote one-link fluctuation belongs to the literal canonical
fixed-right section L2 space. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateDiagonalOuterKernelSectionFluctuation_memLp_two
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
    MemLp
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkFluctuation
        H N hN beta hbeta C link distinguishedSource link
        (C distinguishedSource) (C link)
        (fun A => F (C, A)))
      2
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
        H N hN beta hbeta C) := by
  have hRetained :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceDiagonalRetainedBoundary_eq
      H N C link distinguishedSource
  have hBase :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateKernelSectionFluctuation_memLp_two_of_remote
      H N hN beta hbeta C link distinguishedSource hRefNe hNoShare
      (C distinguishedSource) (C link) F hF bound hbound C
  simpa only [hRetained] using hBase

/-- Canonical diagonal local-mean L2 vector at one outer vacuum boundary.  It
is built directly from the diagonal one-link fluctuation on the literal
section law. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateDiagonalOuterLocalMeanKernelSectionL2
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
        H N hN beta hbeta C) :=
  (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateDiagonalOuterKernelSectionFluctuation_memLp_two
    H N hN beta hbeta C link distinguishedSource hRefNe hNoShare
    F hF bound hbound).toLp
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkFluctuation
        H N hN beta hbeta C link distinguishedSource link
        (C distinguishedSource) (C link)
        (fun A => F (C, A)))

/-- On the canonical diagonal section, the physical local mean is a.e. the
existing remote one-link fluctuation of the right section `A ↦ F(C,A)`. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateDiagonalOuterLocalMean_ae_eq_kernelSectionFluctuation_of_remote
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
  have hRetained :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceDiagonalRetainedBoundary_eq
      H N C link distinguishedSource
  have hBase :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateDiagonalLocalMean_ae_eq_kernelSectionFluctuation_of_remote
      H N hN beta hbeta C link distinguishedSource hRefNe hNoShare
      (C distinguishedSource) (C link) F hF bound hbound C
  simpa only [hRetained] using hBase

/-- The canonical diagonal section L2 vector has the physical diagonal local
mean as an a.e. representative. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateDiagonalOuterLocalMeanKernelSectionL2_coeFn
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
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateDiagonalOuterLocalMeanKernelSectionL2
        H N hN beta hbeta C link distinguishedSource hRefNe hNoShare
        F hF bound hbound A) =ᵐ[
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
        H N hN beta hbeta C]
      (fun A =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateDiagonalLocalMean
          H N hN beta hbeta link F C C distinguishedSource
          (C distinguishedSource) (C link) A) := by
  have hFluct :=
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateDiagonalOuterKernelSectionFluctuation_memLp_two
      H N hN beta hbeta C link distinguishedSource hRefNe hNoShare
      F hF bound hbound).coeFn_toLp
  have hLocal :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateDiagonalOuterLocalMean_ae_eq_kernelSectionFluctuation_of_remote
      H N hN beta hbeta C link distinguishedSource hRefNe hNoShare
      F hF bound hbound
  exact hFluct.trans hLocal.symm

/-- Exact norm-square formula for the canonical diagonal section vector. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateDiagonalOuterLocalMeanKernelSectionL2_norm_sq_eq_integral_sq
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
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateDiagonalOuterLocalMeanKernelSectionL2
        H N hN beta hbeta C link distinguishedSource hRefNe hNoShare
        F hF bound hbound‖ ^ 2 =
      ∫ A,
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateDiagonalLocalMean
          H N hN beta hbeta link F C C distinguishedSource
          (C distinguishedSource) (C link) A) ^ 2
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
          H N hN beta hbeta C := by
  let μ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
      H N hN beta hbeta C
  let q :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateDiagonalOuterLocalMeanKernelSectionL2
      H N hN beta hbeta C link distinguishedSource hRefNe hNoShare
      F hF bound hbound
  letI : IsProbabilityMeasure μ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure_isProbabilityMeasure
      H N hN beta hbeta C
  have hRep :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateDiagonalOuterLocalMeanKernelSectionL2_coeFn
      H N hN beta hbeta C link distinguishedSource hRefNe hNoShare
      F hF bound hbound
  change ‖q‖ ^ 2 =
    ∫ A,
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateDiagonalLocalMean
        H N hN beta hbeta link F C C distinguishedSource
        (C distinguishedSource) (C link) A) ^ 2 ∂μ
  calc
    ‖q‖ ^ 2 = ∫ A, ‖q A‖ ^ 2 ∂μ :=
      realL2_norm_sq_eq_integral_norm_sq q
    _ = ∫ A,
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateDiagonalLocalMean
          H N hN beta hbeta link F C C distinguishedSource
          (C distinguishedSource) (C link) A) ^ 2 ∂μ := by
      apply integral_congr_ae
      filter_upwards [hRep] with A hA
      rw [hA]
      simp [Real.norm_eq_abs, sq_abs]

end

end MathlibAnalytic
end MGAP4D
