import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourcePairTargetLawL2SemanticIdentification
import Mathlib.Tactic

/-!
# Exact source-pair L2 energy of the direct target-law update

PR #4851 identifies the canonical direct-difference L2 vector with the actual
physical direct source-update mean difference on the exact source-pair
background carrier.

This file upgrades that a.e. semantic identification to the exact squared-norm
identity

  ||directDifferenceL2||^2
    =
  integral (actual direct mean difference)^2.

This is the Hilbert-space energy bridge needed before applying the already
proved PR #4728--#4735 direct-energy law-reordering chain.

No new inequality, probability law, coefficient, response estimate,
finite-cardinality factor, or sweep identification is introduced.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

local instance directDifferenceL2EnergySpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance directDifferenceL2EnergySpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance directDifferenceL2EnergySpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance directDifferenceL2EnergySpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance directDifferenceL2EnergySpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance directDifferenceL2EnergySpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- The squared norm of the canonical direct-difference L2 vector is exactly
the source-pair-background average of the squared physical direct mean
difference. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawDirectDifferenceL2_norm_sq_eq_integral_directMeanDifference_sq
    (H N : ℕ) (hN : 0 < N)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource source target :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (hne : target ≠ source)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound)
    (left : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (center : ℝ) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawDirectDifferenceL2
        H N hN beta hbeta B distinguishedSource source target k g₂
        F hF bound hbound left center‖ ^ 2 =
      ∫ z,
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdateDirectMeanDifference
          H N hN beta hbeta target source hne F left B z.1
          (periodicHypercubicEvenSpatialSliceOffTargetRestriction target z.1)
          distinguishedSource k g₂ z.2.1 z.2.2 center) ^ 2
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceIndependentPairBackgroundMeasure
          H N hN beta hbeta B distinguishedSource source k g₂ := by
  let μ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceIndependentPairBackgroundMeasure
      H N hN beta hbeta B distinguishedSource source k g₂
  let q :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawDirectDifferenceL2
      H N hN beta hbeta B distinguishedSource source target k g₂
      F hF bound hbound left center
  have hRep :
      (fun z => q z) =ᵐ[μ]
        (fun z =>
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdateDirectMeanDifference
            H N hN beta hbeta target source hne F left B z.1
            (periodicHypercubicEvenSpatialSliceOffTargetRestriction target z.1)
            distinguishedSource k g₂ z.2.1 z.2.2 center) := by
    simpa [q, μ] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawDirectDifferenceL2_coeFn_semantic
        H N hN beta hbeta B distinguishedSource source target hne k g₂
        F hF bound hbound left center
  change
    ‖q‖ ^ 2 =
      ∫ z,
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdateDirectMeanDifference
          H N hN beta hbeta target source hne F left B z.1
          (periodicHypercubicEvenSpatialSliceOffTargetRestriction target z.1)
          distinguishedSource k g₂ z.2.1 z.2.2 center) ^ 2 ∂μ
  calc
    ‖q‖ ^ 2 = ∫ z, ‖q z‖ ^ 2 ∂μ :=
      realL2_norm_sq_eq_integral_norm_sq q
    _ =
        ∫ z,
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdateDirectMeanDifference
            H N hN beta hbeta target source hne F left B z.1
            (periodicHypercubicEvenSpatialSliceOffTargetRestriction target z.1)
            distinguishedSource k g₂ z.2.1 z.2.2 center) ^ 2 ∂μ := by
      apply integral_congr_ae
      filter_upwards [hRep] with z hz
      rw [hz]
      simp [Real.norm_eq_abs, sq_abs]

end

end MGAP4D.MathlibAnalytic
