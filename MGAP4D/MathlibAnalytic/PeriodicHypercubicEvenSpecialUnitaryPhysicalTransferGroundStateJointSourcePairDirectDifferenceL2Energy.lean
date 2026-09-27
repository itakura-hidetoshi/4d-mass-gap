import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourcePairTargetLawL2SemanticIdentification
import Mathlib.Tactic

/-!
# Source-pair direct-difference L2 energy

PR #4851 identifies the target-law direct-difference L2 vector with the actual
physical direct source-update mean difference on the source-pair background
carrier.

This file records the exact squared-norm realization of that vector:

  ||DirectDifferenceL2||^2
    =
  integral_(nu_source) (directMeanDifference)^2.

This is the Hilbert-space bridge needed before applying the existing
#4728--#4735 direct-energy law-reordering chain.  No inequality, response
coefficient, target-cardinality factor, or change of probability law is
introduced.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

local instance sourcePairDirectDifferenceL2EnergySpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance sourcePairDirectDifferenceL2EnergySpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance sourcePairDirectDifferenceL2EnergySpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance sourcePairDirectDifferenceL2EnergySpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance sourcePairDirectDifferenceL2EnergySpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- For an off-diagonal target/source pair, the squared Hilbert norm of the
physical direct-difference vector is exactly the source-pair average of the
actual direct mean-difference square. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawDirectDifferenceL2_norm_sq_eq_integral_directMeanDifference_sq_of_ne
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
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
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdateDirectMeanDifference
          H N hN beta hbeta target source hne F left B z.1
          (periodicHypercubicEvenSpatialSliceOffTargetRestriction target z.1)
          distinguishedSource k g₂ z.2.1 z.2.2 center ^ 2
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceIndependentPairBackgroundMeasure
          H N hN beta hbeta B distinguishedSource source k g₂ := by
  let μ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceIndependentPairBackgroundMeasure
      H N hN beta hbeta B distinguishedSource source k g₂
  let direct :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawDirectDifferenceL2
      H N hN beta hbeta B distinguishedSource source target k g₂
      F hF bound hbound left center
  let delta :=
    fun z :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        (Matrix.specialUnitaryGroup (Fin N) ℂ ×
          Matrix.specialUnitaryGroup (Fin N) ℂ) =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdateDirectMeanDifference
        H N hN beta hbeta target source hne F left B z.1
        (periodicHypercubicEvenSpatialSliceOffTargetRestriction target z.1)
        distinguishedSource k g₂ z.2.1 z.2.2 center
  have hRep :
      (fun z => direct z) =ᵐ[μ] delta := by
    simpa [direct, delta, μ] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawDirectDifferenceL2_coeFn_semantic
        H N hN beta hbeta B distinguishedSource source target hne
        k g₂ F hF bound hbound left center
  change ‖direct‖ ^ 2 = ∫ z, delta z ^ 2 ∂μ
  calc
    ‖direct‖ ^ 2 = ∫ z, ‖direct z‖ ^ 2 ∂μ :=
      realL2_norm_sq_eq_integral_norm_sq direct
    _ = ∫ z, delta z ^ 2 ∂μ := by
      apply integral_congr_ae
      filter_upwards [hRep] with z hz
      rw [hz]
      simp [Real.norm_eq_abs, sq_abs]

end

end MGAP4D.MathlibAnalytic
