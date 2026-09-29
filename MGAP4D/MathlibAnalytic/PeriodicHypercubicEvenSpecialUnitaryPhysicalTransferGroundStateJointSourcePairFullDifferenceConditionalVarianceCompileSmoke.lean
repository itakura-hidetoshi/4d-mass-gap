import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourcePairFullDifferenceConditionalVariance

namespace MGAP4D.MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

attribute [local instance]
  fullDifferenceVarianceIsTopologicalGroup
  fullDifferenceVarianceCompactSpace
  fullDifferenceVarianceSecondCountableTopology
  fullDifferenceVarianceMeasurableSpace
  fullDifferenceVarianceBorelSpace
  fullDifferenceVarianceSpatialLinkFintype

#check periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSourceValueMean_stronglyMeasurable
#check periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMean_eq_sourceValueMean
#check periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFullDifferenceL2_norm_sq_ofReal_eq_two_mul_sourceValueMean_evariance_lintegral
#check GroundStateSourceFixedPairEnergy.fullDifferenceL2_norm_sq_ofReal_eq_two_mul_conditionalVarianceEnergy
#check GroundStateSourceFixedPairEnergy.pairEnergy_ofReal_eq_two_mul_conditionalVarianceEnergy
#check GroundStateSourceFixedPairEnergy.fullDifferenceL2_vacuum_norm_sq_eq_two_mul_conditionalVarianceEnergy
#check GroundStateSourceFixedPairEnergy.conditionalVarianceEnergy_vacuum_two_mul_le_orderedCoefficient_mul_condExpResidual_of_sourceInvariant

-- Both source samples evaluate one section; no source-fixed premise is needed.
example
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource source target : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (F : (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (left : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) (center : ℝ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) (u v : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOldFirstMean H N hN beta hbeta B distinguishedSource source target k g₂ F left center (A, (u, v)) -
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMean H N hN beta hbeta B distinguishedSource source target k g₂ F left center (A, (u, v)) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSourceValueMean H N hN beta hbeta B distinguishedSource source target k g₂ F left center (A, u) -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSourceValueMean H N hN beta hbeta B distinguishedSource source target k g₂ F left center (A, v) := by
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMean_eq_sourceValueMean]
  rfl

end MGAP4D.MathlibAnalytic
