import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourceFixedPairVariance

namespace MGAP4D.MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open GroundStateSourceFixedPairEnergy

attribute [local instance]
  sourceFixedPairEnergyIsTopologicalGroup
  sourceFixedPairEnergyCompactSpace
  sourceFixedPairEnergySecondCountableTopology
  sourceFixedPairEnergyMeasurableSpace
  sourceFixedPairEnergyBorelSpace
  sourceFixedPairEnergySpatialLinkFintype

#check targetMean_stronglyMeasurable
#check targetMean_sourceSection_memLp_two
#check sourceProjectedTargetMean_eq_fiberIntegral
#check sourceProjectedTargetMean_update_source
#check conditionalVarianceEnergy_eq_fixedBoundaryLeakageEnergy
#check pairEnergy_ofReal_eq_two_mul_fixedBoundaryLeakageEnergy
#check fixedBoundaryLeakageEnergy_vacuum_le_half_orderedCoefficient_mul_condExpResidual_of_sourceInvariant
#check exists_sourceUpdate_representative_fixedBoundaryLeakageEnergy_bound

-- No source invariance, off-diagonal geometry or bound is needed for stationary return.
example (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (source target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F : (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    conditionalVarianceEnergy H N hN beta hbeta source target F C =
      fixedBoundaryLeakageEnergy H N hN beta hbeta source target F C :=
  conditionalVarianceEnergy_eq_fixedBoundaryLeakageEnergy H N hN beta hbeta source target F hF C

-- Cancelling two in ENNReal uses its nonzero AND finite hypotheses explicitly.
example (E B : ℝ≥0∞) (h : 2 * E ≤ B) : E ≤ (2 : ℝ≥0∞)⁻¹ * B := by
  exact (ENNReal.mul_le_iff_le_inv (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by simp : (2 : ℝ≥0∞) ≠ ⊤)).mp h

end MGAP4D.MathlibAnalytic
