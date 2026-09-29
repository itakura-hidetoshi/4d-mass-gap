import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourceFixedJointLeakage

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped ENNReal

#check GroundStateSourceFixedPairEnergy.canonicalMean_ae_eq_targetMean
#check GroundStateSourceFixedPairEnergy.sourceProjection_congr_ae
#check GroundStateSourceFixedPairEnergy.sourceProjectedTargetMean_ae_eq_canonicalDoubleMean
#check GroundStateSourceFixedPairEnergy.fixedBoundaryLeakageEnergy_vacuum_eq_jointLeakageNormSq
#check GroundStateSourceFixedPairEnergy.jointLeakage_norm_sq_le_half_orderedCoefficient_of_sourceInvariant
#check GroundStateSourceFixedPairEnergy.sourceUpdate_jointLeakage_norm_sq_le_half_orderedCoefficient

attribute [local instance]
  groundStateJointOneLinkBoundedCoreSpecialUnitaryIsTopologicalGroup
  groundStateJointOneLinkBoundedCoreSpecialUnitaryCompactSpace
  groundStateJointOneLinkBoundedCoreSpecialUnitarySecondCountableTopology
  groundStateJointOneLinkBoundedCoreSpecialUnitaryMeasurableSpace
  groundStateJointOneLinkBoundedCoreSpecialUnitaryBorelSpace
  groundStateJointOneLinkBoundedCoreSpatialLinkFintype
  groundStateJointOneLinkBoundedCoreTargetLinkFintype
  groundStateJointOneLinkBoundedCoreTargetLinkUnique

-- The exact joint numerator identity needs neither source invariance nor a
-- cutoff, and it includes source = target. Only the bound needs these extras.
example (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (source target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F : (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F) (bound : ℝ) (hbound : ∀ z, ‖F z‖ ≤ bound) :
    (∫⁻ C, GroundStateSourceFixedPairEnergy.fixedBoundaryLeakageEnergy
      H N hN beta hbeta source target F C
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure H N hN beta hbeta) =
    ENNReal.ofReal
      (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
        H N hN beta hbeta target
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
          H N hN beta hbeta F hF bound hbound) -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
          H N hN beta hbeta source
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
            H N hN beta hbeta target
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
              H N hN beta hbeta F hF bound hbound))‖ ^ 2) :=
  GroundStateSourceFixedPairEnergy.fixedBoundaryLeakageEnergy_vacuum_eq_jointLeakageNormSq
    H N hN beta hbeta source target F hF bound hbound

end MGAP4D.MathlibAnalytic
