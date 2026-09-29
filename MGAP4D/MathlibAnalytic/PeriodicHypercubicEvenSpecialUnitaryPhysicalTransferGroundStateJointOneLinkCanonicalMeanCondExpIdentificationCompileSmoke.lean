import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointOneLinkCanonicalMeanCondExpIdentification

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped ENNReal

#check realL2_condExp_eq_of_residual_norm_sq_le
#check GroundStateCanonicalMean.canonicalMeanL2_eq_condExpL2
#check GroundStateCanonicalMean.condExpL2_coeFn_eq_canonicalMean
#check GroundStateCanonicalMean.canonicalResidualL2_eq_condExpResidual
#check GroundStateCanonicalMean.canonicalVariance_eq_condExpResidualNormSq

-- The comparison is in the reverse direction to projection minimality.
-- No finite-measure hypothesis is needed by the Hilbert-space argument.
example {α : Type*} [m0 : MeasurableSpace α] {m : MeasurableSpace α}
    (μ : Measure α) (hm : m ≤ m0) (f g : Lp ℝ 2 μ)
    (hg : AEStronglyMeasurable[m] (fun a => g a) μ)
    (hle : ‖f - g‖ ^ 2 ≤ ‖f - (condExpL2 ℝ ℝ hm f : Lp ℝ 2 μ)‖ ^ 2) :
    (condExpL2 ℝ ℝ hm f : Lp ℝ 2 μ) = g :=
  realL2_condExp_eq_of_residual_norm_sq_le hm f g hg hle

attribute [local instance]
  groundStateJointOneLinkBoundedCoreSpecialUnitaryIsTopologicalGroup
  groundStateJointOneLinkBoundedCoreSpecialUnitaryCompactSpace
  groundStateJointOneLinkBoundedCoreSpecialUnitarySecondCountableTopology
  groundStateJointOneLinkBoundedCoreSpecialUnitaryMeasurableSpace
  groundStateJointOneLinkBoundedCoreSpecialUnitaryBorelSpace
  groundStateJointOneLinkBoundedCoreSpatialLinkFintype
  groundStateJointOneLinkBoundedCoreTargetLinkFintype
  groundStateJointOneLinkBoundedCoreTargetLinkUnique

-- The actual variance identity is an equality, for every beta >= 0.
-- No remote source, cutoff, source-invariance or new energy hypothesis.
example (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F : (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F) (bound : ℝ) (hbound : ∀ z, ‖F z‖ ≤ bound) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberVarianceFunctional
      H N hN beta hbeta target F =
    ENNReal.ofReal (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
      H N hN beta hbeta F hF bound hbound -
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
        H N hN beta hbeta target
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
          H N hN beta hbeta F hF bound hbound)‖ ^ 2) :=
  GroundStateCanonicalMean.canonicalVariance_eq_condExpResidualNormSq
    H N hN beta hbeta target F hF bound hbound

end MGAP4D.MathlibAnalytic
