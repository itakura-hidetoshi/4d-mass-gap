import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourceFixedIntegratedResponse

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped ENNReal

attribute [local instance]
  sourceFixedIntegratedIsTopologicalGroup
  sourceFixedIntegratedCompactSpace
  sourceFixedIntegratedSecondCountableTopology
  sourceFixedIntegratedMeasurableSpace
  sourceFixedIntegratedBorelSpace
  sourceFixedIntegratedSpatialLinkFintype

#check periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedResponseResidualCoefficient_ne_top
#check periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseL2_vacuum_norm_sq_le_orderedCoefficient_mul_canonicalVariance
#check periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseL2_vacuum_norm_sq_le_orderedCoefficient_mul_condExpResidual
#check periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFullDifferenceL2_vacuum_norm_sq_le_orderedCoefficient_mul_condExpResidual_of_sourceInvariant
#check periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2_exists_bounded_representative_integratedResponse

-- Regression: finite ENNReal coefficient extraction needs no measurability premise.
example {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (c : ℝ≥0∞) (hc : c ≠ ⊤) (E : α → ℝ≥0∞) :
    (∫⁻ x, c * E x ∂μ) = c * ∫⁻ x, E x ∂μ :=
  lintegral_const_mul' c E hc

-- Regression: zero genuine target residual forces zero integrated full response.
-- This is an energy statement on the source-pair carrier, not a joint norm identity.
example (N : ℕ) (hN : 0 < N) (s : ℝ) (hs : 1 < s)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hcut : beta ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff s)
    (H : ℕ) (distinguishedSource source target : PeriodicHypercubicEvenSpatialSliceLink H)
    (hne : target ≠ source)
    (F : (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F) (bound : ℝ) (hbound : ∀ z, ‖F z‖ ≤ bound)
    (hInvariant : ∀ (left right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
      (value : Matrix.specialUnitaryGroup (Fin N) ℂ),
      F (left, Function.update right source value) = F (left, right))
    (hFixed : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2 H N hN beta hbeta target
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2 H N hN beta hbeta F hF bound hbound) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2 H N hN beta hbeta F hF bound hbound) :
    (∫⁻ C, ENNReal.ofReal
      (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFullDifferenceL2
        H N hN beta hbeta C distinguishedSource source target
        (C distinguishedSource) (C source) F hF bound hbound C 0‖ ^ 2)
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure H N hN beta hbeta) = 0 := by
  have h :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFullDifferenceL2_vacuum_norm_sq_le_orderedCoefficient_mul_condExpResidual_of_sourceInvariant
      N hN s hs beta hbeta hcut H distinguishedSource source target hne
      F hF bound hbound hInvariant
  apply le_antisymm _ bot_le
  simpa only [hFixed, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0),
    ENNReal.ofReal_zero, mul_zero] using h

end MGAP4D.MathlibAnalytic
