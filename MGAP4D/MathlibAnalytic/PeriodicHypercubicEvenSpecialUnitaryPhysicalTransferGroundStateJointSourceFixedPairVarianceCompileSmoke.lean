import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourceFixedPairVariance

namespace MGAP4D.MathlibAnalytic

open MeasureTheory ProbabilityTheory
open GroundStateSourceFixedPairEnergy

#check targetMean_stronglyMeasurable
#check targetMean_sourceSection_memLp_two
#check sourceVariance_eq_centeredSourceEnergy
#check pairEnergy_eq_two_mul_sourceVariance
#check sourceVariance_eq_half_pairEnergy
#check vacuumSourceVarianceEnergy_eq_half_pairEnergy
#check vacuumSourceVarianceEnergy_le_half_orderedCoefficient_mul_condExpResidual_of_sourceInvariant
#check exists_sourceUpdate_representative_vacuumSourceVarianceEnergy_bound

-- Exact normalization under arbitrary probability laws, not only a finite probe.
example {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] (X : α → ℝ) (hX : MemLp X 2 μ) :
    (1 / 2 : ℝ) * (∫ z : α × α, (X z.1 - X z.2) ^ 2 ∂μ.prod μ) =
      variance X μ := by
  rw [iid_sqDifference_integral_eq_two_mul_variance μ X hX]
  ring

-- A positive variance rejects the incorrect coefficient-one normalization.
example {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] (X : α → ℝ) (hX : MemLp X 2 μ)
    (hpos : 0 < variance X μ) :
    (∫ z : α × α, (X z.1 - X z.2) ^ 2 ∂μ.prod μ) ≠ variance X μ := by
  rw [iid_sqDifference_integral_eq_two_mul_variance μ X hX]
  linarith

end MGAP4D.MathlibAnalytic
