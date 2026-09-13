import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumSameColorSourceRatioLocalization
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

local instance physicalContinuousVacuumReferenceWeightSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

/-- Canonical pointwise reference weight underlying the localized physical
continuous-vacuum covariance.  Unlike the preceding integral identity, this
uses the canonical continuous vacuum representative rather than an arbitrary
`L²` representative. -/
def periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) : ℝ :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
      H N hN beta hbeta A *
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
      H N beta A B target g₂ *
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
      H N beta A (Function.update B source k)

/-- The canonical continuous-vacuum reference weight is strictly positive at
every left-boundary configuration. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight_pos
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    0 < periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight
      H N hN beta hbeta B target source k g₂ A := by
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight
  exact mul_pos
    (mul_pos
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_pos
        H N hN beta hbeta A)
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_pos
        H N beta A B target g₂))
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_pos
      H N beta A (Function.update B source k))

/-- Weighted covariance numerators depend only on the almost-everywhere class
of their reference weight. -/
theorem realIntegralWeightedCovarianceNumerator_congr_weight_ae
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α)
    (w₁ w₂ f g : α → ℝ)
    (hw : w₁ =ᵐ[μ] w₂) :
    realIntegralWeightedCovarianceNumerator μ w₁ f g =
      realIntegralWeightedCovarianceNumerator μ w₂ f g := by
  unfold realIntegralWeightedCovarianceNumerator
  have hMass : (∫ x, w₁ x ∂μ) = ∫ x, w₂ x ∂μ :=
    integral_congr_ae hw
  have hJoint :
      (∫ x, w₁ x * (f x * g x) ∂μ) =
        ∫ x, w₂ x * (f x * g x) ∂μ := by
    apply integral_congr_ae
    filter_upwards [hw] with x hx
    rw [hx]
  have hLeft :
      (∫ x, w₁ x * f x ∂μ) = ∫ x, w₂ x * f x ∂μ := by
    apply integral_congr_ae
    filter_upwards [hw] with x hx
    rw [hx]
  have hRight :
      (∫ x, w₁ x * g x ∂μ) = ∫ x, w₂ x * g x ∂μ := by
    apply integral_congr_ae
    filter_upwards [hw] with x hx
    rw [hx]
  rw [hMass, hJoint, hLeft, hRight]

/-- The `L²`-representative reference weight used in the preceding covariance
localization can be replaced exactly by the canonical pointwise continuous
physical vacuum.  This is the measure-theoretic bridge needed before defining
a genuine normalized reference probability law. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight_weightedCovarianceNumerator_eq
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (f g : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ) :
    realIntegralWeightedCovarianceNumerator
        (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)
        (fun A =>
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
              H N hN beta hbeta).1 A *
            periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
              H N beta A B target g₂ *
            periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
              H N beta A (Function.update B source k))
        f g =
      realIntegralWeightedCovarianceNumerator
        (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight
          H N hN beta hbeta B target source k g₂)
        f g := by
  rfl

end

end MathlibAnalytic
end MGAP4D
