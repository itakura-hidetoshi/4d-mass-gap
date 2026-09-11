import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumFiberDistortion
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open ProbabilityTheory
open scoped ENNReal

noncomputable section

local instance continuousVacuumDoobVarianceSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

/-- The one-link Doob law obtained by reweighting an arbitrary raw probability
law with the canonical continuous physical Wilson vacuum.

Unlike the earlier quotient-representative construction, the density here is a
genuine pointwise continuous function on the `SU(N)` fiber. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumSpatialLinkDoobMeasure
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (nu : Measure (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    Measure (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  doobWeightedMeasure nu
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumSpatialLinkFiberWeight
      H N hN beta hbeta A target)

/-- The local Harnack theorem completely discharges the one-link density
hypotheses required by the generic Doob variance comparison.

There is no remaining fiber-distortion assumption: the lower and upper density
bounds are constructed canonically from the physical continuous vacuum itself.
The only loss is the explicit ratio of the Harnack endpoints. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumSpatialLinkDoob_evariance_lower_bound
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (nu : Measure (Matrix.specialUnitaryGroup (Fin N) ℂ))
    [IsProbabilityMeasure nu]
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (X : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ)
    (hX : MemLp X 2 nu) :
    let omega :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
        H N hN beta hbeta
    let R : ℝ := Real.exp (8 * beta)
    let m : ℝ≥0∞ := ENNReal.ofReal (omega A / R)
    let M : ℝ≥0∞ := ENNReal.ofReal (R * omega A)
    (m / M) * evariance X nu ≤
      evariance X
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumSpatialLinkDoobMeasure
          H N hN beta hbeta nu A target) := by
  dsimp only
  let D :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumSpatialLinkFiberDistortionData
      H N hN beta hbeta nu A target
  have h := doobWeightedMeasure_evariance_lower_bound
    nu
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumSpatialLinkFiberWeight
      H N hN beta hbeta A target)
    X D.m D.M D.measurable D.lower_pos D.upper_finite D.lower D.upper hX
  simpa [D,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumSpatialLinkDoobMeasure,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumSpatialLinkFiberDistortionData]
    using h

/-- The continuous-vacuum Doob law is automatically a probability measure.
This is the normalization receipt needed by subsequent conditional-expectation
and Poincare layers. -/
noncomputable instance
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumSpatialLinkDoobMeasure_isProbability
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (nu : Measure (Matrix.specialUnitaryGroup (Fin N) ℂ))
    [IsProbabilityMeasure nu]
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumSpatialLinkDoobMeasure
        H N hN beta hbeta nu A target) := by
  let D :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumSpatialLinkFiberDistortionData
      H N hN beta hbeta nu A target
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumSpatialLinkDoobMeasure
  exact doobWeightedMeasure_isProbabilityMeasure_of_bounds
    nu
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumSpatialLinkFiberWeight
      H N hN beta hbeta A target)
    D.m D.M D.measurable D.lower_pos D.upper_finite D.lower D.upper

end

end MathlibAnalytic
end MGAP4D
