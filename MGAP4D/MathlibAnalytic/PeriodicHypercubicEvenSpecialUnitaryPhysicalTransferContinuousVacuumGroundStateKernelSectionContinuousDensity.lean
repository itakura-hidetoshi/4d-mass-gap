import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumGroundStateKernelSectionProbability
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal

noncomputable section

local instance physicalContinuousVacuumGroundStateKernelSectionContinuousDensitySpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

/-- Pointwise continuous version of the fixed-right left kernel-section weight.
It uses the canonical continuous vacuum representative rather than the original
`L²` representative. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousWeight
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (C A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) : ℝ :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
      H N hN beta hbeta A *
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta A C

/-- The original `L²`-representative kernel-section weight and the pointwise
continuous kernel-section weight agree Haar-almost everywhere on the complete
left boundary configuration space.

This is deliberately a global a.e. statement.  It is not restricted to an
arbitrary one-link fiber, so no invalid passage from product-a.e. equality to
every section is made. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionWeight_ae_eq_continuousWeight
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionWeight
        H N hN beta hbeta C =ᵐ[
      periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N]
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousWeight
        H N hN beta hbeta C := by
  filter_upwards [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_ae_eq_existing
      H N hN beta hbeta] with A hOmega
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionWeight
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousWeight
  rw [hOmega]

/-- Normalize the pointwise continuous fixed-right kernel section.  This is only
a weighted probability law on the complete left boundary; it is not asserted
to be a regular conditional distribution. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    Measure (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :=
  realIntegralWeightedProbabilityMeasure
    (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousWeight
      H N hN beta hbeta C)

/-- Replacing the old `L²` representative by the canonical continuous vacuum
representative does not change the normalized fixed-right kernel-section
probability measure. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionProbabilityMeasure_eq_continuous
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionProbabilityMeasure
        H N hN beta hbeta C =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
        H N hN beta hbeta C := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let wEig :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionWeight
      H N hN beta hbeta C
  let wCont :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousWeight
      H N hN beta hbeta C
  have hReal : wEig =ᵐ[μ] wCont := by
    simpa [μ, wEig, wCont] using
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionWeight_ae_eq_continuousWeight
        H N hN beta hbeta C)
  have hWeight :
      (fun A => ENNReal.ofReal (wEig A)) =ᵐ[μ]
        (fun A => ENNReal.ofReal (wCont A)) := by
    filter_upwards [hReal] with A hA
    rw [hA]
  have hMass :
      doobWeightMass μ (fun A => ENNReal.ofReal (wEig A)) =
        doobWeightMass μ (fun A => ENNReal.ofReal (wCont A)) := by
    simpa [doobWeightMass] using lintegral_congr_ae hWeight
  change
    doobWeightedMeasure μ (fun A => ENNReal.ofReal (wEig A)) =
      doobWeightedMeasure μ (fun A => ENNReal.ofReal (wCont A))
  unfold doobWeightedMeasure
  apply withDensity_congr_ae
  filter_upwards [hWeight] with A hA
  simp only [doobWeightedDensity]
  rw [hA, hMass]

/-- Hence the continuous-density presentation is a genuine probability measure
with exactly the same normalization as the already validated kernel-section
law. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure_isProbabilityMeasure
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
        H N hN beta hbeta C) := by
  rw [←
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionProbabilityMeasure_eq_continuous
      H N hN beta hbeta C]
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionProbabilityMeasure_isProbabilityMeasure
      H N hN beta hbeta C

end

end MathlibAnalytic
end MGAP4D
