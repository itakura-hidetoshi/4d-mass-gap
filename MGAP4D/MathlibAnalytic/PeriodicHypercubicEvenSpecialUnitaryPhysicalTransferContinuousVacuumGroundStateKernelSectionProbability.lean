import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumRemoteNoShareGroundStateKernelSection
import MGAP4D.MathlibAnalytic.RealIntegralWeightedProbabilityNormalization
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

local instance physicalContinuousVacuumGroundStateKernelSectionProbabilitySpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

/-- The fixed-right left kernel section appearing in the remote continuous-C5
covariance localization.  It is the left vacuum representative multiplied by
the literal one-slab Wilson kernel. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionWeight
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (C A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) : ℝ :=
  (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
      H N hN beta hbeta).1 A *
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta A C

/-- The fixed-right ground-state kernel section is Haar-integrable. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionWeight_integrable
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    Integrable
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionWeight
        H N hN beta hbeta C)
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  simpa [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionWeight] using
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_mul_integrable
      H N hN beta hbeta
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
        H N hN beta hbeta).1 C)

/-- The fixed-right ground-state kernel section is nonnegative almost
everywhere. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionWeight_ae_nonnegative
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    ∀ᵐ A ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N),
      0 ≤ periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionWeight
        H N hN beta hbeta C A := by
  have hOmega :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector_ae_nonnegative
      H N hN beta hbeta
  filter_upwards [hOmega] with A hA
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionWeight
  exact mul_nonneg hA
    (le_of_lt
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_pos
        H N beta A C))

/-- The exact total mass of the fixed-right kernel section is the physical
transfer norm times the pointwise continuous-vacuum representative at the
fixed right boundary. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionWeight_integral
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    (∫ A,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionWeight
        H N hN beta hbeta C A
      ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) =
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta‖ *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
          H N hN beta hbeta C := by
  simpa [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionWeight] using
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_topNorm_mul_eq_integral_kernel
      H N hN beta hbeta C).symm

/-- In particular the kernel-section mass is strictly positive at every fixed
right boundary. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionWeight_integral_pos
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    0 <
      ∫ A,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionWeight
          H N hN beta hbeta C A
        ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionWeight_integral
      H N hN beta hbeta C]
  exact mul_pos
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos_from_uniform_kernel_floor
      H N hN beta hbeta)
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_pos
      H N hN beta hbeta C)

/-- Normalize the fixed-right kernel section to a genuine probability measure.
This is a canonical weighted probability law on the left boundary.  No claim
that it is a regular conditional distribution of the ground-state joint law is
made here. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionProbabilityMeasure
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    Measure (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :=
  realIntegralWeightedProbabilityMeasure
    (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionWeight
      H N hN beta hbeta C)

/-- The normalized fixed-right kernel section is an actual probability measure. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionProbabilityMeasure_isProbabilityMeasure
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionProbabilityMeasure
        H N hN beta hbeta C) := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionProbabilityMeasure
  exact
    realIntegralWeightedProbabilityMeasure_isProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionWeight
        H N hN beta hbeta C)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionWeight_integrable
        H N hN beta hbeta C)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionWeight_ae_nonnegative
        H N hN beta hbeta C)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionWeight_integral_pos
        H N hN beta hbeta C)

/-- Unnormalized covariance under a fixed-right ground-state kernel section is
exactly its squared physical mass times covariance under the normalized
kernel-section probability law. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSection_weightedCovarianceNumerator_eq_mass_sq_mul_probabilityCovariance
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (f g : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ) :
    realIntegralWeightedCovarianceNumerator
        (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionWeight
          H N hN beta hbeta C)
        f g =
      (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta‖ *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
          H N hN beta hbeta C) ^ 2 *
      realIntegralCovariance
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionProbabilityMeasure
          H N hN beta hbeta C)
        f g := by
  rw [←
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionWeight_integral
      H N hN beta hbeta C]
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionProbabilityMeasure
  exact
    realIntegralWeightedCovarianceNumerator_eq_mass_sq_mul_probabilityCovariance
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionWeight
        H N hN beta hbeta C)
      f g
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionWeight_integrable
        H N hN beta hbeta C)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionWeight_ae_nonnegative
        H N hN beta hbeta C)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionWeight_integral_pos
        H N hN beta hbeta C)

end

end MathlibAnalytic
end MGAP4D
