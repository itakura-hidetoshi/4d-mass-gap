import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceWeight
import MGAP4D.MathlibAnalytic.RealIntegralWeightedProbabilityNormalization
import Mathlib.MeasureTheory.Integral.CompactlySupported
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped ENNReal

noncomputable section

local instance physicalContinuousVacuumReferenceProbabilitySpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance physicalContinuousVacuumReferenceProbabilitySpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance physicalContinuousVacuumReferenceProbabilitySpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance physicalContinuousVacuumReferenceProbabilitySpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance physicalContinuousVacuumReferenceProbabilitySpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance physicalContinuousVacuumReferenceProbabilitySpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance physicalContinuousVacuumReferenceProbabilityHaarIsProbability
    (H N : ℕ) :
    IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

/-- For fixed right boundary data, the exact target-local Boltzmann factor is
continuous in the left boundary.  The proof avoids reopening its plaquette
formula: strict positivity of the base kernel and the exact update
factorization identify the factor with a quotient of two continuous kernel
sections. -/
theorem
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_continuous_left
    (H N : ℕ)
    (beta : ℝ)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    Continuous
      (fun A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
          H N beta A B target g) := by
  let Bg : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N :=
    Function.update B target g
  have hUpdated : Continuous
      (fun A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta A Bg) := by
    exact
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_continuous H N beta).comp
        (Continuous.prodMk continuous_id continuous_const)
  have hBase : Continuous
      (fun A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta A B) := by
    exact
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_continuous H N beta).comp
        (Continuous.prodMk continuous_id continuous_const)
  have hQuot : Continuous
      (fun A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta A Bg /
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta A B) := by
    exact hUpdated.div hBase fun A =>
      ne_of_gt
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_pos H N beta A B)
  have hEq :
      (fun A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
          H N beta A B target g) =
      (fun A =>
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta A Bg /
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta A B) := by
    funext A
    apply (eq_div_iff
      (ne_of_gt
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_pos H N beta A B))).2
    simpa [Bg] using
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_update_right_eq_localFactor_mul
        H N beta A B target g).symm
  rw [hEq]
  exact hQuot

/-- The canonical physical covariance reference weight is continuous on the
compact left-boundary configuration space. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight_continuous
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    Continuous
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight
        H N hN beta hbeta B target source k g₂) := by
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight
  have hKernel : Continuous
      (fun A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          H N beta A (Function.update B source k)) := by
    exact
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_continuous H N beta).comp
        (Continuous.prodMk continuous_id continuous_const)
  exact
    ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_continuous
        H N hN beta hbeta).mul
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_continuous_left
        H N beta B target g₂)).mul hKernel

/-- The canonical positive reference weight is integrable against spatial Haar
measure by continuity on the compact finite-link configuration space. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight_integrable
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    Integrable
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight
        H N hN beta hbeta B target source k g₂)
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  exact
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight_continuous
      H N hN beta hbeta B target source k g₂).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

/-- Real partition function of the localized continuous-vacuum reference
weight. -/
def periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePartitionFunction
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ) : ℝ :=
  ∫ A,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight
      H N hN beta hbeta B target source k g₂ A
    ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)

/-- The physical reference partition function is strictly positive. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePartitionFunction_pos
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    0 <
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePartitionFunction
        H N hN beta hbeta B target source k g₂ := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let w :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight
      H N hN beta hbeta B target source k g₂
  have hwNonneg : 0 ≤ w := fun A =>
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight_pos
      H N hN beta hbeta B target source k g₂ A).le
  have hwInt : Integrable w μ := by
    simpa [μ, w] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight_integrable
        H N hN beta hbeta B target source k g₂
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePartitionFunction
  change 0 < ∫ A, w A ∂μ
  rw [integral_pos_iff_support_of_nonneg hwNonneg hwInt]
  have hsupp : Function.support w = Set.univ := by
    ext A
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    exact
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight_pos
        H N hN beta hbeta B target source k g₂ A).ne'
  rw [hsupp]
  simp [μ]

/-- Genuine normalized probability law associated with the positive reference
weight `Ω_cont * L_{g₂} * Q_k`. -/
def periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    Measure (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :=
  realIntegralWeightedProbabilityMeasure
    (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight
      H N hN beta hbeta B target source k g₂)

/-- The normalized continuous-vacuum reference law has total mass one. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure_isProbabilityMeasure
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
        H N hN beta hbeta B target source k g₂) := by
  apply realIntegralWeightedProbabilityMeasure_isProbabilityMeasure
  · exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight_integrable
        H N hN beta hbeta B target source k g₂
  · exact ae_of_all _ fun A =>
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight_pos
        H N hN beta hbeta B target source k g₂ A).le
  · simpa [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePartitionFunction] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePartitionFunction_pos
        H N hN beta hbeta B target source k g₂

/-- The unnormalized physical covariance numerator is exactly `Z²` times the
ordinary covariance under the normalized continuous-vacuum reference law. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight_weightedCovarianceNumerator_eq_partition_sq_mul_probabilityCovariance
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
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight
          H N hN beta hbeta B target source k g₂)
        f g =
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePartitionFunction
        H N hN beta hbeta B target source k g₂) ^ 2 *
      realIntegralCovariance
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
          H N hN beta hbeta B target source k g₂)
        f g := by
  simpa [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePartitionFunction,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure] using
    (realIntegralWeightedCovarianceNumerator_eq_mass_sq_mul_probabilityCovariance
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight
        H N hN beta hbeta B target source k g₂)
      f g
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight_integrable
        H N hN beta hbeta B target source k g₂)
      (ae_of_all _ fun A =>
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight_pos
          H N hN beta hbeta B target source k g₂ A).le)
      (by
        simpa [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePartitionFunction] using
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePartitionFunction_pos
            H N hN beta hbeta B target source k g₂))

/-- The localized same-color remote physical defect is `Z²` times an ordinary
covariance under a genuine probability law whose two observables are already
one-link local.  No Gibbs identification or distance-decay statement is used. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_sameColor_remote_crossRatio_defect_eq_sourceSpatialRatio_mul_partition_sq_mul_referenceProbabilityCovariance
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    {target source : PeriodicHypercubicEvenSpatialSliceLink H}
    (hColor : periodicHypercubicEvenSpatialSliceLinkColor H target =
      periodicHypercubicEvenSpatialSliceLinkColor H source)
    (hne : target ≠ source)
    (h k g₁ g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta‖ *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
          H N hN beta hbeta
          (Function.update (Function.update B source h) target g₁)) *
      (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta‖ *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
          H N hN beta hbeta
          (Function.update (Function.update B source k) target g₂)) -
      (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta‖ *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
          H N hN beta hbeta
          (Function.update (Function.update B source k) target g₁)) *
      (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta‖ *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
          H N hN beta hbeta
          (Function.update (Function.update B source h) target g₂)) =
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetSpatialHalfUpdateFactor
          H N beta B source h /
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetSpatialHalfUpdateFactor
          H N beta B source k) *
      ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePartitionFunction
          H N hN beta hbeta B target source k g₂) ^ 2 *
        realIntegralCovariance
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
            H N hN beta hbeta B target source k g₂)
          (fun A =>
            periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
                H N beta A B target g₁ /
              periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
                H N beta A B target g₂)
          (fun A =>
            specialUnitaryWilsonRelativeKernel N beta (A source) h /
              specialUnitaryWilsonRelativeKernel N beta (A source) k)) := by
  rfl

end

end MathlibAnalytic
end MGAP4D
