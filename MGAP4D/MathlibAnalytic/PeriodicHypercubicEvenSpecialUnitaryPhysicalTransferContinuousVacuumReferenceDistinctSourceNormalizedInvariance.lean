import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceDistinctSourceScalarFactor
import MGAP4D.MathlibAnalytic.RealIntegralWeightedProbabilityScalarNormalization
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal

noncomputable section

local instance referenceDistinctSourceNormalizedInvarianceSpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance referenceDistinctSourceNormalizedInvarianceSpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance referenceDistinctSourceNormalizedInvarianceSpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance referenceDistinctSourceNormalizedInvarianceSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance referenceDistinctSourceNormalizedInvarianceSpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance referenceDistinctSourceNormalizedInvarianceSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- The exact fiber-independent scalar carried by a right-boundary source
replacement once the source link is distinct from the selected left fiber. -/
def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkDistinctSourceScalar
    (H N : ℕ)
    (beta : ℝ)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (source : PeriodicHypercubicEvenSpatialSliceLink H)
    (k : Matrix.specialUnitaryGroup (Fin N) ℂ) : ℝ :=
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
    H N beta A B source k

/-- The common C5 one-link fiber weight after removing the distinct-source
scalar.  It contains the continuous-vacuum factor, target-local factor, and the
unmodified one-slab kernel. -/
def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkDistinctSourceBaseFiberWeight
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target fiber : PeriodicHypercubicEvenSpatialSliceLink H)
    (g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) : ℝ :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkCommonTargetWeight
      H N hN beta hbeta B target fiber g₂ A g *
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
      H N beta
      (periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink
        H N A fiber g)
      B

/-- For a source distinct from the selected fiber, each source-sensitive kernel
is individually a positive fiber-independent scalar times the same unmodified
one-slab kernel. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkSourceKernel_eq_distinctSourceScalar_mul_baseKernel
    (H N : ℕ)
    (beta : ℝ)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (source fiber : PeriodicHypercubicEvenSpatialSliceLink H)
    (k : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (hNe : source ≠ fiber) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkSourceKernel
        H N beta B source fiber k A g =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkDistinctSourceScalar
          H N beta A B source k *
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          H N beta
          (periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink
            H N A fiber g)
          B := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkSourceKernel
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkDistinctSourceScalar
  rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_update_right_eq_localFactor_mul]
  rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_continuousVacuumReplaceLink_eq_of_source_ne_fiber
    H N beta A B source fiber k g hNe]

/-- The distinct-source scalar is strictly positive; this is inherited from the
exact local Boltzmann factor and introduces no new positivity axiom. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkDistinctSourceScalar_pos
    (H N : ℕ)
    (beta : ℝ)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (source : PeriodicHypercubicEvenSpatialSliceLink H)
    (k : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    0 <
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkDistinctSourceScalar
        H N beta A B source k := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkDistinctSourceScalar
  exact periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_pos
    H N beta A B source k

/-- The common base fiber weight is integrable.  This is not a new analytic
estimate: choosing the unchanged source value `B source` turns the already
integrable literal C5 fiber weight into exactly this base weight. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkDistinctSourceBaseFiberWeight_integrable
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source fiber : PeriodicHypercubicEvenSpatialSliceLink H)
    (g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    Integrable
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkDistinctSourceBaseFiberWeight
        H N hN beta hbeta B target fiber g₂ A)
      (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)) := by
  have hInt :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberWeight_integrable
      H N hN beta hbeta B target source fiber (B source) g₂ A
  have hUpdate : Function.update B source (B source) = B := by
    exact Function.update_eq_self source B
  simpa [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkDistinctSourceBaseFiberWeight,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkCommonTargetWeight,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberWeight,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight,
    hUpdate] using hInt

/-- For distinct source and fiber, the full literal C5 fiber weight is exactly a
positive source scalar times one common base fiber weight. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberWeight_eq_distinctSourceScalar_mul_baseFiberWeight
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source fiber : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (hNe : source ≠ fiber) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberWeight
        H N hN beta hbeta B target source fiber k g₂ A =
      fun g =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkDistinctSourceScalar
            H N beta A B source k *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkDistinctSourceBaseFiberWeight
            H N hN beta hbeta B target fiber g₂ A g := by
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberWeight_eq_commonTargetWeight_mul_sourceKernel]
  funext g
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkSourceKernel_eq_distinctSourceScalar_mul_baseKernel
    H N beta B source fiber k A g hNe]
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkDistinctSourceBaseFiberWeight
  ring

/-- The exact C5 fiber partition function scales by the same distinct-source
scalar.  This is the normalization-mass counterpart of the pointwise weight
factorization. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberPartitionFunction_eq_distinctSourceScalar_mul_baseIntegral
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source fiber : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (hNe : source ≠ fiber) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberPartitionFunction
        H N hN beta hbeta B target source fiber k g₂ A =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkDistinctSourceScalar
          H N beta A B source k *
        ∫ g,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkDistinctSourceBaseFiberWeight
            H N hN beta hbeta B target fiber g₂ A g
          ∂normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ) := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberPartitionFunction
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberWeight_eq_distinctSourceScalar_mul_baseFiberWeight
    H N hN beta hbeta B target source fiber k g₂ A hNe]
  rw [integral_const_mul]

/-- Distinct right-boundary source values induce literally the same normalized
C5 one-link fiber law whenever the source link is different from the selected
left fiber.  The equality is at the measure level, before taking expectations
or defining an influence coefficient. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_eq_of_source_ne_fiber
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source fiber : PeriodicHypercubicEvenSpatialSliceLink H)
    (k₁ k₂ g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (hNe : source ≠ fiber) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
        H N hN beta hbeta B target source fiber k₁ g₂ A =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
        H N hN beta hbeta B target source fiber k₂ g₂ A := by
  let μ := normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)
  let w :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkDistinctSourceBaseFiberWeight
      H N hN beta hbeta B target fiber g₂ A
  have hwInt : Integrable w μ := by
    simpa [μ, w] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkDistinctSourceBaseFiberWeight_integrable
        H N hN beta hbeta B target source fiber g₂ A
  have hwAE : AEMeasurable w μ :=
    hwInt.aestronglyMeasurable.aemeasurable
  have hc₁ :
      0 < periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkDistinctSourceScalar
        H N beta A B source k₁ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkDistinctSourceScalar_pos
      H N beta A B source k₁
  have hc₂ :
      0 < periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkDistinctSourceScalar
        H N beta A B source k₂ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkDistinctSourceScalar_pos
      H N beta A B source k₂
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberWeight_eq_distinctSourceScalar_mul_baseFiberWeight
    H N hN beta hbeta B target source fiber k₁ g₂ A hNe]
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberWeight_eq_distinctSourceScalar_mul_baseFiberWeight
    H N hN beta hbeta B target source fiber k₂ g₂ A hNe]
  change
    realIntegralWeightedProbabilityMeasure μ
        (fun g =>
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkDistinctSourceScalar
              H N beta A B source k₁ * w g) =
      realIntegralWeightedProbabilityMeasure μ
        (fun g =>
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkDistinctSourceScalar
              H N beta A B source k₂ * w g)
  rw [realIntegralWeightedProbabilityMeasure_const_mul
    μ w
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkDistinctSourceScalar
      H N beta A B source k₁)
    hwAE hc₁]
  rw [realIntegralWeightedProbabilityMeasure_const_mul
    μ w
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkDistinctSourceScalar
      H N beta A B source k₂)
    hwAE hc₂]

end

end MathlibAnalytic
end MGAP4D
