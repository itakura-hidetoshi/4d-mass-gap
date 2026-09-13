import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceProbability
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped ENNReal

noncomputable section

local instance continuousVacuumReferenceOneLinkFiberSpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance continuousVacuumReferenceOneLinkFiberSpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance continuousVacuumReferenceOneLinkFiberSpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance continuousVacuumReferenceOneLinkFiberSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance continuousVacuumReferenceOneLinkFiberSpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance continuousVacuumReferenceOneLinkFiberSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Literal restriction of the normalized-reference weight to one spatial-link
fiber.  This is a pointwise density on the inserted `SU(N)` coordinate; no RCD
identification is asserted at this layer. -/
def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberWeight
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source fiber : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) : ℝ :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight
    H N hN beta hbeta B target source k g₂
    (periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink
      H N A fiber g)

/-- The literal continuous-vacuum reference density stays strictly positive on
every spatial one-link fiber. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberWeight_pos
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source fiber : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    0 <
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberWeight
        H N hN beta hbeta B target source fiber k g₂ A g := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberWeight
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight_pos
      H N hN beta hbeta B target source k g₂
      (periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink
        H N A fiber g)

/-- Along one selected spatial coordinate the complete reference weight is a
continuous real function of the inserted `SU(N)` value.  This is deliberately
a fiber-local continuity statement; no full-configuration product-continuity
theorem is introduced. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberWeight_continuous
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source fiber : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    Continuous
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberWeight
        H N hN beta hbeta B target source fiber k g₂ A) := by
  let replace : Matrix.specialUnitaryGroup (Fin N) ℂ →
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N :=
    fun g =>
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink
        H N A fiber g
  have hReplace : Continuous replace := by
    simpa [replace] using
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink_continuous
        H N A fiber
  have hOmega : Continuous
      (fun g : Matrix.specialUnitaryGroup (Fin N) ℂ =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
          H N hN beta hbeta (replace g)) :=
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_continuous
      H N hN beta hbeta).comp hReplace
  have hLocal : Continuous
      (fun g : Matrix.specialUnitaryGroup (Fin N) ℂ =>
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
          H N beta (replace g) B target g₂) :=
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_continuous_left
      H N beta B target g₂).comp hReplace
  have hKernel : Continuous
      (fun g : Matrix.specialUnitaryGroup (Fin N) ℂ =>
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          H N beta (replace g) (Function.update B source k)) :=
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_continuous
      H N beta).comp
      (hReplace.prodMk continuous_const)
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberWeight
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight
  simpa [replace] using (hOmega.mul hLocal).mul hKernel

/-- The literal reference density is Haar-integrable on every selected
one-link fiber.  Compactness is used only after restricting to that one
coordinate. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberWeight_integrable
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source fiber : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    Integrable
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberWeight
        H N hN beta hbeta B target source fiber k g₂ A)
      (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)) := by
  exact
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberWeight_continuous
      H N hN beta hbeta B target source fiber k g₂ A).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

/-- Real normalizing mass of the literal reference weight on one selected
spatial-link fiber. -/
def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberPartitionFunction
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source fiber : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) : ℝ :=
  ∫ g,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberWeight
      H N hN beta hbeta B target source fiber k g₂ A g
    ∂normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)

/-- Every literal one-link reference fiber has strictly positive normalizing
mass. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberPartitionFunction_pos
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source fiber : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    0 <
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberPartitionFunction
        H N hN beta hbeta B target source fiber k g₂ A := by
  let μ := normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)
  let w :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberWeight
      H N hN beta hbeta B target source fiber k g₂ A
  have hwNonneg : 0 ≤ w := fun g =>
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberWeight_pos
      H N hN beta hbeta B target source fiber k g₂ A g).le
  have hwInt : Integrable w μ := by
    simpa [μ, w] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberWeight_integrable
        H N hN beta hbeta B target source fiber k g₂ A
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberPartitionFunction
  change 0 < ∫ g, w g ∂μ
  rw [integral_pos_iff_support_of_nonneg hwNonneg hwInt]
  have hsupp : Function.support w = Set.univ := by
    ext g
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    exact
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberWeight_pos
        H N hN beta hbeta B target source fiber k g₂ A g).ne'
  rw [hsupp]
  simp [μ]

/-- Normalized probability law associated with the literal one-coordinate
restriction of the continuous-vacuum reference weight.  At this layer it is a
normalized fiber density; identification as a conditional distribution of the
full reference law is deferred to the split/Fubini compatibility theorem. -/
def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source fiber : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    Measure (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  realIntegralWeightedProbabilityMeasure
    (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberWeight
      H N hN beta hbeta B target source fiber k g₂ A)

/-- The normalized literal one-link reference fiber has total mass one. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_isProbabilityMeasure
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source fiber : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
        H N hN beta hbeta B target source fiber k g₂ A) := by
  apply realIntegralWeightedProbabilityMeasure_isProbabilityMeasure
  · exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberWeight_integrable
        H N hN beta hbeta B target source fiber k g₂ A
  · exact ae_of_all _ fun g =>
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberWeight_pos
        H N hN beta hbeta B target source fiber k g₂ A g).le
  · simpa [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberPartitionFunction] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberPartitionFunction_pos
        H N hN beta hbeta B target source fiber k g₂ A

end

end MathlibAnalytic
end MGAP4D
