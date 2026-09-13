import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceOneLinkSetwiseConditional
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

noncomputable section

local instance continuousVacuumReferenceOneLinkConditionalLIntegralSpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance continuousVacuumReferenceOneLinkConditionalLIntegralSpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance continuousVacuumReferenceOneLinkConditionalLIntegralSpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance continuousVacuumReferenceOneLinkConditionalLIntegralSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance continuousVacuumReferenceOneLinkConditionalLIntegralSpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance continuousVacuumReferenceOneLinkConditionalLIntegralSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Restricting the stationary reference law to any off-fiber measurable
set preserves stationarity for the proper off-fiber heat-bath kernel. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkOffFiberHeatBathKernel_comp_restrict_referenceProbabilityMeasure
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source fiber : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (Bset : Set
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N))
    (hB : MeasurableSet[
      periodicHypercubicEvenSpecialUnitarySpatialSliceOffFiberMeasurableSpace H N fiber] Bset) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkOffFiberHeatBathKernel
        H N hN beta hbeta B target source fiber k g₂ ∘ₘ
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
        H N hN beta hbeta B target source k g₂).restrict Bset =
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
        H N hN beta hbeta B target source k g₂).restrict Bset := by
  let Koff :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkOffFiberHeatBathKernel
      H N hN beta hbeta B target source fiber k g₂
  let μ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
      H N hN beta hbeta B target source k g₂
  let hle :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceOffFiberMeasurableSpace_le
      H N fiber
  ext Aset hA
  rw [Measure.bind_apply hA (Koff.measurable.mono hle le_rfl).aemeasurable,
    Measure.restrict_apply hA]
  simpa [Koff, μ] using
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkOffFiberHeatBathKernel_setLIntegral_eq_inter
      H N hN beta hbeta B target source fiber k g₂ Aset Bset hA hB

/-- The proper off-fiber heat-bath kernel satisfies the conditional
nonnegative integral identity under the reference probability law. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkOffFiberHeatBathKernel_setLIntegral_lintegral_eq
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source fiber : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (f : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ≥0∞)
    (hf : Measurable f)
    (Bset : Set
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N))
    (hB : MeasurableSet[
      periodicHypercubicEvenSpecialUnitarySpatialSliceOffFiberMeasurableSpace H N fiber] Bset) :
    (∫⁻ A in Bset,
      (∫⁻ C, f C ∂
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkOffFiberHeatBathKernel
          H N hN beta hbeta B target source fiber k g₂ A)
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
        H N hN beta hbeta B target source k g₂) =
      ∫⁻ A in Bset, f A ∂
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
          H N hN beta hbeta B target source k g₂ := by
  let Koff :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkOffFiberHeatBathKernel
      H N hN beta hbeta B target source fiber k g₂
  let μ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
      H N hN beta hbeta B target source k g₂
  let hle :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceOffFiberMeasurableSpace_le
      H N fiber
  have hRestricted : Koff ∘ₘ μ.restrict Bset = μ.restrict Bset := by
    simpa [Koff, μ] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkOffFiberHeatBathKernel_comp_restrict_referenceProbabilityMeasure
        H N hN beta hbeta B target source fiber k g₂ Bset hB
  have hIntegral :
      (∫⁻ C, f C ∂(Koff ∘ₘ μ.restrict Bset)) =
        ∫⁻ C, f C ∂μ.restrict Bset := by
    exact congrArg (fun ν : Measure
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) =>
        ∫⁻ C, f C ∂ν) hRestricted
  rw [Measure.lintegral_bind
    (Koff.measurable.mono hle le_rfl).aemeasurable hf.aemeasurable] at hIntegral
  simpa [Koff, μ] using hIntegral

end

end MathlibAnalytic
end MGAP4D
