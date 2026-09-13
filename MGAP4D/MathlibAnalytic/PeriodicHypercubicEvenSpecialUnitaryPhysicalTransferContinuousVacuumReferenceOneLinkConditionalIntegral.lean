import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceOneLinkConditionalLIntegral
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

noncomputable section

local instance continuousVacuumReferenceOneLinkConditionalIntegralSpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance continuousVacuumReferenceOneLinkConditionalIntegralSpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance continuousVacuumReferenceOneLinkConditionalIntegralSpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance continuousVacuumReferenceOneLinkConditionalIntegralSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance continuousVacuumReferenceOneLinkConditionalIntegralSpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance continuousVacuumReferenceOneLinkConditionalIntegralSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- For every integrable real observable and every off-fiber measurable event,
the off-fiber heat-bath kernel satisfies the exact conditional Bochner-integral identity. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkOffFiberHeatBathKernel_setIntegral_integral_eq
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source fiber : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (f : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ)
    (hf : Integrable f
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
        H N hN beta hbeta B target source k g₂))
    (Bset : Set
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N))
    (hB : MeasurableSet[
      periodicHypercubicEvenSpecialUnitarySpatialSliceOffFiberMeasurableSpace H N fiber] Bset) :
    (∫ A in Bset,
      (∫ C, f C ∂
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkOffFiberHeatBathKernel
          H N hN beta hbeta B target source fiber k g₂ A)
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
        H N hN beta hbeta B target source k g₂) =
      ∫ A in Bset, f A ∂
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
          H N hN beta hbeta B target source k g₂ := by
  let Koff :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkOffFiberHeatBathKernel
      H N hN beta hbeta B target source fiber k g₂
  let μ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
      H N hN beta hbeta B target source k g₂
  have hRestricted : Koff ∘ₘ μ.restrict Bset = μ.restrict Bset := by
    simpa [Koff, μ] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkOffFiberHeatBathKernel_comp_restrict_referenceProbabilityMeasure
        H N hN beta hbeta B target source fiber k g₂ Bset hB
  have hfRestr : Integrable f (μ.restrict Bset) := by
    simpa [μ] using (hf.restrict (s := Bset))
  have hfComp : Integrable f (Koff ∘ₘ μ.restrict Bset) := by
    rw [hRestricted]
    exact hfRestr
  rw [Measure.comp_eq_comp_const_apply] at hfComp
  have hFubini :=
    ProbabilityTheory.integral_comp
      (κ := Kernel.const Unit (μ.restrict Bset))
      (η := Koff)
      (a := ())
      hfComp
  have hFubiniMeasure :
      (∫ C, f C ∂(Koff ∘ₘ μ.restrict Bset)) =
        ∫ A, (∫ C, f C ∂Koff A) ∂μ.restrict Bset := by
    simpa only [Measure.comp_eq_comp_const_apply, Kernel.const_apply] using hFubini
  have hFinal :
      (∫ A, (∫ C, f C ∂Koff A) ∂μ.restrict Bset) =
        ∫ A, f A ∂μ.restrict Bset := by
    calc
      (∫ A, (∫ C, f C ∂Koff A) ∂μ.restrict Bset) =
          ∫ C, f C ∂(Koff ∘ₘ μ.restrict Bset) := hFubiniMeasure.symm
      _ = ∫ C, f C ∂μ.restrict Bset := by rw [hRestricted]
  simpa [Koff, μ] using hFinal

end

end MathlibAnalytic
end MGAP4D
