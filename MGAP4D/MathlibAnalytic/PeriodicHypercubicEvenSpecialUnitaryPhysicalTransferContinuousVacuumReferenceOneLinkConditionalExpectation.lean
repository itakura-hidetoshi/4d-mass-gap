import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceOneLinkConditionalIntegral
import Mathlib.Probability.ConditionalExpectation
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

noncomputable section

local instance continuousVacuumReferenceOneLinkConditionalExpectationSpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance continuousVacuumReferenceOneLinkConditionalExpectationSpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance continuousVacuumReferenceOneLinkConditionalExpectationSpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance continuousVacuumReferenceOneLinkConditionalExpectationSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance continuousVacuumReferenceOneLinkConditionalExpectationSpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance continuousVacuumReferenceOneLinkConditionalExpectationSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- The off-fiber one-link heat-bath integral is a genuine representative of the conditional
expectation onto the off-fiber sigma-algebra for every integrable real observable. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkOffFiberHeatBathKernel_ae_eq_condExp
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
        H N hN beta hbeta B target source k g₂)) :
    (fun A =>
      ∫ C, f C ∂
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkOffFiberHeatBathKernel
          H N hN beta hbeta B target source fiber k g₂ A) =ᵐ[
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
        H N hN beta hbeta B target source k g₂]
      MeasureTheory.condExp
        (periodicHypercubicEvenSpecialUnitarySpatialSliceOffFiberMeasurableSpace H N fiber)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
          H N hN beta hbeta B target source k g₂)
        f := by
  let Koff :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkOffFiberHeatBathKernel
      H N hN beta hbeta B target source fiber k g₂
  let μ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
      H N hN beta hbeta B target source k g₂
  letI : IsProbabilityMeasure μ := by
    simpa [μ] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure_isProbabilityMeasure
        H N hN beta hbeta B target source k g₂
  let hle :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceOffFiberMeasurableSpace_le
      H N fiber
  let μoff : @Measure
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
      (periodicHypercubicEvenSpecialUnitarySpatialSliceOffFiberMeasurableSpace H N fiber) :=
    μ.trim hle
  have hStat : Koff ∘ₘ μ = μ := by
    simpa [Koff, μ] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkOffFiberHeatBathKernel_comp_referenceProbabilityMeasure
        H N hN beta hbeta B target source fiber k g₂
  have hCompTrim :
      (Koff ∘ₖ Kernel.const Unit μoff) () = Koff ∘ₘ μ := by
    ext s hs
    rw [Kernel.comp_apply' _ _ _ hs, Kernel.const_apply,
      Measure.bind_apply hs (Koff.measurable.mono hle le_rfl).aemeasurable]
    simpa [μoff] using
      (lintegral_trim hle (Koff.measurable_coe hs))
  have hKernelStat :
      (Koff ∘ₖ Kernel.const Unit μoff) () = μ :=
    hCompTrim.trans hStat
  have hfKernelComp :
      Integrable f ((Koff ∘ₖ Kernel.const Unit μoff) ()) := by
    rw [hKernelStat]
    simpa [μ] using hf
  have hgOff :
      Integrable (fun A => ∫ C, f C ∂Koff A) μoff := by
    simpa only [Kernel.const_apply] using hfKernelComp.integral_comp
  have hg :
      Integrable (fun A => ∫ C, f C ∂Koff A) μ := by
    apply integrable_of_integrable_trim hle
    simpa [μoff] using hgOff
  have hgmTrim :
      AEStronglyMeasurable[
        periodicHypercubicEvenSpecialUnitarySpatialSliceOffFiberMeasurableSpace H N fiber]
        (fun A => ∫ C, f C ∂Koff A) (μ.trim hle) := by
    simpa [μoff] using hgOff.aestronglyMeasurable
  have hgm :
      AEStronglyMeasurable[
        periodicHypercubicEvenSpecialUnitarySpatialSliceOffFiberMeasurableSpace H N fiber]
        (fun A => ∫ C, f C ∂Koff A) μ := by
    exact hgmTrim.of_trim hle
  have hCE :
      (fun A => ∫ C, f C ∂Koff A) =ᵐ[μ]
        MeasureTheory.condExp
          (periodicHypercubicEvenSpecialUnitarySpatialSliceOffFiberMeasurableSpace H N fiber)
          μ f := by
    refine MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq hle hf ?_ ?_ hgm
    · intro s _ _
      exact hg.integrableOn
    · intro s hs _
      simpa [Koff, μ] using
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkOffFiberHeatBathKernel_setIntegral_integral_eq
          H N hN beta hbeta B target source fiber k g₂ f hf s hs
  simpa [Koff, μ] using hCE

end

end MathlibAnalytic
end MGAP4D
