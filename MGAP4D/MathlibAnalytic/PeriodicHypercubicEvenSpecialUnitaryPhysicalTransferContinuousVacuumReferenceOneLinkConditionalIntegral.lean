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
  let hle :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceOffFiberMeasurableSpace_le
      H N fiber
  let μBoff : @Measure
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
      (periodicHypercubicEvenSpecialUnitarySpatialSliceOffFiberMeasurableSpace H N fiber) :=
    (μ.restrict Bset).trim hle
  have hRestricted : Koff ∘ₘ μ.restrict Bset = μ.restrict Bset := by
    simpa [Koff, μ] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkOffFiberHeatBathKernel_comp_restrict_referenceProbabilityMeasure
        H N hN beta hbeta B target source fiber k g₂ Bset hB
  have hfRestr : Integrable f (μ.restrict Bset) := by
    simpa [μ] using (hf.restrict (s := Bset))
  have hCompTrim :
      (Koff ∘ₖ Kernel.const Unit μBoff) () = Koff ∘ₘ μ.restrict Bset := by
    ext s hs
    rw [Kernel.comp_apply' _ _ _ hs, Kernel.const_apply,
      Measure.bind_apply hs (Koff.measurable.mono hle le_rfl).aemeasurable]
    simpa [μBoff] using
      (lintegral_trim hle (Koff.measurable_coe hs))
  have hKernelStat :
      (Koff ∘ₖ Kernel.const Unit μBoff) () = μ.restrict Bset :=
    hCompTrim.trans hRestricted
  have hfKernelComp :
      Integrable f ((Koff ∘ₖ Kernel.const Unit μBoff) ()) := by
    rw [hKernelStat]
    exact hfRestr
  have hFubini :=
    ProbabilityTheory.integral_comp
      (κ := Kernel.const Unit μBoff)
      (η := Koff)
      (a := ())
      hfKernelComp
  have hFubiniOff :
      (∫ C, f C ∂((Koff ∘ₖ Kernel.const Unit μBoff) ())) =
        ∫ A, (∫ C, f C ∂Koff A) ∂μBoff := by
    simpa only [Kernel.const_apply] using hFubini
  have hgOff :
      Integrable (fun A => ∫ C, f C ∂Koff A) μBoff := by
    simpa only [Kernel.const_apply] using hfKernelComp.integral_comp
  have hOuterTrim :
      (∫ A, (∫ C, f C ∂Koff A) ∂μ.restrict Bset) =
        ∫ A, (∫ C, f C ∂Koff A) ∂μBoff := by
    simpa [μBoff] using
      (integral_trim_ae hle hgOff.aestronglyMeasurable)
  have hFinal :
      (∫ A, (∫ C, f C ∂Koff A) ∂μ.restrict Bset) =
        ∫ A, f A ∂μ.restrict Bset := by
    calc
      (∫ A, (∫ C, f C ∂Koff A) ∂μ.restrict Bset) =
          ∫ A, (∫ C, f C ∂Koff A) ∂μBoff := hOuterTrim
      _ = ∫ C, f C ∂((Koff ∘ₖ Kernel.const Unit μBoff) ()) := hFubiniOff.symm
      _ = ∫ C, f C ∂μ.restrict Bset := by rw [hKernelStat]
  simpa [Koff, μ] using hFinal

end

end MathlibAnalytic
end MGAP4D
