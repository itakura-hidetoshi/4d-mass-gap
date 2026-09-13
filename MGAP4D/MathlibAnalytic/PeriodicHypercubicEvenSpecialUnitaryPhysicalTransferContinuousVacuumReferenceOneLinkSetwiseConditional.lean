import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceOneLinkHeatBathProper
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

noncomputable section

local instance continuousVacuumReferenceOneLinkSetwiseConditionalSpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance continuousVacuumReferenceOneLinkSetwiseConditionalSpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance continuousVacuumReferenceOneLinkSetwiseConditionalSpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance continuousVacuumReferenceOneLinkSetwiseConditionalSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance continuousVacuumReferenceOneLinkSetwiseConditionalSpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance continuousVacuumReferenceOneLinkSetwiseConditionalSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- The off-fiber typed heat-bath kernel has exactly the same stationary
reference probability law as the ambient-source presentation. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkOffFiberHeatBathKernel_comp_referenceProbabilityMeasure
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source fiber : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkOffFiberHeatBathKernel
        H N hN beta hbeta B target source fiber k g₂ ∘ₘ
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
        H N hN beta hbeta B target source k g₂ =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
        H N hN beta hbeta B target source k g₂ := by
  let Koff :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkOffFiberHeatBathKernel
      H N hN beta hbeta B target source fiber k g₂
  let K :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel
      H N hN beta hbeta B target source fiber k g₂
  let μ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
      H N hN beta hbeta B target source k g₂
  let hle :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceOffFiberMeasurableSpace_le
      H N fiber
  ext s hs
  rw [Measure.bind_apply hs (Koff.measurable.mono hle le_rfl).aemeasurable]
  have hStat : (K ∘ₘ μ) s = μ s := by
    simpa [K, μ] using
      congrArg (fun ν : Measure
        (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) => ν s)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel_comp_referenceProbabilityMeasure
          H N hN beta hbeta B target source fiber k g₂)
  rw [Measure.bind_apply hs K.aemeasurable] at hStat
  simpa [Koff, K, μ] using hStat

/-- For every ambient measurable event `Aset` and every event `Bset`
measurable from the off-fiber coordinates, the reference heat-bath transition
probability satisfies the exact defining setwise conditional identity. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkOffFiberHeatBathKernel_setLIntegral_eq_inter
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source fiber : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (Aset Bset : Set
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N))
    (hA : MeasurableSet Aset)
    (hB : MeasurableSet[
      periodicHypercubicEvenSpecialUnitarySpatialSliceOffFiberMeasurableSpace H N fiber] Bset) :
    (∫⁻ A in Bset,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkOffFiberHeatBathKernel
        H N hN beta hbeta B target source fiber k g₂ A Aset
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
        H N hN beta hbeta B target source k g₂) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
        H N hN beta hbeta B target source k g₂ (Aset ∩ Bset) := by
  let Koff :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkOffFiberHeatBathKernel
      H N hN beta hbeta B target source fiber k g₂
  let μ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
      H N hN beta hbeta B target source k g₂
  let hle :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceOffFiberMeasurableSpace_le
      H N fiber
  have hProper : Kernel.IsProper Koff := by
    simpa [Koff] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkOffFiberHeatBathKernel_isProper
        H N hN beta hbeta B target source fiber k g₂
  calc
    (∫⁻ A in Bset,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkOffFiberHeatBathKernel
          H N hN beta hbeta B target source fiber k g₂ A Aset
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
          H N hN beta hbeta B target source k g₂) =
      (Koff ∘ₘ μ) (Aset ∩ Bset) := by
        simpa [Koff, μ] using
          hProper.setLIntegral_eq_comp hle hA hB
    _ = μ (Aset ∩ Bset) := by
      have hStat : Koff ∘ₘ μ = μ := by
        simpa [Koff, μ] using
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkOffFiberHeatBathKernel_comp_referenceProbabilityMeasure
            H N hN beta hbeta B target source fiber k g₂
      exact congrArg (fun ν : Measure
        (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) => ν (Aset ∩ Bset)) hStat
    _ = periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
        H N hN beta hbeta B target source k g₂ (Aset ∩ Bset) := by
      rfl

end

end MathlibAnalytic
end MGAP4D
