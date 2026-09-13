import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceOneLinkConditionalExpectation
import Mathlib.Probability.Kernel.Condexp
import Mathlib.Probability.Kernel.CompProdEqIff
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

noncomputable section

local instance continuousVacuumReferenceOneLinkRegularConditionalDistributionSpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance continuousVacuumReferenceOneLinkRegularConditionalDistributionSpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance continuousVacuumReferenceOneLinkRegularConditionalDistributionAmbientMatrixSecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix (Fin N) (Fin N) ℂ) :=
  specialUnitaryAmbientMatrixSecondCountableTopology N

local instance continuousVacuumReferenceOneLinkRegularConditionalDistributionAmbientMatrixIsCompletelyMetrizableSpace
    (N : ℕ) :
    IsCompletelyMetrizableSpace (Matrix (Fin N) (Fin N) ℂ) := by
  change IsCompletelyMetrizableSpace (Fin N → Fin N → ℂ)
  infer_instance

local instance continuousVacuumReferenceOneLinkRegularConditionalDistributionAmbientMatrixPolishSpace
    (N : ℕ) :
    PolishSpace (Matrix (Fin N) (Fin N) ℂ) := by
  infer_instance

local instance continuousVacuumReferenceOneLinkRegularConditionalDistributionSpecialUnitaryPolishSpace
    (N : ℕ) :
    PolishSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  (specialUnitaryGroup_isClosed N).polishSpace

local instance continuousVacuumReferenceOneLinkRegularConditionalDistributionSpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance continuousVacuumReferenceOneLinkRegularConditionalDistributionSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance continuousVacuumReferenceOneLinkRegularConditionalDistributionSpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance continuousVacuumReferenceOneLinkRegularConditionalDistributionSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance continuousVacuumReferenceOneLinkRegularConditionalDistributionReferenceProbabilityMeasure
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
        H N hN beta hbeta B target source k g₂) :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure_isProbabilityMeasure
    H N hN beta hbeta B target source k g₂

/-- The off-fiber reference one-link heat-bath kernel is the regular conditional
probability kernel of the ambient reference law given the off-fiber sigma-algebra,
up to the canonical restricted-law null sets. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkOffFiberHeatBathKernel_ae_eq_condExpKernel
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source fiber : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkOffFiberHeatBathKernel
        H N hN beta hbeta B target source fiber k g₂ =ᵐ[
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
        H N hN beta hbeta B target source k g₂).trim
        (periodicHypercubicEvenSpecialUnitarySpatialSliceOffFiberMeasurableSpace_le H N fiber)]
      ProbabilityTheory.condExpKernel
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
          H N hN beta hbeta B target source k g₂)
        (periodicHypercubicEvenSpecialUnitarySpatialSliceOffFiberMeasurableSpace H N fiber) := by
  let Koff :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkOffFiberHeatBathKernel
      H N hN beta hbeta B target source fiber k g₂
  let μ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
      H N hN beta hbeta B target source k g₂
  let m : MeasurableSpace
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceOffFiberMeasurableSpace H N fiber
  let hle : m ≤ MeasurableSpace.pi := by
    simpa [m] using
      periodicHypercubicEvenSpecialUnitarySpatialSliceOffFiberMeasurableSpace_le H N fiber
  let μoff : @Measure
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) m :=
    μ.trim hle
  have hDiagMeas :
      @Measurable
        (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
        ((PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ×
          (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N))
        MeasurableSpace.pi
        (m.prod MeasurableSpace.pi)
        (fun A => (id A, id A)) :=
    (measurable_id'' hle).prodMk measurable_id
  have hJointKoff :
      μoff ⊗ₘ Koff =
        @Measure.map
          (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
          ((PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ×
            (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N))
          MeasurableSpace.pi
          (m.prod MeasurableSpace.pi)
          (fun A => (id A, id A)) μ := by
    apply Measure.ext_prod
    intro s t hs ht
    rw [Measure.compProd_apply_prod hs ht,
      Measure.map_apply hDiagMeas (hs.prod ht), Set.mk_preimage_prod]
    simp only [preimage_id_eq]
    rw [show μoff = μ.trim hle by rfl,
      setLIntegral_trim hle (Koff.measurable_coe ht) hs]
    simpa [Koff, μ, m, inter_comm] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkOffFiberHeatBathKernel_setLIntegral_eq_inter
        H N hN beta hbeta B target source fiber k g₂ t s ht hs
  have hJointCondExp :
      μoff ⊗ₘ ProbabilityTheory.condExpKernel μ m =
        @Measure.map
          (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
          ((PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ×
            (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N))
          MeasurableSpace.pi
          (m.prod MeasurableSpace.pi)
          (fun A => (id A, id A)) μ := by
    simpa [μoff] using
      (ProbabilityTheory.compProd_trim_condExpKernel (μ := μ) (m := m) hle)
  have hProd :
      μoff ⊗ₘ Koff =
        μoff ⊗ₘ ProbabilityTheory.condExpKernel μ m :=
    hJointKoff.trans hJointCondExp.symm
  have hAE :
      Koff =ᵐ[μoff] ProbabilityTheory.condExpKernel μ m :=
    ProbabilityTheory.Kernel.ae_eq_of_compProd_eq hProd
  simpa [Koff, μ, m, hle, μoff] using hAE

end

end MathlibAnalytic
end MGAP4D
