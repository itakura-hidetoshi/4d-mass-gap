import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceOneLinkRegularConditionalDistribution
import MGAP4D.MathlibAnalytic.DoobWeightedConditionalMeasureCenteredVariance
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

local instance continuousVacuumReferenceOneLinkConditionalVarianceSpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance continuousVacuumReferenceOneLinkConditionalVarianceSpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance continuousVacuumReferenceOneLinkConditionalVarianceAmbientMatrixSecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix (Fin N) (Fin N) ℂ) :=
  specialUnitaryAmbientMatrixSecondCountableTopology N

local instance continuousVacuumReferenceOneLinkConditionalVarianceAmbientMatrixIsCompletelyMetrizableSpace
    (N : ℕ) :
    TopologicalSpace.IsCompletelyMetrizableSpace (Matrix (Fin N) (Fin N) ℂ) := by
  change TopologicalSpace.IsCompletelyMetrizableSpace (Fin N → Fin N → ℂ)
  infer_instance

local instance continuousVacuumReferenceOneLinkConditionalVarianceAmbientMatrixPolishSpace
    (N : ℕ) :
    PolishSpace (Matrix (Fin N) (Fin N) ℂ) := by
  infer_instance

local instance continuousVacuumReferenceOneLinkConditionalVarianceSpecialUnitaryPolishSpace
    (N : ℕ) :
    PolishSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  (specialUnitaryGroup_isClosed N).polishSpace

local instance continuousVacuumReferenceOneLinkConditionalVarianceSpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance continuousVacuumReferenceOneLinkConditionalVarianceSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance continuousVacuumReferenceOneLinkConditionalVarianceSpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance continuousVacuumReferenceOneLinkConditionalVarianceSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance continuousVacuumReferenceOneLinkConditionalVarianceReferenceProbabilityMeasure
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

/-- The best constant fiber residual is invariant under replacing the explicit
off-fiber heat-bath kernel by Mathlib's regular conditional probability kernel. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkOffFiberHeatBathKernel_bestConstantSquaredResidual_ae_eq_condExpKernel
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source fiber : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (X : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ) :
    (fun A =>
      doobBestConstantSquaredResidual
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkOffFiberHeatBathKernel
          H N hN beta hbeta B target source fiber k g₂ A) X) =ᵐ[
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
        H N hN beta hbeta B target source k g₂).trim
        (periodicHypercubicEvenSpecialUnitarySpatialSliceOffFiberMeasurableSpace_le H N fiber)]
      (fun A =>
        doobBestConstantSquaredResidual
          ((ProbabilityTheory.condExpKernel
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
              H N hN beta hbeta B target source k g₂)
            (periodicHypercubicEvenSpecialUnitarySpatialSliceOffFiberMeasurableSpace H N fiber)) A) X) := by
  rfl

/-- Extended conditional variance is invariant under the same RCD replacement. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkOffFiberHeatBathKernel_evariance_ae_eq_condExpKernel
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source fiber : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (X : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ) :
    (fun A =>
      evariance X
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkOffFiberHeatBathKernel
          H N hN beta hbeta B target source fiber k g₂ A)) =ᵐ[
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
        H N hN beta hbeta B target source k g₂).trim
        (periodicHypercubicEvenSpecialUnitarySpatialSliceOffFiberMeasurableSpace_le H N fiber)]
      (fun A =>
        evariance X
          ((ProbabilityTheory.condExpKernel
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
              H N hN beta hbeta B target source k g₂)
            (periodicHypercubicEvenSpecialUnitarySpatialSliceOffFiberMeasurableSpace H N fiber)) A)) := by
  rfl

end

end MathlibAnalytic
end MGAP4D
