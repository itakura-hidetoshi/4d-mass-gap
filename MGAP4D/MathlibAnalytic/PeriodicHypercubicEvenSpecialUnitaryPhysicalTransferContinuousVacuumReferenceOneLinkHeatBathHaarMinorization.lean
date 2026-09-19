import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceOneLinkHaarMinorization
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceOneLinkHeatBathKernel
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

local instance referenceOneLinkHeatBathHaarMinorizationSpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance referenceOneLinkHeatBathHaarMinorizationSpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance referenceOneLinkHeatBathHaarMinorizationSpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance referenceOneLinkHeatBathHaarMinorizationSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance referenceOneLinkHeatBathHaarMinorizationSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Configuration-space Haar refresh at one selected spatial link.  The old
value of that link is discarded and replaced by an independent normalized Haar
sample; every other link remains fixed. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHaarRefreshMeasure
    (H N : ℕ)
    (fiber : PeriodicHypercubicEvenSpatialSliceLink H)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    Measure (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :=
  Measure.map
    (fun g : Matrix.specialUnitaryGroup (Fin N) ℂ =>
      Function.update A fiber g)
    (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))

/-- Pointwise form of the full-configuration heat-bath kernel: sample the
literal normalized one-link law, then insert the sampled value into the selected
coordinate. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel_apply_eq_map_fiberProbabilityMeasure
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source fiber : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel
        H N hN beta hbeta B target source fiber k g₂ A =
      Measure.map
        (fun g : Matrix.specialUnitaryGroup (Fin N) ℂ =>
          Function.update A fiber g)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
          H N hN beta hbeta B target source fiber k g₂ A) := by
  ext s hs
  have hUpdate :
      Measurable
        (fun z :
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
            Matrix.specialUnitaryGroup (Fin N) ℂ =>
          Function.update z.1 fiber z.2) :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkUpdate_uncurry_measurable
      H N fiber
  have hReplace :
      Measurable
        (fun g : Matrix.specialUnitaryGroup (Fin N) ℂ =>
          Function.update A fiber g) := by
    exact hUpdate.comp (measurable_const.prodMk measurable_id)
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel,
    Kernel.map_apply' _ hUpdate _ hs,
    Kernel.id_prod_apply' _ A (hUpdate hs),
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkConditionalKernel_apply,
    Measure.map_apply hReplace hs
  ]
  rfl

/-- The actual full-configuration one-link heat-bath update dominates an
explicit configuration-space Haar refresh with the same volume-independent
coefficient as the fiber law.

This is the first Doeblin-form statement on the actual configuration kernel.  It
uses no covariance decay, remote-residual estimate, or sweep contraction. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel_lower_bound_haarRefresh
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source fiber : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    (ENNReal.ofReal (Real.exp (32 * beta)))⁻¹ •
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHaarRefreshMeasure
          H N fiber A ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel
        H N hN beta hbeta B target source fiber k g₂ A := by
  have hReplace :
      Measurable
        (fun g : Matrix.specialUnitaryGroup (Fin N) ℂ =>
          Function.update A fiber g) := by
    exact
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkUpdate_uncurry_measurable
        H N fiber).comp (measurable_const.prodMk measurable_id)
  have hFiber :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_lower_bound_normalizedCompactHaar
      H N hN beta hbeta B target source fiber k g₂ A
  have hMapped :=
    Measure.map_mono hFiber hReplace
  rw [Measure.map_smul _ hReplace] at hMapped
  simpa [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHaarRefreshMeasure,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel_apply_eq_map_fiberProbabilityMeasure
  ] using hMapped

end

end MathlibAnalytic
end MGAP4D
