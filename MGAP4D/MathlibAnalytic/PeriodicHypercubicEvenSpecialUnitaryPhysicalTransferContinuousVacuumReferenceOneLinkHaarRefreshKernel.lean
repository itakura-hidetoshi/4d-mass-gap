import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceOneLinkHeatBathHaarMinorization
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

local instance referenceOneLinkHaarRefreshKernelSpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance referenceOneLinkHaarRefreshKernelSpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance referenceOneLinkHaarRefreshKernelSpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance referenceOneLinkHaarRefreshKernelSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance referenceOneLinkHaarRefreshKernelSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Markov kernel which independently replaces one selected spatial-link
coordinate by normalized compact Haar and leaves every other coordinate fixed.

This kernel is the actual kernel-level reference object underlying the
configuration-space Haar-refresh measure introduced in the one-link
minorization theorem. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHaarRefreshKernel
    (H N : ℕ)
    (fiber : PeriodicHypercubicEvenSpatialSliceLink H) :
    Kernel
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :=
  (Kernel.id ×ₖ
      Kernel.const
        (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
        (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))).map
    (fun z :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        Matrix.specialUnitaryGroup (Fin N) ℂ =>
      Function.update z.1 fiber z.2)

/-- The Haar-refresh kernel evaluates pointwise to exactly the Haar-refresh
measure used in the one-link Doeblin lower bound. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHaarRefreshKernel_apply
    (H N : ℕ)
    (fiber : PeriodicHypercubicEvenSpatialSliceLink H)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHaarRefreshKernel
        H N fiber A =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHaarRefreshMeasure
        H N fiber A := by
  ext s hs
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHaarRefreshKernel,
    Kernel.map_apply' _
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkUpdate_uncurry_measurable
        H N fiber)
      A hs,
    Kernel.id_prod_apply' _ A
      ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkUpdate_uncurry_measurable
        H N fiber) hs),
    Kernel.const_apply]
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHaarRefreshMeasure
  have hSingle :
      Measurable
        (fun g : Matrix.specialUnitaryGroup (Fin N) ℂ =>
          Function.update A fiber g) := by
    exact
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkUpdate_uncurry_measurable
        H N fiber).comp (measurable_const.prodMk measurable_id)
  rw [Measure.map_apply hSingle hs]
  rfl

/-- Kernel-level form of the actual one-link Doeblin minorization.  The
coefficient is volume-independent and the theorem remains independent of
terminal covariance decay and remote-residual control. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel_lower_bound_haarRefreshKernel
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source fiber : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    (ENNReal.ofReal (Real.exp (32 * beta)))⁻¹ •
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHaarRefreshKernel
          H N fiber A ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel
        H N hN beta hbeta B target source fiber k g₂ A := by
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHaarRefreshKernel_apply]
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel_lower_bound_haarRefresh
      H N hN beta hbeta B target source fiber k g₂ A

end

end MathlibAnalytic
end MGAP4D
