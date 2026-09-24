import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceOneLinkHeatBathReversibility
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

/-!
# Integral symmetry of the continuous-vacuum reference one-link heat-bath joint law

PR #4732 proves the exact measure-level detailed-balance identity

  map swap J_fiber = J_fiber.

This file exposes the corresponding measure-preserving swap and the two
integration forms needed downstream:

* ENNReal lower-integral symmetry for measurable nonnegative observables;
* Bochner-integral symmetry for a.e. strongly measurable normed-space
  observables.

No new probabilistic or analytic assumption is introduced.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

local instance referenceHeatBathIntegralSymmetrySpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance referenceHeatBathIntegralSymmetrySpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance referenceHeatBathIntegralSymmetrySpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance referenceHeatBathIntegralSymmetrySpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance referenceHeatBathIntegralSymmetrySpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance referenceHeatBathIntegralSymmetrySpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Exchange of the old and newly resampled configurations preserves the exact
continuous-vacuum reference one-link heat-bath joint law. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathJointSwapMeasurePreserving
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (referenceTarget referenceSource fiber :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    MeasurePreserving Prod.swap
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathJointMeasure
        H N hN beta hbeta B referenceTarget referenceSource fiber k g₂)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathJointMeasure
        H N hN beta hbeta B referenceTarget referenceSource fiber k g₂) :=
  ⟨measurable_swap,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathJointMeasure_map_swap
      H N hN beta hbeta B referenceTarget referenceSource fiber k g₂⟩

/-- Nonnegative measurable integration against the exact reference heat-bath
joint law is symmetric under old/new exchange. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathJointMeasure_lintegral_symm
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (referenceTarget referenceSource fiber :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (Phi :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) →
        ℝ≥0∞)
    (hPhi : Measurable Phi) :
    (∫⁻ z, Phi z
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathJointMeasure
        H N hN beta hbeta B referenceTarget referenceSource fiber k g₂) =
      ∫⁻ z, Phi z.swap
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathJointMeasure
          H N hN beta hbeta B referenceTarget referenceSource fiber k g₂ := by
  let J :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathJointMeasure
      H N hN beta hbeta B referenceTarget referenceSource fiber k g₂
  have hMap : Measure.map Prod.swap J = J := by
    simpa [J] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathJointMeasure_map_swap
        H N hN beta hbeta B referenceTarget referenceSource fiber k g₂
  calc
    (∫⁻ z, Phi z ∂J) =
        ∫⁻ z, Phi z ∂Measure.map Prod.swap J := by
      rw [hMap]
    _ = ∫⁻ z, Phi z.swap ∂J := by
      exact MeasureTheory.lintegral_map hPhi measurable_swap

/-- Bochner integration against the exact reference heat-bath joint law is
symmetric under old/new exchange. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathJointMeasure_integral_symm
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (referenceTarget referenceSource fiber :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (Phi :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) →
        E)
    (hPhi : AEStronglyMeasurable Phi
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathJointMeasure
        H N hN beta hbeta B referenceTarget referenceSource fiber k g₂)) :
    (∫ z, Phi z
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathJointMeasure
        H N hN beta hbeta B referenceTarget referenceSource fiber k g₂) =
      ∫ z, Phi z.swap
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathJointMeasure
          H N hN beta hbeta B referenceTarget referenceSource fiber k g₂ := by
  let J :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathJointMeasure
      H N hN beta hbeta B referenceTarget referenceSource fiber k g₂
  have hMap : Measure.map Prod.swap J = J := by
    simpa [J] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathJointMeasure_map_swap
        H N hN beta hbeta B referenceTarget referenceSource fiber k g₂
  have hPhiMap : AEStronglyMeasurable Phi (Measure.map Prod.swap J) := by
    simpa [hMap] using hPhi
  calc
    (∫ z, Phi z ∂J) =
        ∫ z, Phi z ∂Measure.map Prod.swap J := by
      rw [hMap]
    _ = ∫ z, Phi z.swap ∂J :=
      MeasureTheory.integral_map measurable_swap.aemeasurable hPhiMap

end

end MGAP4D.MathlibAnalytic
