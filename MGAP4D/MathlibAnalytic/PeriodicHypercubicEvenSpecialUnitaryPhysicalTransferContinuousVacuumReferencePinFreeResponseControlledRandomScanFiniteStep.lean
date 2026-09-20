import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferencePinFreeResponseControlledSourceForcingResolvent
import Mathlib.Tactic

/-!
# Finite-step pin-free response-controlled random-scan transport

The preceding theorem units removed the distinguished-target pin from the
configuration-independent physical left kernel, propagated that kernel through
the weighted random-scan orbit, and rebuilt the accumulated source-forcing
resolvent with the pin-free orbit.

This file reconnects those abstract bounds to the literal finite-step physical
random-scan dynamics.

It proves:

* every n-step physical restricted random-scan observable has left-fiber
  variation bounded by the pin-free response-controlled orbit;
* two n-step physical random-scan orbits with distinct represented right
  boundary values differ pointwise by the pin-free accumulated source
  discrepancy.

No distinguished-target pin is reintroduced.  No contraction, stationary
closure, covariance decay, coercivity, or mass-gap input is assumed.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory BigOperators

noncomputable section

local instance pinFreeResponseControlledRandomScanFiniteStepSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance pinFreeResponseControlledRandomScanFiniteStepSpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance pinFreeResponseControlledRandomScanFiniteStepSpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance pinFreeResponseControlledRandomScanFiniteStepSpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance pinFreeResponseControlledRandomScanFiniteStepSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance pinFreeResponseControlledRandomScanFiniteStepSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Every finite physical random-scan iterate has left-fiber variation bounded
by the pin-free response-controlled orbit. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate_fiberVariation_le_pinFreeResponseControlled
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (R :
      PeriodicHypercubicEvenSpatialSliceLink H →
        PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hRNonneg : ∀ target source, 0 ≤ R target source)
    (hResponse :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioUniformResponseProfileBound
        H N hN beta hbeta R)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (g₂ k : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (F : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ)
    (hF : StronglyMeasurable F)
    (variation : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hVariationNonneg : ∀ e, 0 ≤ variation e)
    (hVariation :
      ∀ (e : PeriodicHypercubicEvenSpatialSliceLink H)
        (C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
        (u v : Matrix.specialUnitaryGroup (Fin N) ℂ),
        |F (Function.update C e u) - F (Function.update C e v)| ≤ variation e)
    (n : ℕ)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (u v : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    |periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate
        H N hN beta hbeta B target source g₂ k F n (Function.update A e u) -
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate
        H N hN beta hbeta B target source g₂ k F n (Function.update A e v)| ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledRandomScanVariationIterate
        H beta hbeta R hRNonneg variation n e := by
  induction n generalizing e A u v with
  | zero =>
      simpa using hVariation e A u v
  | succ n ih =>
      rw [
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate_succ,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledRandomScanVariationIterate_succ]
      exact
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectation_fiberVariation_le_pinFreeResponseControlled
          H N hN beta hbeta R hRNonneg hResponse
          B target source g₂ k
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate
            H N hN beta hbeta B target source g₂ k F n)
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate_stronglyMeasurable
            H N hN beta hbeta B target source g₂ k F hF n)
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledRandomScanVariationIterate
            H beta hbeta R hRNonneg variation n)
          (fun background =>
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledRandomScanVariationIterate_nonneg
              H beta hbeta R hRNonneg variation hVariationNonneg n background)
          (fun background C a b => ih background C a b)
          e A u v

/-- Two physical restricted random-scan orbits with distinct represented
right-boundary values differ pointwise by the pin-free accumulated source
discrepancy. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate_boundarySource_difference_le_pinFreeResponseControlledAccumulated
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (R :
      PeriodicHypercubicEvenSpatialSliceLink H →
        PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hRNonneg : ∀ target source, 0 ≤ R target source)
    (hResponse :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioUniformResponseProfileBound
        H N hN beta hbeta R)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (g₂ k₁ k₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (F : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ)
    (hF : StronglyMeasurable F)
    (variation : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hVariationNonneg : ∀ e, 0 ≤ variation e)
    (hVariation :
      ∀ (e : PeriodicHypercubicEvenSpatialSliceLink H)
        (C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
        (u v : Matrix.specialUnitaryGroup (Fin N) ℂ),
        |F (Function.update C e u) - F (Function.update C e v)| ≤ variation e)
    (n : ℕ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    |periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate
        H N hN beta hbeta B target source g₂ k₁ F n A -
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate
        H N hN beta hbeta B target source g₂ k₂ F n A| ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledAccumulatedSourceDiscrepancy
        H beta hbeta source R hRNonneg variation n := by
  induction n generalizing A with
  | zero =>
      simp
  | succ n ih =>
      let F₁ :=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate
          H N hN beta hbeta B target source g₂ k₁ F n
      let F₂ :=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate
          H N hN beta hbeta B target source g₂ k₂ F n
      let vN :=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledRandomScanVariationIterate
          H beta hbeta R hRNonneg variation n
      let dN :=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledAccumulatedSourceDiscrepancy
          H beta hbeta source R hRNonneg variation n
      let profile :
          Sum
            (PeriodicHypercubicEvenSpatialSliceLink H)
            (PeriodicHypercubicEvenSpatialSliceLink H) → ℝ :=
        fun x =>
          match x with
          | Sum.inl e => vN e
          | Sum.inr _ => dN
      have hF₁ : StronglyMeasurable F₁ := by
        dsimp [F₁]
        exact
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate_stronglyMeasurable
            H N hN beta hbeta B target source g₂ k₁ F hF n
      have hF₂ : StronglyMeasurable F₂ := by
        dsimp [F₂]
        exact
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate_stronglyMeasurable
            H N hN beta hbeta B target source g₂ k₂ F hF n
      have hVNNonneg : ∀ e, 0 ≤ vN e := by
        intro e
        dsimp [vN]
        exact
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledRandomScanVariationIterate_nonneg
            H beta hbeta R hRNonneg variation hVariationNonneg n e
      have hDNNonneg : 0 ≤ dN := by
        dsimp [dN]
        exact
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledAccumulatedSourceDiscrepancy_nonneg
            H beta hbeta source R hRNonneg variation hVariationNonneg n
      have hProfileNonneg : ∀ x, 0 ≤ profile x := by
        intro x
        cases x with
        | inl e => simpa [profile] using hVNNonneg e
        | inr e => simpa [profile] using hDNNonneg
      have hVariation₁ :
          ∀ (e : PeriodicHypercubicEvenSpatialSliceLink H)
            (C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
            (u v : Matrix.specialUnitaryGroup (Fin N) ℂ),
            |F₁ (Function.update C e u) - F₁ (Function.update C e v)| ≤
              profile (Sum.inl e) := by
        intro e C u v
        dsimp [F₁, profile, vN]
        exact
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate_fiberVariation_le_pinFreeResponseControlled
            H N hN beta hbeta R hRNonneg hResponse B target source g₂ k₁
            F hF variation hVariationNonneg hVariation n e C u v
      have hVariation₂ :
          ∀ (e : PeriodicHypercubicEvenSpatialSliceLink H)
            (C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
            (u v : Matrix.specialUnitaryGroup (Fin N) ℂ),
            |F₂ (Function.update C e u) - F₂ (Function.update C e v)| ≤
              profile (Sum.inl e) := by
        intro e C u v
        dsimp [F₂, profile, vN]
        exact
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate_fiberVariation_le_pinFreeResponseControlled
            H N hN beta hbeta R hRNonneg hResponse B target source g₂ k₂
            F hF variation hVariationNonneg hVariation n e C u v
      have hPoint : ∀ C, |F₁ C - F₂ C| ≤ profile (Sum.inr source) := by
        intro C
        dsimp [F₁, F₂, profile, dN]
        exact ih C
      have hAffine :=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectation_affineTransport_le
          H N hN beta hbeta B target source g₂ k₁ k₂ A
          F₁ F₂ hF₁ hF₂ profile hProfileNonneg
          hVariation₁ hVariation₂ hPoint
      rw [
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate_succ,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate_succ,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledAccumulatedSourceDiscrepancy_succ]
      simpa [
        F₁, F₂, vN, dN, profile,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryRandomScanSourceDiscrepancyStep,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanUpdatedVariation,
        finiteInfluenceKernelRestrictedTargetRandomScanUpdatedVariation,
        finiteInfluenceKernelUpdatedVariation,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedKernel_left_right] using hAffine

end

end MathlibAnalytic
end MGAP4D
