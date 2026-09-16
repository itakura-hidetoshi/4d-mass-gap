import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceDistinctFiberRestrictedRandomScanIterate
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory BigOperators

noncomputable section

local instance referenceDistinctFiberRestrictedRandomScanFiniteStepSpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance referenceDistinctFiberRestrictedRandomScanFiniteStepSpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance referenceDistinctFiberRestrictedRandomScanFiniteStepSpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance referenceDistinctFiberRestrictedRandomScanFiniteStepSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance referenceDistinctFiberRestrictedRandomScanFiniteStepSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance referenceDistinctFiberRestrictedRandomScanFiniteStepSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- The actual physical continuous-C5 restricted random-scan observable after
`n` steps.  Each step samples only a physical left fiber; represented
right-source coordinates are never update targets. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (g₂ k : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (F : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ) :
    ℕ → (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ)
  | 0 => F
  | n + 1 => fun A =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectation
        H N hN beta hbeta B target source g₂ k A
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate
          H N hN beta hbeta B target source g₂ k F n)

@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate_zero
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (g₂ k : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (F : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate
        H N hN beta hbeta B target source g₂ k F 0 = F := by
  rfl

@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate_succ
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (g₂ k : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (F : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ)
    (n : ℕ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate
        H N hN beta hbeta B target source g₂ k F (n + 1) =
      fun A =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectation
          H N hN beta hbeta B target source g₂ k A
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate
            H N hN beta hbeta B target source g₂ k F n) := by
  rfl

/-- Every finite physical restricted random-scan iterate remains strongly
measurable when the starting observable is strongly measurable. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate_stronglyMeasurable
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (g₂ k : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (F : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ)
    (hF : StronglyMeasurable F)
    (n : ℕ) :
    StronglyMeasurable
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate
        H N hN beta hbeta B target source g₂ k F n) := by
  induction n with
  | zero => simpa using hF
  | succ n ih =>
      rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate_succ]
      exact
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectation_stronglyMeasurable
          H N hN beta hbeta B target source g₂ k
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate
            H N hN beta hbeta B target source g₂ k F n)
          ih

/-- At every finite step, physical left-fiber variation is dominated by the
matching `n`-step restricted tagged-carrier profile. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate_fiberVariation_le
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
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
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanVariationIterate
        H beta hbeta variation n (Sum.inl e) := by
  induction n generalizing e A u v with
  | zero =>
      simpa [
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTaggedLeftVariation] using
        hVariation e A u v
  | succ n ih =>
      have hIterMeas :
          StronglyMeasurable
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate
              H N hN beta hbeta B target source g₂ k F n) :=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate_stronglyMeasurable
          H N hN beta hbeta B target source g₂ k F hF n
      have hProfileNonneg :
          ∀ x : Sum
            (PeriodicHypercubicEvenSpatialSliceLink H)
            (PeriodicHypercubicEvenSpatialSliceLink H),
            0 ≤
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanVariationIterate
                H beta hbeta variation n x := by
        intro x
        exact
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanVariationIterate_nonneg
            H beta hbeta variation hVariationNonneg n x
      have hStep :=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectation_fiberVariation_le
          H N hN beta hbeta B target source g₂ k
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate
            H N hN beta hbeta B target source g₂ k F n)
          hIterMeas
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanVariationIterate
            H beta hbeta variation n)
          hProfileNonneg
          (by
            intro e' C u' v'
            exact ih e' C u' v')
          e A u v
      simpa only [
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate_succ,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanVariationIterate_succ] using
        hStep

/-- The actual `n`-step physical continuous-C5 restricted random-scan boundary
response is dominated by the right-source component of the same `n`-step
restricted tagged-carrier iterate. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate_transport_le
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
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
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanVariationIterate
        H beta hbeta variation n (Sum.inr source) := by
  induction n generalizing A with
  | zero =>
      simp [
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTaggedLeftVariation]
  | succ n ih =>
      let F₁ :=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate
          H N hN beta hbeta B target source g₂ k₁ F n
      let F₂ :=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate
          H N hN beta hbeta B target source g₂ k₂ F n
      let profile :=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanVariationIterate
          H beta hbeta variation n
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
      have hProfileNonneg : ∀ x, 0 ≤ profile x := by
        intro x
        dsimp [profile]
        exact
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanVariationIterate_nonneg
            H beta hbeta variation hVariationNonneg n x
      have hVariation₁ :
          ∀ (e : PeriodicHypercubicEvenSpatialSliceLink H)
            (C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
            (u v : Matrix.specialUnitaryGroup (Fin N) ℂ),
            |F₁ (Function.update C e u) - F₁ (Function.update C e v)| ≤
              profile (Sum.inl e) := by
        intro e C u v
        dsimp [F₁, profile]
        exact
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate_fiberVariation_le
            H N hN beta hbeta B target source g₂ k₁ F hF variation
            hVariationNonneg hVariation n e C u v
      have hVariation₂ :
          ∀ (e : PeriodicHypercubicEvenSpatialSliceLink H)
            (C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
            (u v : Matrix.specialUnitaryGroup (Fin N) ℂ),
            |F₂ (Function.update C e u) - F₂ (Function.update C e v)| ≤
              profile (Sum.inl e) := by
        intro e C u v
        dsimp [F₂, profile]
        exact
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate_fiberVariation_le
            H N hN beta hbeta B target source g₂ k₂ F hF variation
            hVariationNonneg hVariation n e C u v
      have hPoint : ∀ C, |F₁ C - F₂ C| ≤ profile (Sum.inr source) := by
        intro C
        dsimp [F₁, F₂, profile]
        exact ih C
      have hStep :=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectation_affineTransport_le
          H N hN beta hbeta B target source g₂ k₁ k₂ A F₁ F₂
          hF₁ hF₂ profile hProfileNonneg hVariation₁ hVariation₂ hPoint
      simpa only [
        F₁,
        F₂,
        profile,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate_succ,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanVariationIterate_succ] using
        hStep

end

end MathlibAnalytic
end MGAP4D
