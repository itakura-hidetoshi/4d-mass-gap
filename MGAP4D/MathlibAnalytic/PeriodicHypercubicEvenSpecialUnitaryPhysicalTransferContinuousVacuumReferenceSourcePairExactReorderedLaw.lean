import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceSourcePairLawOrdering
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Tactic

/-!
# Exact reordered source-pair / target-fiber law

PR #4726 proves that after sampling the first source value `u` from the
source conditional law, the updated background

  C = A[source <- u]

has exactly the original source reference distribution.

This file keeps the second independent source value `v` and the target-fiber
sample `g`.  It proves the exact law identity

  (A,u,v,g) |-> ((C,v),g)

between the PR #4725 triple law and the ordered conditional law

  mu_source(dC) kappa_source(C)(dv) kappa_target(C)(dg).

The key point is the exact source-fiber update invariance

  kappa_source(A[source <- u]) = kappa_source(A).

Thus no source/target heat-bath commutation is introduced.  The target sample
is simply retained after the source law has been reordered.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

noncomputable section

local instance sourcePairExactReorderSpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance sourcePairExactReorderSpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance sourcePairExactReorderSpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance sourcePairExactReorderSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance sourcePairExactReorderSpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance sourcePairExactReorderSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Keep the first source-updated background and the second independent source
sample. -/
def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairReorderedMap
    (H N : ℕ)
    (source : PeriodicHypercubicEvenSpatialSliceLink H)
    (z :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        (Matrix.specialUnitaryGroup (Fin N) ℂ ×
          Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      Matrix.specialUnitaryGroup (Fin N) ℂ :=
  (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairFirstUpdatedBackground
      H N source z,
    z.2.2)

/-- The source-pair reordering map is measurable. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairReorderedMap_measurable
    (H N : ℕ)
    (source : PeriodicHypercubicEvenSpatialSliceLink H) :
    Measurable
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairReorderedMap
        H N source) := by
  exact
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairFirstUpdatedBackground_measurable
      H N source).prodMk
      (measurable_snd.comp measurable_snd)

/-- Ordered source-background / second-source-value law

  mu_source(dC) kappa_source(C)(dv).

This is the source-dependent base measure after the first source sample has
been absorbed into the background. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceSecondBackgroundMeasure
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource source : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    Measure
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
      H N hN beta hbeta B source distinguishedSource k g₂ ⊗ₘ
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkConditionalKernel
      H N hN beta hbeta B source distinguishedSource source k g₂

instance
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceSecondBackgroundMeasure_isProbabilityMeasure
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource source : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceSecondBackgroundMeasure
        H N hN beta hbeta B distinguishedSource source k g₂) := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceSecondBackgroundMeasure
  infer_instance

/-- ENNReal integration form of the exact pair-law reordering.

The first source sample is absorbed into the background by stationarity, while
the second source sample remains conditionally distributed by the same source
kernel because that kernel is invariant under changing the stored source
coordinate. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePair_lintegral_reordered
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource source : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (Phi :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ≥0∞)
    (hPhi : Measurable Phi) :
    (∫⁻ z,
      Phi
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairReorderedMap
          H N source z)
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceIndependentPairBackgroundMeasure
        H N hN beta hbeta B distinguishedSource source k g₂) =
      ∫⁻ y, Phi y
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceSecondBackgroundMeasure
          H N hN beta hbeta B distinguishedSource source k g₂ := by
  let μ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
      H N hN beta hbeta B source distinguishedSource k g₂
  let κ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkConditionalKernel
      H N hN beta hbeta B source distinguishedSource source k g₂
  let Hfun := fun C :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
    ∫⁻ v, Phi (C, v) ∂κ C
  have hHfun : Measurable Hfun := by
    dsimp [Hfun]
    exact hPhi.lintegral_kernel_prod_right'
  have hFiber :
      ∀ A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
        (∫⁻ uv,
          Phi (Function.update A source uv.1, uv.2)
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkConditionalIndependentPairKernel
            H N hN beta hbeta B source distinguishedSource source k g₂ A) =
          ∫⁻ u, Hfun (Function.update A source u) ∂κ A := by
    intro A
    have hSection : Measurable
        (fun uv :
          Matrix.specialUnitaryGroup (Fin N) ℂ ×
            Matrix.specialUnitaryGroup (Fin N) ℂ =>
          Phi (Function.update A source uv.1, uv.2)) := by
      exact hPhi.comp
        (((measurable_update A).comp measurable_fst).prodMk measurable_snd)
    change
      (∫⁻ uv,
        Phi (Function.update A source uv.1, uv.2)
        ∂(κ A).prod (κ A)) =
        ∫⁻ u, Hfun (Function.update A source u) ∂κ A
    rw [MeasureTheory.lintegral_prod _ hSection.aemeasurable]
    apply lintegral_congr
    intro u
    have hUpdate :
        κ (Function.update A source u) = κ A := by
      dsimp [κ]
      exact
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkConditionalKernel_update_fiber
          H N hN beta hbeta B source distinguishedSource source k g₂ A u
    dsimp [Hfun]
    rw [hUpdate]
  have hReorderPhi : Measurable
      (fun z :
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          (Matrix.specialUnitaryGroup (Fin N) ℂ ×
            Matrix.specialUnitaryGroup (Fin N) ℂ) =>
        Phi
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairReorderedMap
            H N source z)) :=
    hPhi.comp
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairReorderedMap_measurable
        H N source)
  calc
    (∫⁻ z,
      Phi
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairReorderedMap
          H N source z)
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceIndependentPairBackgroundMeasure
        H N hN beta hbeta B distinguishedSource source k g₂) =
      ∫⁻ A,
        ∫⁻ uv,
          Phi (Function.update A source uv.1, uv.2)
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkConditionalIndependentPairKernel
            H N hN beta hbeta B source distinguishedSource source k g₂ A
        ∂μ := by
      unfold
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceIndependentPairBackgroundMeasure
      simpa [
        μ,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairReorderedMap,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairFirstUpdatedBackground]
        using Measure.lintegral_compProd hReorderPhi
    _ = ∫⁻ A,
        ∫⁻ u, Hfun (Function.update A source u) ∂κ A ∂μ := by
      apply lintegral_congr
      intro A
      exact hFiber A
    _ = ∫⁻ A, Hfun A ∂μ := by
      have hStationary :=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure_lintegral_oneLinkFiber
          H N hN beta hbeta B source distinguishedSource source k g₂
          Hfun hHfun
      apply hStationary.trans'
      apply lintegral_congr
      intro A
      rw [
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkConditionalKernel_apply]
    _ = ∫⁻ y, Phi y
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceSecondBackgroundMeasure
          H N hN beta hbeta B distinguishedSource source k g₂ := by
      symm
      unfold
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceSecondBackgroundMeasure
      simpa [μ, κ, Hfun] using Measure.lintegral_compProd hPhi

/-- Measure-level form of the pair reordering. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePair_map_reordered
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource source : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    Measure.map
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairReorderedMap
          H N source)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceIndependentPairBackgroundMeasure
          H N hN beta hbeta B distinguishedSource source k g₂) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceSecondBackgroundMeasure
        H N hN beta hbeta B distinguishedSource source k g₂ := by
  apply Measure.ext
  intro s hs
  let F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ≥0∞ :=
    s.indicator (fun _ => 1)
  have hF : Measurable F := measurable_const.indicator hs
  have hInt :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePair_lintegral_reordered
      H N hN beta hbeta B distinguishedSource source k g₂ F hF
  rw [Measure.map_apply
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairReorderedMap_measurable
      H N source) hs]
  have hPre : MeasurableSet
      ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairReorderedMap
        H N source) ⁻¹' s) :=
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairReorderedMap_measurable
      H N source) hs
  calc
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceIndependentPairBackgroundMeasure
        H N hN beta hbeta B distinguishedSource source k g₂
        ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairReorderedMap
          H N source) ⁻¹' s) =
      ∫⁻ z,
        F
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairReorderedMap
            H N source z)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceIndependentPairBackgroundMeasure
          H N hN beta hbeta B distinguishedSource source k g₂ := by
      rw [← lintegral_indicator_one hPre]
      apply lintegral_congr
      intro z
      by_cases hz :
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairReorderedMap
            H N source z ∈ s
      · simp [F, hz]
      · simp [F, hz]
    _ = ∫⁻ y, F y
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceSecondBackgroundMeasure
          H N hN beta hbeta B distinguishedSource source k g₂ := hInt
    _ = periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceSecondBackgroundMeasure
          H N hN beta hbeta B distinguishedSource source k g₂ s := by
      simpa [F] using lintegral_indicator_one hs

/-- Pull back the exact target-fiber kernel to an ordered source-background /
second-source-value carrier.  The retained second source value does not affect
the target law. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceSecondTargetFiberKernel
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource source target :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    Kernel
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        Matrix.specialUnitaryGroup (Fin N) ℂ)
      (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkConditionalKernel
      H N hN beta hbeta B source distinguishedSource target k g₂).comap
    Prod.fst measurable_fst

instance
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceSecondTargetFiberKernel_isMarkovKernel
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource source target :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    IsMarkovKernel
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceSecondTargetFiberKernel
        H N hN beta hbeta B distinguishedSource source target k g₂) := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceSecondTargetFiberKernel
  infer_instance

theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceSecondTargetFiberKernel_apply
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource source target :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (Cv :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceSecondTargetFiberKernel
        H N hN beta hbeta B distinguishedSource source target k g₂ Cv =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
        H N hN beta hbeta B source distinguishedSource target k g₂ Cv.1 := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceSecondTargetFiberKernel
  rw [Kernel.comap_apply]
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkConditionalKernel_apply
      H N hN beta hbeta B source distinguishedSource target k g₂ Cv.1

/-- Fully ordered law

  mu_source(dC) kappa_source(C)(dv) kappa_target(C)(dg).

The carrier is associated as `((C,v),g)`, which avoids any artificial
identification between the two conditional stages. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceSecondTargetOrderedMeasure
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource source target :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    Measure
      ((PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          Matrix.specialUnitaryGroup (Fin N) ℂ) ×
        Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceSecondBackgroundMeasure
      H N hN beta hbeta B distinguishedSource source k g₂ ⊗ₘ
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceSecondTargetFiberKernel
      H N hN beta hbeta B distinguishedSource source target k g₂

instance
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceSecondTargetOrderedMeasure_isProbabilityMeasure
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource source target :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceSecondTargetOrderedMeasure
        H N hN beta hbeta B distinguishedSource source target k g₂) := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceSecondTargetOrderedMeasure
  infer_instance

/-- Reorder one PR #4725 triple-law sample as `((C,v),g)`. -/
def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairTargetFiberReorderedMap
    (H N : ℕ)
    (source : PeriodicHypercubicEvenSpatialSliceLink H)
    (zg :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          (Matrix.specialUnitaryGroup (Fin N) ℂ ×
            Matrix.specialUnitaryGroup (Fin N) ℂ)) ×
        Matrix.specialUnitaryGroup (Fin N) ℂ) :
    (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        Matrix.specialUnitaryGroup (Fin N) ℂ) ×
      Matrix.specialUnitaryGroup (Fin N) ℂ :=
  (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairReorderedMap
      H N source zg.1,
    zg.2)

theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairTargetFiberReorderedMap_measurable
    (H N : ℕ)
    (source : PeriodicHypercubicEvenSpatialSliceLink H) :
    Measurable
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairTargetFiberReorderedMap
        H N source) := by
  exact
    ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairReorderedMap_measurable
      H N source).comp measurable_fst).prodMk measurable_snd

/-- Exact ENNReal integral identity for the fully reordered triple law. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairTargetFiberTripleMeasure_lintegral_reordered
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource source target :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (Phi :
      ((PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          Matrix.specialUnitaryGroup (Fin N) ℂ) ×
        Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ≥0∞)
    (hPhi : Measurable Phi) :
    (∫⁻ zg,
      Phi
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairTargetFiberReorderedMap
          H N source zg)
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairTargetFiberTripleMeasure
        H N hN beta hbeta B distinguishedSource source target k g₂) =
      ∫⁻ Cvg, Phi Cvg
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceSecondTargetOrderedMeasure
          H N hN beta hbeta B distinguishedSource source target k g₂ := by
  let orderedKernel :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceSecondTargetFiberKernel
      H N hN beta hbeta B distinguishedSource source target k g₂
  let psi := fun Cv :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        Matrix.specialUnitaryGroup (Fin N) ℂ =>
    ∫⁻ g, Phi (Cv, g) ∂orderedKernel Cv
  have hPsi : Measurable psi := by
    dsimp [psi]
    exact hPhi.lintegral_kernel_prod_right'
  have hOriginal : Measurable
      (fun zg :
        (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
            (Matrix.specialUnitaryGroup (Fin N) ℂ ×
              Matrix.specialUnitaryGroup (Fin N) ℂ)) ×
          Matrix.specialUnitaryGroup (Fin N) ℂ =>
        Phi
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairTargetFiberReorderedMap
            H N source zg)) :=
    hPhi.comp
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairTargetFiberReorderedMap_measurable
        H N source)
  calc
    (∫⁻ zg,
      Phi
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairTargetFiberReorderedMap
          H N source zg)
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairTargetFiberTripleMeasure
        H N hN beta hbeta B distinguishedSource source target k g₂) =
      ∫⁻ z,
        ∫⁻ g,
          Phi
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairReorderedMap
              H N source z, g)
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairTargetFiberKernel
            H N hN beta hbeta B distinguishedSource source target k g₂ z
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceIndependentPairBackgroundMeasure
          H N hN beta hbeta B distinguishedSource source k g₂ := by
      unfold
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairTargetFiberTripleMeasure
      simpa [
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairTargetFiberReorderedMap]
        using Measure.lintegral_compProd hOriginal
    _ = ∫⁻ z,
        psi
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairReorderedMap
            H N source z)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceIndependentPairBackgroundMeasure
          H N hN beta hbeta B distinguishedSource source k g₂ := by
      apply lintegral_congr
      intro z
      dsimp [psi, orderedKernel]
      rw [
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairTargetFiberKernel_apply,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceSecondTargetFiberKernel_apply]
      rfl
    _ = ∫⁻ Cv, psi Cv
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceSecondBackgroundMeasure
          H N hN beta hbeta B distinguishedSource source k g₂ := by
      exact
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePair_lintegral_reordered
          H N hN beta hbeta B distinguishedSource source k g₂ psi hPsi
    _ = ∫⁻ Cvg, Phi Cvg
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceSecondTargetOrderedMeasure
          H N hN beta hbeta B distinguishedSource source target k g₂ := by
      symm
      unfold
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceSecondTargetOrderedMeasure
      simpa [orderedKernel, psi] using Measure.lintegral_compProd hPhi

/-- Exact measure-level law ordering:

  map ((A,u,v),g) -> ((A[source<-u],v),g) tripleLaw
    = mu_source(dC) kappa_source(C)(dv) kappa_target(C)(dg).
-/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairTargetFiberTripleMeasure_map_reordered
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource source target :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    Measure.map
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairTargetFiberReorderedMap
          H N source)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairTargetFiberTripleMeasure
          H N hN beta hbeta B distinguishedSource source target k g₂) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceSecondTargetOrderedMeasure
        H N hN beta hbeta B distinguishedSource source target k g₂ := by
  apply Measure.ext
  intro s hs
  let F :
      ((PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          Matrix.specialUnitaryGroup (Fin N) ℂ) ×
        Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ≥0∞ :=
    s.indicator (fun _ => 1)
  have hF : Measurable F := measurable_const.indicator hs
  have hInt :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairTargetFiberTripleMeasure_lintegral_reordered
      H N hN beta hbeta B distinguishedSource source target k g₂ F hF
  rw [Measure.map_apply
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairTargetFiberReorderedMap_measurable
      H N source) hs]
  have hPre : MeasurableSet
      ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairTargetFiberReorderedMap
        H N source) ⁻¹' s) :=
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairTargetFiberReorderedMap_measurable
      H N source) hs
  calc
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairTargetFiberTripleMeasure
        H N hN beta hbeta B distinguishedSource source target k g₂
        ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairTargetFiberReorderedMap
          H N source) ⁻¹' s) =
      ∫⁻ zg,
        F
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairTargetFiberReorderedMap
            H N source zg)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairTargetFiberTripleMeasure
          H N hN beta hbeta B distinguishedSource source target k g₂ := by
      rw [← lintegral_indicator_one hPre]
      apply lintegral_congr
      intro zg
      by_cases hzg :
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairTargetFiberReorderedMap
            H N source zg ∈ s
      · simp [F, hzg]
      · simp [F, hzg]
    _ = ∫⁻ Cvg, F Cvg
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceSecondTargetOrderedMeasure
          H N hN beta hbeta B distinguishedSource source target k g₂ := hInt
    _ = periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceSecondTargetOrderedMeasure
          H N hN beta hbeta B distinguishedSource source target k g₂ s := by
      simpa [F] using lintegral_indicator_one hs

end

end MGAP4D.MathlibAnalytic
