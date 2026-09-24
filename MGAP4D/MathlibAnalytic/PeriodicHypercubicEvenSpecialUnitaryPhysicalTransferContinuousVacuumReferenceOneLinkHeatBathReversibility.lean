import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceOneLinkIndependentPairReversibility
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSixSpatialSweepStageSourceUpdateCanonicalDirectEnergy
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Tactic

/-!
# Continuous-vacuum reference one-link heat-bath reversibility

PR #4731 constructs an exchangeable pair of complete configurations by taking
two conditionally iid samples from one selected reference fiber.

This file identifies that exchangeable pair law with the actual old/new
one-link reference heat-bath joint law

  mu_ref(dC) K_fiber(C,dD).

The proof first absorbs the first iid fiber sample into the background using
the already-proved exact one-link stationarity and same-fiber conditional-law
invariance. The resulting ordered law is

  mu_ref(dC) kappa_fiber(C)(dv).

Mapping (C,v) to (C,C[fiber <- v]) is then exactly the composition-product
heat-bath joint law. Hence exchangeability of the iid pair gives the concrete
detailed-balance statement

  map Prod.swap J_fiber = J_fiber.

No commutation between different fibers, covariance estimate, or additional
analytic assumption is used.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

noncomputable section

local instance referenceOneLinkReversibilitySpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance referenceOneLinkReversibilitySpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance referenceOneLinkReversibilitySpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance referenceOneLinkReversibilitySpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance referenceOneLinkReversibilitySpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance referenceOneLinkReversibilitySpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Absorb the first iid fiber sample into the background while retaining the
second sample as an explicit fiber value. -/
def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkIndependentPairReorderedMap
    (H N : ℕ)
    (fiber : PeriodicHypercubicEvenSpatialSliceLink H)
    (z :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        (Matrix.specialUnitaryGroup (Fin N) ℂ ×
          Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      Matrix.specialUnitaryGroup (Fin N) ℂ :=
  (Function.update z.1 fiber z.2.1, z.2.2)

theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkIndependentPairReorderedMap_measurable
    (H N : ℕ)
    (fiber : PeriodicHypercubicEvenSpatialSliceLink H) :
    Measurable
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkIndependentPairReorderedMap
        H N fiber) := by
  have hFirstInput :
      Measurable
        (fun z :
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
            (Matrix.specialUnitaryGroup (Fin N) ℂ ×
              Matrix.specialUnitaryGroup (Fin N) ℂ) =>
          (z.1, z.2.1)) :=
    measurable_fst.prodMk (measurable_fst.comp measurable_snd)
  exact
    ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkUpdate_uncurry_measurable
      H N fiber).comp hFirstInput).prodMk
      (measurable_snd.comp measurable_snd)

/-- Ordered reference background plus one remaining conditional fiber value:
mu_ref(dC) kappa_fiber(C)(dv). -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkOrderedBackgroundValueMeasure
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (referenceTarget referenceSource fiber :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    Measure
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
      H N hN beta hbeta B referenceTarget referenceSource k g₂ ⊗ₘ
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkConditionalKernel
      H N hN beta hbeta B referenceTarget referenceSource fiber k g₂

instance
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkOrderedBackgroundValueMeasure_isProbabilityMeasure
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (referenceTarget referenceSource fiber :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkOrderedBackgroundValueMeasure
        H N hN beta hbeta B referenceTarget referenceSource fiber k g₂) := by
  let μ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
      H N hN beta hbeta B referenceTarget referenceSource k g₂
  letI : IsProbabilityMeasure μ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure_isProbabilityMeasure
      H N hN beta hbeta B referenceTarget referenceSource k g₂
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkOrderedBackgroundValueMeasure
  infer_instance

/-- Generic iid pair law ordering. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkIndependentPair_lintegral_reordered
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (referenceTarget referenceSource fiber :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (Phi :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ≥0∞)
    (hPhi : Measurable Phi) :
    (∫⁻ z,
      Phi
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkIndependentPairReorderedMap
          H N fiber z)
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkIndependentPairBackgroundMeasure
        H N hN beta hbeta B referenceTarget referenceSource fiber k g₂) =
      ∫⁻ y, Phi y
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkOrderedBackgroundValueMeasure
          H N hN beta hbeta B referenceTarget referenceSource fiber k g₂ := by
  let μ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
      H N hN beta hbeta B referenceTarget referenceSource k g₂
  letI : IsProbabilityMeasure μ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure_isProbabilityMeasure
      H N hN beta hbeta B referenceTarget referenceSource k g₂
  let κ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkConditionalKernel
      H N hN beta hbeta B referenceTarget referenceSource fiber k g₂
  let Hfun := fun C :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
    ∫⁻ v, Phi (C, v) ∂κ C
  have hHfun : Measurable Hfun := by
    dsimp [Hfun]
    exact hPhi.lintegral_kernel_prod_right'
  have hFiber :
      ∀ A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
        (∫⁻ uv,
          Phi (Function.update A fiber uv.1, uv.2)
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkConditionalIndependentPairKernel
            H N hN beta hbeta B referenceTarget referenceSource fiber k g₂ A) =
          ∫⁻ u, Hfun (Function.update A fiber u) ∂κ A := by
    intro A
    have hSection : Measurable
        (fun uv :
          Matrix.specialUnitaryGroup (Fin N) ℂ ×
            Matrix.specialUnitaryGroup (Fin N) ℂ =>
          Phi (Function.update A fiber uv.1, uv.2)) := by
      exact hPhi.comp
        (((measurable_update A).comp measurable_fst).prodMk measurable_snd)
    unfold
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkConditionalIndependentPairKernel
    rw [Kernel.prod_apply]
    change
      (∫⁻ uv,
        Phi (Function.update A fiber uv.1, uv.2)
        ∂(κ A).prod (κ A)) =
        ∫⁻ u, Hfun (Function.update A fiber u) ∂κ A
    rw [MeasureTheory.lintegral_prod _ hSection.aemeasurable]
    apply lintegral_congr
    intro u
    have hUpdate : κ (Function.update A fiber u) = κ A := by
      dsimp [κ]
      exact
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkConditionalKernel_update_fiber
          H N hN beta hbeta B referenceTarget referenceSource fiber k g₂ A u
    dsimp [Hfun]
    rw [hUpdate]
  have hReorderPhi : Measurable
      (fun z :
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          (Matrix.specialUnitaryGroup (Fin N) ℂ ×
            Matrix.specialUnitaryGroup (Fin N) ℂ) =>
        Phi
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkIndependentPairReorderedMap
            H N fiber z)) :=
    hPhi.comp
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkIndependentPairReorderedMap_measurable
        H N fiber)
  calc
    (∫⁻ z,
      Phi
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkIndependentPairReorderedMap
          H N fiber z)
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkIndependentPairBackgroundMeasure
        H N hN beta hbeta B referenceTarget referenceSource fiber k g₂) =
      ∫⁻ A,
        ∫⁻ uv,
          Phi (Function.update A fiber uv.1, uv.2)
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkConditionalIndependentPairKernel
            H N hN beta hbeta B referenceTarget referenceSource fiber k g₂ A
        ∂μ := by
      unfold
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkIndependentPairBackgroundMeasure
      simpa [
        μ,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkIndependentPairReorderedMap]
        using Measure.lintegral_compProd hReorderPhi
    _ = ∫⁻ A,
        ∫⁻ u, Hfun (Function.update A fiber u) ∂κ A ∂μ := by
      apply lintegral_congr
      intro A
      exact hFiber A
    _ = ∫⁻ A, Hfun A ∂μ := by
      calc
        (∫⁻ A,
          ∫⁻ u, Hfun (Function.update A fiber u) ∂κ A ∂μ) =
          ∫⁻ A,
            ∫⁻ u, Hfun (Function.update A fiber u)
              ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
                H N hN beta hbeta B referenceTarget referenceSource fiber k g₂ A
            ∂μ := by
          apply lintegral_congr
          intro A
          rw [
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkConditionalKernel_apply]
        _ = ∫⁻ A, Hfun A ∂μ := by
          simpa [μ] using
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure_lintegral_oneLinkFiber
              H N hN beta hbeta B referenceTarget referenceSource fiber k g₂
              Hfun hHfun
    _ = ∫⁻ y, Phi y
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkOrderedBackgroundValueMeasure
          H N hN beta hbeta B referenceTarget referenceSource fiber k g₂ := by
      symm
      unfold
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkOrderedBackgroundValueMeasure
      simpa [μ, κ, Hfun] using Measure.lintegral_compProd hPhi

/-- Measure-level generic iid pair reordering. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkIndependentPairBackgroundMeasure_map_reordered
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (referenceTarget referenceSource fiber :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    Measure.map
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkIndependentPairReorderedMap
          H N fiber)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkIndependentPairBackgroundMeasure
          H N hN beta hbeta B referenceTarget referenceSource fiber k g₂) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkOrderedBackgroundValueMeasure
        H N hN beta hbeta B referenceTarget referenceSource fiber k g₂ := by
  apply Measure.ext
  intro s hs
  let F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ≥0∞ :=
    s.indicator (fun _ => 1)
  have hF : Measurable F := measurable_const.indicator hs
  have hInt :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkIndependentPair_lintegral_reordered
      H N hN beta hbeta B referenceTarget referenceSource fiber k g₂ F hF
  rw [Measure.map_apply
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkIndependentPairReorderedMap_measurable
      H N fiber) hs]
  have hPre : MeasurableSet
      ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkIndependentPairReorderedMap
        H N fiber) ⁻¹' s) :=
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkIndependentPairReorderedMap_measurable
      H N fiber) hs
  calc
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkIndependentPairBackgroundMeasure
        H N hN beta hbeta B referenceTarget referenceSource fiber k g₂
        ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkIndependentPairReorderedMap
          H N fiber) ⁻¹' s) =
      ∫⁻ z,
        F
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkIndependentPairReorderedMap
            H N fiber z)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkIndependentPairBackgroundMeasure
          H N hN beta hbeta B referenceTarget referenceSource fiber k g₂ := by
      rw [← lintegral_indicator_one hPre]
      apply lintegral_congr
      intro z
      by_cases hz :
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkIndependentPairReorderedMap
            H N fiber z ∈ s
      · simp [F, hz]
      · simp [F, hz]
    _ = ∫⁻ y, F y
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkOrderedBackgroundValueMeasure
          H N hN beta hbeta B referenceTarget referenceSource fiber k g₂ := hInt
    _ =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkOrderedBackgroundValueMeasure
        H N hN beta hbeta B referenceTarget referenceSource fiber k g₂ s := by
      simpa [F] using lintegral_indicator_one hs

/-- Old/new joint law of the actual full-configuration reference one-link
heat-bath kernel. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathJointMeasure
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (referenceTarget referenceSource fiber :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    Measure
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
      H N hN beta hbeta B referenceTarget referenceSource k g₂ ⊗ₘ
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel
      H N hN beta hbeta B referenceTarget referenceSource fiber k g₂

instance
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathJointMeasure_isProbabilityMeasure
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (referenceTarget referenceSource fiber :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathJointMeasure
        H N hN beta hbeta B referenceTarget referenceSource fiber k g₂) := by
  let μ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
      H N hN beta hbeta B referenceTarget referenceSource k g₂
  letI : IsProbabilityMeasure μ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure_isProbabilityMeasure
      H N hN beta hbeta B referenceTarget referenceSource k g₂
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathJointMeasure
  infer_instance

/-- Pointwise description of the full reference heat-bath kernel as the
pushforward of the literal fiber probability law. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel_apply_eq_map
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (referenceTarget referenceSource fiber :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel
        H N hN beta hbeta B referenceTarget referenceSource fiber k g₂ A =
      Measure.map
        (fun v : Matrix.specialUnitaryGroup (Fin N) ℂ =>
          Function.update A fiber v)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
          H N hN beta hbeta B referenceTarget referenceSource fiber k g₂ A) := by
  let update :=
    fun z :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        Matrix.specialUnitaryGroup (Fin N) ℂ =>
      Function.update z.1 fiber z.2
  have hUpdate : Measurable update :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkUpdate_uncurry_measurable
      H N fiber
  have hFiberUpdate : Measurable
      (fun v : Matrix.specialUnitaryGroup (Fin N) ℂ =>
        Function.update A fiber v) :=
    measurable_update A
  ext s hs
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel
  rw [Kernel.map_apply' _ hUpdate A hs]
  rw [Kernel.id_prod_apply' _ A (hUpdate hs)]
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkConditionalKernel_apply]
  rw [Measure.map_apply hFiberUpdate hs]
  rfl

/-- Turn an ordered background/value pair into the corresponding old/new pair
of complete configurations. -/
def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkOrderedBackgroundValueConfigurationPairMap
    (H N : ℕ)
    (fiber : PeriodicHypercubicEvenSpatialSliceLink H)
    (Cv :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        Matrix.specialUnitaryGroup (Fin N) ℂ) :
    PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N :=
  (Cv.1, Function.update Cv.1 fiber Cv.2)

theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkOrderedBackgroundValueConfigurationPairMap_measurable
    (H N : ℕ)
    (fiber : PeriodicHypercubicEvenSpatialSliceLink H) :
    Measurable
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkOrderedBackgroundValueConfigurationPairMap
        H N fiber) := by
  exact measurable_fst.prodMk
    ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkUpdate_uncurry_measurable
      H N fiber).comp (measurable_fst.prodMk measurable_snd))

/-- Mapping the ordered background/value law to complete configurations is
exactly the actual old/new heat-bath joint law. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkOrderedBackgroundValueMeasure_map_configurationPair
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (referenceTarget referenceSource fiber :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    Measure.map
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkOrderedBackgroundValueConfigurationPairMap
          H N fiber)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkOrderedBackgroundValueMeasure
          H N hN beta hbeta B referenceTarget referenceSource fiber k g₂) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathJointMeasure
        H N hN beta hbeta B referenceTarget referenceSource fiber k g₂ := by
  let pairMap :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkOrderedBackgroundValueConfigurationPairMap
      H N fiber
  have hPairMap : Measurable pairMap :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkOrderedBackgroundValueConfigurationPairMap_measurable
      H N fiber
  apply Measure.ext
  intro s hs
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkOrderedBackgroundValueMeasure
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathJointMeasure
  rw [Measure.map_apply hPairMap hs]
  rw [Measure.compProd_apply (hPairMap hs)]
  rw [Measure.compProd_apply hs]
  apply lintegral_congr
  intro C
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel_apply_eq_map
      H N hN beta hbeta B referenceTarget referenceSource fiber k g₂ C]
  have hFiberUpdate : Measurable
      (fun v : Matrix.specialUnitaryGroup (Fin N) ℂ =>
        Function.update C fiber v) :=
    measurable_update C
  rw [Measure.map_apply hFiberUpdate (measurable_prodMk_left hs)]
  rfl

/-- The iid-pair configuration law from PR #4731 is exactly the actual
old/new reference heat-bath joint law. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkIndependentPairConfigurationMeasure_eq_heatBathJointMeasure
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (referenceTarget referenceSource fiber :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkIndependentPairConfigurationMeasure
        H N hN beta hbeta B referenceTarget referenceSource fiber k g₂ =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathJointMeasure
        H N hN beta hbeta B referenceTarget referenceSource fiber k g₂ := by
  let reorder :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkIndependentPairReorderedMap
      H N fiber
  let pairMap :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkOrderedBackgroundValueConfigurationPairMap
      H N fiber
  have hReorder : Measurable reorder :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkIndependentPairReorderedMap_measurable
      H N fiber
  have hPairMap : Measurable pairMap :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkOrderedBackgroundValueConfigurationPairMap_measurable
      H N fiber
  have hCompose :
      pairMap ∘ reorder =
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkIndependentPairConfigurationMap
          H N fiber := by
    funext z
    apply Prod.ext
    · rfl
    · exact
        periodicHypercubicEvenSpatialSliceSourceUpdate_update
          z.1 fiber z.2.1 z.2.2
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkIndependentPairConfigurationMeasure
  rw [← hCompose]
  rw [← Measure.map_map hPairMap hReorder]
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkIndependentPairBackgroundMeasure_map_reordered
      H N hN beta hbeta B referenceTarget referenceSource fiber k g₂]
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkOrderedBackgroundValueMeasure_map_configurationPair
      H N hN beta hbeta B referenceTarget referenceSource fiber k g₂

/-- Concrete detailed balance / reversibility of the normalized
continuous-vacuum reference one-link heat-bath joint law. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathJointMeasure_map_swap
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (referenceTarget referenceSource fiber :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    Measure.map Prod.swap
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathJointMeasure
          H N hN beta hbeta B referenceTarget referenceSource fiber k g₂) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathJointMeasure
        H N hN beta hbeta B referenceTarget referenceSource fiber k g₂ := by
  rw [
    ← periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkIndependentPairConfigurationMeasure_eq_heatBathJointMeasure
      H N hN beta hbeta B referenceTarget referenceSource fiber k g₂]
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkIndependentPairConfigurationMeasure_map_swap
      H N hN beta hbeta B referenceTarget referenceSource fiber k g₂

end

end MGAP4D.MathlibAnalytic
