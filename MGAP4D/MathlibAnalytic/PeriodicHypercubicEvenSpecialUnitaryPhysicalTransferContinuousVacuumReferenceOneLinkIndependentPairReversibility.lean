import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceOneLinkConditionalIndependentPairKernel
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Tactic

/-!
# Exchangeable reference one-link iid resampling pair

The continuous-vacuum reference law already has an exact measurable one-link
conditional kernel at every spatial fiber.  This file forms two conditionally
independent samples from that same fiber over an arbitrary reference law
parameter pair `(referenceTarget, referenceSource)`.

The resulting background/pair law is invariant under swapping the two sampled
fiber values.  After inserting the two samples into the same background, the
induced pair of complete configurations is therefore invariant under exchanging
the two configurations.

This is the concrete exchangeable carrier needed before identifying it with
the old/new one-link heat-bath transition joint law.  No commutation between
different fibers and no new analytic estimate is used.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

local instance referenceIidPairReversibilitySpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance referenceIidPairReversibilitySpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance referenceIidPairReversibilitySpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance referenceIidPairReversibilitySpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance referenceIidPairReversibilitySpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance referenceIidPairReversibilitySpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- The conditional independent-pair fiber kernel is invariant under swapping
its two iid fiber coordinates. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkConditionalIndependentPairKernel_map_swap
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (referenceTarget referenceSource fiber :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkConditionalIndependentPairKernel
      H N hN beta hbeta B referenceTarget referenceSource fiber k g₂).map
        Prod.swap =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkConditionalIndependentPairKernel
        H N hN beta hbeta B referenceTarget referenceSource fiber k g₂ := by
  ext A : 1
  rw [Kernel.map_apply _ measurable_swap A]
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkConditionalIndependentPairKernel_apply]
  let μA :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
      H N hN beta hbeta B referenceTarget referenceSource fiber k g₂ A
  letI : IsProbabilityMeasure μA :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_isProbabilityMeasure
      H N hN beta hbeta B referenceTarget referenceSource fiber k g₂ A
  simpa [μA] using (Measure.prod_swap (μ := μA) (ν := μA))

/-- Generic reference background together with two iid values from one selected
fiber.  Unlike PR #4724, the reference target/source parameters and the sampled
fiber are independent parameters. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkIndependentPairBackgroundMeasure
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (referenceTarget referenceSource fiber :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    Measure
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        (Matrix.specialUnitaryGroup (Fin N) ℂ ×
          Matrix.specialUnitaryGroup (Fin N) ℂ)) :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
      H N hN beta hbeta B referenceTarget referenceSource k g₂ ⊗ₘ
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkConditionalIndependentPairKernel
      H N hN beta hbeta B referenceTarget referenceSource fiber k g₂

/-- The generic iid pair/background law is a probability measure. -/
instance
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkIndependentPairBackgroundMeasure_isProbabilityMeasure
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (referenceTarget referenceSource fiber :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkIndependentPairBackgroundMeasure
        H N hN beta hbeta B referenceTarget referenceSource fiber k g₂) := by
  let μ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
      H N hN beta hbeta B referenceTarget referenceSource k g₂
  letI : IsProbabilityMeasure μ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure_isProbabilityMeasure
      H N hN beta hbeta B referenceTarget referenceSource k g₂
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkIndependentPairBackgroundMeasure
  infer_instance

/-- Keep the background fixed and swap the two iid fiber samples. -/
def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkIndependentPairBackgroundSwap
    (H N : ℕ)
    (z :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        (Matrix.specialUnitaryGroup (Fin N) ℂ ×
          Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      (Matrix.specialUnitaryGroup (Fin N) ℂ ×
        Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  Prod.map id Prod.swap z

theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkIndependentPairBackgroundSwap_measurable
    (H N : ℕ) :
    Measurable
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkIndependentPairBackgroundSwap
        H N) := by
  exact measurable_fst.prodMk
    ((measurable_snd.comp measurable_snd).prodMk
      (measurable_fst.comp measurable_snd))

/-- The generic reference pair/background law is exchangeable in its two
conditionally iid fiber values. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkIndependentPairBackgroundMeasure_map_swap
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (referenceTarget referenceSource fiber :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    Measure.map
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkIndependentPairBackgroundSwap
          H N)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkIndependentPairBackgroundMeasure
          H N hN beta hbeta B referenceTarget referenceSource fiber k g₂) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkIndependentPairBackgroundMeasure
        H N hN beta hbeta B referenceTarget referenceSource fiber k g₂ := by
  let μ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
      H N hN beta hbeta B referenceTarget referenceSource k g₂
  letI : IsProbabilityMeasure μ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure_isProbabilityMeasure
      H N hN beta hbeta B referenceTarget referenceSource k g₂
  let κ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkConditionalIndependentPairKernel
      H N hN beta hbeta B referenceTarget referenceSource fiber k g₂
  have hSwap :
      Measurable
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkIndependentPairBackgroundSwap
          H N) :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkIndependentPairBackgroundSwap_measurable
      H N
  have hKernel :
      (Kernel.id ×ₖ κ).map
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkIndependentPairBackgroundSwap
            H N) =
        Kernel.id ×ₖ κ := by
    change
      (Kernel.id ×ₖ κ).map (Prod.map id Prod.swap) =
        Kernel.id ×ₖ κ
    rw [← Kernel.map_prod_map _ _ measurable_id measurable_swap]
    rw [Kernel.map_id]
    rw [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkConditionalIndependentPairKernel_map_swap
        H N hN beta hbeta B referenceTarget referenceSource fiber k g₂]
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkIndependentPairBackgroundMeasure
  rw [Measure.compProd_eq_comp_prod]
  rw [Measure.map_comp μ (Kernel.id ×ₖ κ) hSwap]
  rw [hKernel]

/-- Insert the two iid fiber values into the same background, producing an
ordered pair of complete configurations. -/
def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkIndependentPairConfigurationMap
    (H N : ℕ)
    (fiber : PeriodicHypercubicEvenSpatialSliceLink H)
    (z :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        (Matrix.specialUnitaryGroup (Fin N) ℂ ×
          Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N :=
  (Function.update z.1 fiber z.2.1,
    Function.update z.1 fiber z.2.2)

theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkIndependentPairConfigurationMap_measurable
    (H N : ℕ)
    (fiber : PeriodicHypercubicEvenSpatialSliceLink H) :
    Measurable
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkIndependentPairConfigurationMap
        H N fiber) := by
  have hFirstInput :
      Measurable
        (fun z :
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
            (Matrix.specialUnitaryGroup (Fin N) ℂ ×
              Matrix.specialUnitaryGroup (Fin N) ℂ) =>
          (z.1, z.2.1)) :=
    measurable_fst.prodMk (measurable_fst.comp measurable_snd)
  have hSecondInput :
      Measurable
        (fun z :
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
            (Matrix.specialUnitaryGroup (Fin N) ℂ ×
              Matrix.specialUnitaryGroup (Fin N) ℂ) =>
          (z.1, z.2.2)) :=
    measurable_fst.prodMk (measurable_snd.comp measurable_snd)
  exact
    ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkUpdate_uncurry_measurable
      H N fiber).comp hFirstInput).prodMk
      ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkUpdate_uncurry_measurable
        H N fiber).comp hSecondInput)

/-- Pair of complete configurations generated by two iid resamplings of one
reference fiber. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkIndependentPairConfigurationMeasure
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (referenceTarget referenceSource fiber :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    Measure
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :=
  Measure.map
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkIndependentPairConfigurationMap
      H N fiber)
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkIndependentPairBackgroundMeasure
      H N hN beta hbeta B referenceTarget referenceSource fiber k g₂)

/-- The complete-configuration pair law is exchangeable. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkIndependentPairConfigurationMeasure_map_swap
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (referenceTarget referenceSource fiber :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    Measure.map Prod.swap
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkIndependentPairConfigurationMeasure
          H N hN beta hbeta B referenceTarget referenceSource fiber k g₂) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkIndependentPairConfigurationMeasure
        H N hN beta hbeta B referenceTarget referenceSource fiber k g₂ := by
  let ν :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkIndependentPairBackgroundMeasure
      H N hN beta hbeta B referenceTarget referenceSource fiber k g₂
  let swapIn :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkIndependentPairBackgroundSwap
      H N
  let configPair :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkIndependentPairConfigurationMap
      H N fiber
  have hSwapIn : Measurable swapIn := by
    simpa [swapIn] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkIndependentPairBackgroundSwap_measurable
        H N
  have hConfigPair : Measurable configPair := by
    simpa [configPair] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkIndependentPairConfigurationMap_measurable
        H N fiber
  have hSwapLaw : Measure.map swapIn ν = ν := by
    simpa [swapIn, ν] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkIndependentPairBackgroundMeasure_map_swap
        H N hN beta hbeta B referenceTarget referenceSource fiber k g₂
  have hComm :
      Prod.swap ∘ configPair = configPair ∘ swapIn := by
    funext z
    rfl
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkIndependentPairConfigurationMeasure
  rw [Measure.map_map measurable_swap hConfigPair]
  rw [hComm]
  rw [← Measure.map_map hConfigPair hSwapIn]
  rw [hSwapLaw]

end

end MGAP4D.MathlibAnalytic
