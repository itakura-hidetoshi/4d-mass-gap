import MGAP4D.MathlibAnalytic.PeriodicHypercubicSpecialUnitaryNativeConditionalPairReferenceEnergyBCF
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory

noncomputable section

/-- Short explicit name for the periodic compact-Haar `SU(N)` Wilson system used
by the one-link support certificates below. -/
abbrev periodicHypercubicSpecialUnitaryOneLinkSupportSystem
    (n N : ℕ)
    [NeZero n]
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (beta_nonneg : 0 ≤ beta) :
    ContinuousCompactOrientedGaugeWilsonSystem :=
  periodicHypercubicSpecialUnitaryWilsonSystem
    n N hN beta beta_nonneg

section PeriodicSpecialUnitary

variable
    (n N : ℕ)
    [NeZero n]
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (beta_nonneg : 0 ≤ beta)

/-- Squared configuration-pair disagreement away from one target physical link.
It vanishes exactly on pairs whose two configurations agree at every source
other than the target. -/
def periodicHypercubicSpecialUnitaryOffTargetPairEnergy
    (target : PeriodicHypercubicEdge n)
    (y :
      (periodicHypercubicSpecialUnitaryOneLinkSupportSystem
        n N hN beta beta_nonneg).base.Configuration ×
      (periodicHypercubicSpecialUnitaryOneLinkSupportSystem
        n N hN beta beta_nonneg).base.Configuration) : ℝ := by
  classical
  exact ∑ source : PeriodicHypercubicEdge n,
    if source = target then 0
    else dist (y.2 source) (y.1 source) ^ 2

/-- The off-target pair energy is continuous on the configuration-pair carrier. -/
theorem periodicHypercubicSpecialUnitary_offTargetPairEnergy_continuous
    (target : PeriodicHypercubicEdge n) :
    Continuous
      (periodicHypercubicSpecialUnitaryOffTargetPairEnergy
        n N hN beta beta_nonneg target) := by
  classical
  unfold periodicHypercubicSpecialUnitaryOffTargetPairEnergy
  apply continuous_finset_sum
  intro source _
  by_cases hSource : source = target
  · simp [hSource]
  · simp only [hSource, if_false]
    exact
      (((continuous_apply source).comp continuous_snd).dist
        ((continuous_apply source).comp continuous_fst)).pow 2

/-- Agreement away from the target forces the off-target pair energy to vanish. -/
theorem periodicHypercubicSpecialUnitary_offTargetPairEnergy_eq_zero_of_agreeOffLink
    (target : PeriodicHypercubicEdge n)
    (y :
      (periodicHypercubicSpecialUnitaryOneLinkSupportSystem
        n N hN beta beta_nonneg).base.Configuration ×
      (periodicHypercubicSpecialUnitaryOneLinkSupportSystem
        n N hN beta beta_nonneg).base.Configuration)
    (hAgree :
      (periodicHypercubicSpecialUnitaryOneLinkSupportSystem
        n N hN beta beta_nonneg).base.AgreeOffLink y.2 y.1 target) :
    periodicHypercubicSpecialUnitaryOffTargetPairEnergy
        n N hN beta beta_nonneg target y = 0 := by
  classical
  unfold periodicHypercubicSpecialUnitaryOffTargetPairEnergy
  apply Finset.sum_eq_zero
  intro source _
  by_cases hSource : source = target
  · simp [hSource]
  · simp [hSource, hAgree source hSource]

/-- Every canonical hybrid endpoint pair has zero off-target disagreement. -/
@[simp]
theorem periodicHypercubicSpecialUnitary_offTargetPairEnergy_hybridEndpointPairMap
    (target : PeriodicHypercubicEdge n)
    (z :
      (periodicHypercubicSpecialUnitaryOneLinkSupportSystem
        n N hN beta beta_nonneg).base.Configuration ×
      (periodicHypercubicSpecialUnitaryOneLinkSupportSystem
        n N hN beta beta_nonneg).base.Configuration) :
    periodicHypercubicSpecialUnitaryOffTargetPairEnergy
        n N hN beta beta_nonneg target
        ((periodicHypercubicSpecialUnitaryOneLinkSupportSystem
          n N hN beta beta_nonneg).independentPairHybridEndpointPairMap
            target z) = 0 := by
  exact
    periodicHypercubicSpecialUnitary_offTargetPairEnergy_eq_zero_of_agreeOffLink
      n N hN beta beta_nonneg target
      ((periodicHypercubicSpecialUnitaryOneLinkSupportSystem
        n N hN beta beta_nonneg).independentPairHybridEndpointPairMap target z)
      (continuous_compact_oriented_independentPairHybridEndpointPairMap_agreeOffLink
        (periodicHypercubicSpecialUnitaryOneLinkSupportSystem
          n N hN beta beta_nonneg) target z)

/-- Two native one-link conditional samples from the same background agree away
from the resampled target link. -/
theorem periodicHypercubicSpecialUnitary_singleLinkConditionalPairConfigurationMap_agreeOffLink
    (target : PeriodicHypercubicEdge n)
    (A :
      (periodicHypercubicSpecialUnitaryOneLinkSupportSystem
        n N hN beta beta_nonneg).base.Configuration)
    (z :
      (periodicHypercubicSpecialUnitaryOneLinkSupportSystem
        n N hN beta beta_nonneg).base.Gauge ×
      (periodicHypercubicSpecialUnitaryOneLinkSupportSystem
        n N hN beta beta_nonneg).base.Gauge) :
    (periodicHypercubicSpecialUnitaryOneLinkSupportSystem
      n N hN beta beta_nonneg).base.AgreeOffLink
      ((periodicHypercubicSpecialUnitaryOneLinkSupportSystem
        n N hN beta beta_nonneg).singleLinkConditionalPairConfigurationMap
          A target z).2
      ((periodicHypercubicSpecialUnitaryOneLinkSupportSystem
        n N hN beta beta_nonneg).singleLinkConditionalPairConfigurationMap
          A target z).1
      target := by
  intro source hSource
  simp [ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalPairConfigurationMap,
    CompactOrientedGaugeWilsonSystem.replaceLink, hSource]

/-- Every native conditional-pair generator value has zero off-target
configuration disagreement. -/
@[simp]
theorem periodicHypercubicSpecialUnitary_offTargetPairEnergy_singleLinkConditionalPairConfigurationMap
    (target : PeriodicHypercubicEdge n)
    (A :
      (periodicHypercubicSpecialUnitaryOneLinkSupportSystem
        n N hN beta beta_nonneg).base.Configuration)
    (z :
      (periodicHypercubicSpecialUnitaryOneLinkSupportSystem
        n N hN beta beta_nonneg).base.Gauge ×
      (periodicHypercubicSpecialUnitaryOneLinkSupportSystem
        n N hN beta beta_nonneg).base.Gauge) :
    periodicHypercubicSpecialUnitaryOffTargetPairEnergy
        n N hN beta beta_nonneg target
        ((periodicHypercubicSpecialUnitaryOneLinkSupportSystem
          n N hN beta beta_nonneg).singleLinkConditionalPairConfigurationMap
            A target z) = 0 := by
  exact
    periodicHypercubicSpecialUnitary_offTargetPairEnergy_eq_zero_of_agreeOffLink
      n N hN beta beta_nonneg target
      ((periodicHypercubicSpecialUnitaryOneLinkSupportSystem
        n N hN beta beta_nonneg).singleLinkConditionalPairConfigurationMap
          A target z)
      (periodicHypercubicSpecialUnitary_singleLinkConditionalPairConfigurationMap_agreeOffLink
        n N hN beta beta_nonneg target A z)

/-- The hybrid endpoint transport plan has exactly zero squared disagreement
away from its target physical link. -/
theorem periodicHypercubicSpecialUnitary_integral_offTargetPairEnergy_hybridEndpointPairMeasure
    (target : PeriodicHypercubicEdge n) :
    (∫ y :
        (periodicHypercubicSpecialUnitaryOneLinkSupportSystem
          n N hN beta beta_nonneg).base.Configuration ×
        (periodicHypercubicSpecialUnitaryOneLinkSupportSystem
          n N hN beta beta_nonneg).base.Configuration,
        periodicHypercubicSpecialUnitaryOffTargetPairEnergy
          n N hN beta beta_nonneg target y
        ∂(periodicHypercubicSpecialUnitaryOneLinkSupportSystem
          n N hN beta beta_nonneg).independentPairHybridEndpointPairMeasure
            target) = 0 := by
  rw [continuous_compact_oriented_integral_independentPairHybridEndpointPairMeasure
    (periodicHypercubicSpecialUnitaryOneLinkSupportSystem
      n N hN beta beta_nonneg) target
    (periodicHypercubicSpecialUnitaryOffTargetPairEnergy
      n N hN beta beta_nonneg target)
    (periodicHypercubicSpecialUnitary_offTargetPairEnergy_continuous
      n N hN beta beta_nonneg target).stronglyMeasurable]
  simp

/-- Pointwise in the Gibbs background, the native independent heat-bath pair
kernel has zero squared disagreement away from the target link. -/
theorem periodicHypercubicSpecialUnitary_integral_offTargetPairEnergy_singleLinkHeatBathIndependentPairKernel
    (target : PeriodicHypercubicEdge n)
    (A :
      (periodicHypercubicSpecialUnitaryOneLinkSupportSystem
        n N hN beta beta_nonneg).base.Configuration) :
    (∫ y :
        (periodicHypercubicSpecialUnitaryOneLinkSupportSystem
          n N hN beta beta_nonneg).base.Configuration ×
        (periodicHypercubicSpecialUnitaryOneLinkSupportSystem
          n N hN beta beta_nonneg).base.Configuration,
        periodicHypercubicSpecialUnitaryOffTargetPairEnergy
          n N hN beta beta_nonneg target y
        ∂(periodicHypercubicSpecialUnitaryOneLinkSupportSystem
          n N hN beta beta_nonneg).singleLinkHeatBathIndependentPairKernel
            target A) = 0 := by
  rw [continuous_compact_oriented_singleLinkHeatBathIndependentPairKernel_apply]
  calc
    (∫ y :
        (periodicHypercubicSpecialUnitaryOneLinkSupportSystem
          n N hN beta beta_nonneg).base.Configuration ×
        (periodicHypercubicSpecialUnitaryOneLinkSupportSystem
          n N hN beta beta_nonneg).base.Configuration,
        periodicHypercubicSpecialUnitaryOffTargetPairEnergy
          n N hN beta beta_nonneg target y
        ∂Measure.map
          ((periodicHypercubicSpecialUnitaryOneLinkSupportSystem
            n N hN beta beta_nonneg).singleLinkConditionalPairConfigurationMap
              A target)
          (((periodicHypercubicSpecialUnitaryOneLinkSupportSystem
            n N hN beta beta_nonneg).singleLinkConditionalMeasure A target).prod
            ((periodicHypercubicSpecialUnitaryOneLinkSupportSystem
              n N hN beta beta_nonneg).singleLinkConditionalMeasure A target))) =
      ∫ z :
        (periodicHypercubicSpecialUnitaryOneLinkSupportSystem
          n N hN beta beta_nonneg).base.Gauge ×
        (periodicHypercubicSpecialUnitaryOneLinkSupportSystem
          n N hN beta beta_nonneg).base.Gauge,
        periodicHypercubicSpecialUnitaryOffTargetPairEnergy
          n N hN beta beta_nonneg target
          ((periodicHypercubicSpecialUnitaryOneLinkSupportSystem
            n N hN beta beta_nonneg).singleLinkConditionalPairConfigurationMap
              A target z)
        ∂(((periodicHypercubicSpecialUnitaryOneLinkSupportSystem
          n N hN beta beta_nonneg).singleLinkConditionalMeasure A target).prod
          ((periodicHypercubicSpecialUnitaryOneLinkSupportSystem
            n N hN beta beta_nonneg).singleLinkConditionalMeasure A target)) := by
      exact MeasureTheory.integral_map
        (continuous_compact_oriented_singleLinkConditionalPairConfigurationMap_continuous
          (periodicHypercubicSpecialUnitaryOneLinkSupportSystem
            n N hN beta beta_nonneg) A target).measurable.aemeasurable
        (periodicHypercubicSpecialUnitary_offTargetPairEnergy_continuous
          n N hN beta beta_nonneg target).stronglyMeasurable.aestronglyMeasurable
    _ = 0 := by simp

/-- The Gibbs-averaged native conditional-pair reference law also has exactly
zero squared disagreement away from the target physical link. -/
theorem periodicHypercubicSpecialUnitary_integral_offTargetPairEnergy_singleLinkHeatBathIndependentPairMeasure
    (target : PeriodicHypercubicEdge n) :
    (∫ y :
        (periodicHypercubicSpecialUnitaryOneLinkSupportSystem
          n N hN beta beta_nonneg).base.Configuration ×
        (periodicHypercubicSpecialUnitaryOneLinkSupportSystem
          n N hN beta beta_nonneg).base.Configuration,
        periodicHypercubicSpecialUnitaryOffTargetPairEnergy
          n N hN beta beta_nonneg target y
        ∂(periodicHypercubicSpecialUnitaryOneLinkSupportSystem
          n N hN beta beta_nonneg).singleLinkHeatBathIndependentPairMeasure
            target) = 0 := by
  let C := periodicHypercubicSpecialUnitaryOneLinkSupportSystem
    n N hN beta beta_nonneg
  letI : IsProbabilityMeasure C.gibbsMeasure :=
    continuous_compact_oriented_gibbsMeasure_isProbabilityMeasure C
  have hIntReference : Integrable
      (periodicHypercubicSpecialUnitaryOffTargetPairEnergy
        n N hN beta beta_nonneg target)
      (C.singleLinkHeatBathIndependentPairMeasure target) := by
    letI : IsProbabilityMeasure
        (C.singleLinkHeatBathIndependentPairMeasure target) :=
      continuousCompactOriented_singleLinkHeatBathIndependentPairMeasure_isProbability
        C target
    exact
      (periodicHypercubicSpecialUnitary_offTargetPairEnergy_continuous
        n N hN beta beta_nonneg target).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hIntComp : Integrable
      (periodicHypercubicSpecialUnitaryOffTargetPairEnergy
        n N hN beta beta_nonneg target)
      (((C.singleLinkHeatBathIndependentPairKernel target) ∘ₖ
        Kernel.const Unit C.gibbsMeasure) ()) := by
    rw [← Measure.comp_eq_comp_const_apply]
    simpa
      [ContinuousCompactOrientedGaugeWilsonSystem.singleLinkHeatBathIndependentPairMeasure]
      using hIntReference
  change
    (∫ y : C.base.Configuration × C.base.Configuration,
        periodicHypercubicSpecialUnitaryOffTargetPairEnergy
          n N hN beta beta_nonneg target y
        ∂C.singleLinkHeatBathIndependentPairMeasure target) = 0
  calc
    (∫ y : C.base.Configuration × C.base.Configuration,
        periodicHypercubicSpecialUnitaryOffTargetPairEnergy
          n N hN beta beta_nonneg target y
        ∂C.singleLinkHeatBathIndependentPairMeasure target) =
      ∫ y : C.base.Configuration × C.base.Configuration,
        periodicHypercubicSpecialUnitaryOffTargetPairEnergy
          n N hN beta beta_nonneg target y
        ∂(((C.singleLinkHeatBathIndependentPairKernel target) ∘ₖ
          Kernel.const Unit C.gibbsMeasure) ()) := by
      rw [ContinuousCompactOrientedGaugeWilsonSystem.singleLinkHeatBathIndependentPairMeasure,
        Measure.comp_eq_comp_const_apply]
    _ = ∫ A,
        ∫ y : C.base.Configuration × C.base.Configuration,
          periodicHypercubicSpecialUnitaryOffTargetPairEnergy
            n N hN beta beta_nonneg target y
          ∂C.singleLinkHeatBathIndependentPairKernel target A
        ∂C.gibbsMeasure := by
      simpa [Kernel.const_apply] using
        (ProbabilityTheory.Kernel.integral_comp hIntComp)
    _ = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [] with A
      exact
        periodicHypercubicSpecialUnitary_integral_offTargetPairEnergy_singleLinkHeatBathIndependentPairKernel
          n N hN beta beta_nonneg target A

end PeriodicSpecialUnitary

end

end MathlibAnalytic
end MGAP4D
