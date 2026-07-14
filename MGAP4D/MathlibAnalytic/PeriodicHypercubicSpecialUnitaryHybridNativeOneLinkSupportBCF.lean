import MGAP4D.MathlibAnalytic.PeriodicHypercubicSpecialUnitaryNativeConditionalPairReferenceEnergyBCF
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory

noncomputable section

/-- Explicit periodic compact-Haar `SU(N)` Wilson system used by the support
certificates. -/
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

abbrev periodicHypercubicSpecialUnitaryOneLinkSupportConfiguration
    (n N : ℕ)
    [NeZero n]
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (beta_nonneg : 0 ≤ beta) : Type :=
  (periodicHypercubicSpecialUnitaryOneLinkSupportSystem
    n N hN beta beta_nonneg).base.Configuration

abbrev periodicHypercubicSpecialUnitaryOneLinkSupportGauge
    (n N : ℕ)
    [NeZero n]
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (beta_nonneg : 0 ≤ beta) : Type :=
  (periodicHypercubicSpecialUnitaryOneLinkSupportSystem
    n N hN beta beta_nonneg).base.Gauge

section PeriodicSpecialUnitary

variable
    (n N : ℕ)
    [NeZero n]
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (beta_nonneg : 0 ≤ beta)

/-- Expose one native gauge value as its actual ambient complex matrix. -/
def periodicHypercubicSpecialUnitaryOneLinkSupportGaugeMatrix
    (g : periodicHypercubicSpecialUnitaryOneLinkSupportGauge
      n N hN beta beta_nonneg) : Matrix (Fin N) (Fin N) ℂ := by
  change Matrix.specialUnitaryGroup (Fin N) ℂ at g
  exact g

/-- The native-gauge-to-ambient-matrix map is continuous. -/
theorem periodicHypercubicSpecialUnitary_oneLinkSupportGaugeMatrix_continuous :
    Continuous
      (periodicHypercubicSpecialUnitaryOneLinkSupportGaugeMatrix
        n N hN beta beta_nonneg) := by
  change Continuous
    ((↑) : Matrix.specialUnitaryGroup (Fin N) ℂ →
      Matrix (Fin N) (Fin N) ℂ)
  exact continuous_subtype_val

/-- Squared disagreement away from one target link, computed in the ambient
complex matrix carrier of `SU(N)`. -/
def periodicHypercubicSpecialUnitaryOffTargetPairEnergy
    (target : PeriodicHypercubicEdge n)
    (y :
      periodicHypercubicSpecialUnitaryOneLinkSupportConfiguration
          n N hN beta beta_nonneg ×
      periodicHypercubicSpecialUnitaryOneLinkSupportConfiguration
          n N hN beta beta_nonneg) : ℝ := by
  classical
  exact ∑ source : PeriodicHypercubicEdge n,
    if source = target then 0
    else ∑ i : Fin N, ∑ j : Fin N,
      ‖(periodicHypercubicSpecialUnitaryOneLinkSupportGaugeMatrix
          n N hN beta beta_nonneg (y.2 source)) i j -
        (periodicHypercubicSpecialUnitaryOneLinkSupportGaugeMatrix
          n N hN beta beta_nonneg (y.1 source)) i j‖ ^ 2

/-- The ambient-matrix off-target pair energy is continuous. -/
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
  · simpa [hSource] using
      (continuous_const : Continuous
        (fun _ :
          periodicHypercubicSpecialUnitaryOneLinkSupportConfiguration
              n N hN beta beta_nonneg ×
          periodicHypercubicSpecialUnitaryOneLinkSupportConfiguration
              n N hN beta beta_nonneg => (0 : ℝ)))
  · simp only [hSource, if_false]
    apply continuous_finset_sum
    intro i _
    apply continuous_finset_sum
    intro j _
    have hPostGauge : Continuous
        (fun y :
          periodicHypercubicSpecialUnitaryOneLinkSupportConfiguration
              n N hN beta beta_nonneg ×
          periodicHypercubicSpecialUnitaryOneLinkSupportConfiguration
              n N hN beta beta_nonneg => y.2 source) :=
      (continuous_apply source).comp continuous_snd
    have hPostMatrix : Continuous
        (fun y :
          periodicHypercubicSpecialUnitaryOneLinkSupportConfiguration
              n N hN beta beta_nonneg ×
          periodicHypercubicSpecialUnitaryOneLinkSupportConfiguration
              n N hN beta beta_nonneg =>
          periodicHypercubicSpecialUnitaryOneLinkSupportGaugeMatrix
            n N hN beta beta_nonneg (y.2 source)) :=
      (periodicHypercubicSpecialUnitary_oneLinkSupportGaugeMatrix_continuous
        n N hN beta beta_nonneg).comp hPostGauge
    have hPost : Continuous
        (fun y :
          periodicHypercubicSpecialUnitaryOneLinkSupportConfiguration
              n N hN beta beta_nonneg ×
          periodicHypercubicSpecialUnitaryOneLinkSupportConfiguration
              n N hN beta beta_nonneg =>
          (periodicHypercubicSpecialUnitaryOneLinkSupportGaugeMatrix
            n N hN beta beta_nonneg (y.2 source)) i j) :=
      (continuous_apply j).comp ((continuous_apply i).comp hPostMatrix)
    have hPreGauge : Continuous
        (fun y :
          periodicHypercubicSpecialUnitaryOneLinkSupportConfiguration
              n N hN beta beta_nonneg ×
          periodicHypercubicSpecialUnitaryOneLinkSupportConfiguration
              n N hN beta beta_nonneg => y.1 source) :=
      (continuous_apply source).comp continuous_fst
    have hPreMatrix : Continuous
        (fun y :
          periodicHypercubicSpecialUnitaryOneLinkSupportConfiguration
              n N hN beta beta_nonneg ×
          periodicHypercubicSpecialUnitaryOneLinkSupportConfiguration
              n N hN beta beta_nonneg =>
          periodicHypercubicSpecialUnitaryOneLinkSupportGaugeMatrix
            n N hN beta beta_nonneg (y.1 source)) :=
      (periodicHypercubicSpecialUnitary_oneLinkSupportGaugeMatrix_continuous
        n N hN beta beta_nonneg).comp hPreGauge
    have hPre : Continuous
        (fun y :
          periodicHypercubicSpecialUnitaryOneLinkSupportConfiguration
              n N hN beta beta_nonneg ×
          periodicHypercubicSpecialUnitaryOneLinkSupportConfiguration
              n N hN beta beta_nonneg =>
          (periodicHypercubicSpecialUnitaryOneLinkSupportGaugeMatrix
            n N hN beta beta_nonneg (y.1 source)) i j) :=
      (continuous_apply j).comp ((continuous_apply i).comp hPreMatrix)
    exact (hPost.sub hPre).norm.pow 2

/-- Agreement away from the target forces the off-target energy to vanish. -/
theorem periodicHypercubicSpecialUnitary_offTargetPairEnergy_eq_zero_of_agreeOffLink
    (target : PeriodicHypercubicEdge n)
    (y :
      periodicHypercubicSpecialUnitaryOneLinkSupportConfiguration
          n N hN beta beta_nonneg ×
      periodicHypercubicSpecialUnitaryOneLinkSupportConfiguration
          n N hN beta beta_nonneg)
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
  · rw [if_neg hSource, hAgree source hSource]
    simp

/-- Every canonical hybrid endpoint pair has zero off-target disagreement. -/
@[simp]
theorem periodicHypercubicSpecialUnitary_offTargetPairEnergy_hybridEndpointPairMap
    (target : PeriodicHypercubicEdge n)
    (z :
      periodicHypercubicSpecialUnitaryOneLinkSupportConfiguration
          n N hN beta beta_nonneg ×
      periodicHypercubicSpecialUnitaryOneLinkSupportConfiguration
          n N hN beta beta_nonneg) :
    periodicHypercubicSpecialUnitaryOffTargetPairEnergy
        n N hN beta beta_nonneg target
        ((periodicHypercubicSpecialUnitaryOneLinkSupportSystem
          n N hN beta beta_nonneg).independentPairHybridEndpointPairMap
            target z) = 0 :=
  periodicHypercubicSpecialUnitary_offTargetPairEnergy_eq_zero_of_agreeOffLink
    n N hN beta beta_nonneg target _
    (continuous_compact_oriented_independentPairHybridEndpointPairMap_agreeOffLink
      (periodicHypercubicSpecialUnitaryOneLinkSupportSystem
        n N hN beta beta_nonneg) target z)

/-- Two native conditional samples from one background agree off target. -/
theorem periodicHypercubicSpecialUnitary_singleLinkConditionalPairConfigurationMap_agreeOffLink
    (target : PeriodicHypercubicEdge n)
    (A : periodicHypercubicSpecialUnitaryOneLinkSupportConfiguration
      n N hN beta beta_nonneg)
    (z :
      periodicHypercubicSpecialUnitaryOneLinkSupportGauge
          n N hN beta beta_nonneg ×
      periodicHypercubicSpecialUnitaryOneLinkSupportGauge
          n N hN beta beta_nonneg) :
    (periodicHypercubicSpecialUnitaryOneLinkSupportSystem
      n N hN beta beta_nonneg).base.AgreeOffLink
      ((periodicHypercubicSpecialUnitaryOneLinkSupportSystem
        n N hN beta beta_nonneg).singleLinkConditionalPairConfigurationMap
          A target z).2
      ((periodicHypercubicSpecialUnitaryOneLinkSupportSystem
        n N hN beta beta_nonneg).singleLinkConditionalPairConfigurationMap
          A target z).1 target := by
  intro source hSource
  simp [ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalPairConfigurationMap,
    CompactOrientedGaugeWilsonSystem.replaceLink, hSource]

/-- Every native conditional-pair generator value has zero off-target energy. -/
@[simp]
theorem periodicHypercubicSpecialUnitary_offTargetPairEnergy_singleLinkConditionalPairConfigurationMap
    (target : PeriodicHypercubicEdge n)
    (A : periodicHypercubicSpecialUnitaryOneLinkSupportConfiguration
      n N hN beta beta_nonneg)
    (z :
      periodicHypercubicSpecialUnitaryOneLinkSupportGauge
          n N hN beta beta_nonneg ×
      periodicHypercubicSpecialUnitaryOneLinkSupportGauge
          n N hN beta beta_nonneg) :
    periodicHypercubicSpecialUnitaryOffTargetPairEnergy
        n N hN beta beta_nonneg target
        ((periodicHypercubicSpecialUnitaryOneLinkSupportSystem
          n N hN beta beta_nonneg).singleLinkConditionalPairConfigurationMap
            A target z) = 0 :=
  periodicHypercubicSpecialUnitary_offTargetPairEnergy_eq_zero_of_agreeOffLink
    n N hN beta beta_nonneg target _
    (periodicHypercubicSpecialUnitary_singleLinkConditionalPairConfigurationMap_agreeOffLink
      n N hN beta beta_nonneg target A z)

/-- The hybrid endpoint transport plan has zero integrated off-target energy. -/
theorem periodicHypercubicSpecialUnitary_integral_offTargetPairEnergy_hybridEndpointPairMeasure
    (target : PeriodicHypercubicEdge n) :
    (∫ y :
        periodicHypercubicSpecialUnitaryOneLinkSupportConfiguration
            n N hN beta beta_nonneg ×
        periodicHypercubicSpecialUnitaryOneLinkSupportConfiguration
            n N hN beta beta_nonneg,
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

/-- Pointwise in the Gibbs background, the native pair kernel has zero
integrated off-target energy. -/
theorem periodicHypercubicSpecialUnitary_integral_offTargetPairEnergy_singleLinkHeatBathIndependentPairKernel
    (target : PeriodicHypercubicEdge n)
    (A : periodicHypercubicSpecialUnitaryOneLinkSupportConfiguration
      n N hN beta beta_nonneg) :
    (∫ y :
        periodicHypercubicSpecialUnitaryOneLinkSupportConfiguration
            n N hN beta beta_nonneg ×
        periodicHypercubicSpecialUnitaryOneLinkSupportConfiguration
            n N hN beta beta_nonneg,
        periodicHypercubicSpecialUnitaryOffTargetPairEnergy
          n N hN beta beta_nonneg target y
        ∂(periodicHypercubicSpecialUnitaryOneLinkSupportSystem
          n N hN beta beta_nonneg).singleLinkHeatBathIndependentPairKernel
            target A) = 0 := by
  rw [continuous_compact_oriented_singleLinkHeatBathIndependentPairKernel_apply]
  exact (MeasureTheory.integral_map
    (continuous_compact_oriented_singleLinkConditionalPairConfigurationMap_continuous
      (periodicHypercubicSpecialUnitaryOneLinkSupportSystem
        n N hN beta beta_nonneg) A target).measurable.aemeasurable
    (periodicHypercubicSpecialUnitary_offTargetPairEnergy_continuous
      n N hN beta beta_nonneg target).stronglyMeasurable.aestronglyMeasurable).trans <| by
        simp

/-- The Gibbs-averaged native reference law has zero integrated off-target
energy. -/
theorem periodicHypercubicSpecialUnitary_integral_offTargetPairEnergy_singleLinkHeatBathIndependentPairMeasure
    (target : PeriodicHypercubicEdge n) :
    (∫ y :
        periodicHypercubicSpecialUnitaryOneLinkSupportConfiguration
            n N hN beta beta_nonneg ×
        periodicHypercubicSpecialUnitaryOneLinkSupportConfiguration
            n N hN beta beta_nonneg,
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
  calc
    (∫ y : C.base.Configuration × C.base.Configuration,
        periodicHypercubicSpecialUnitaryOffTargetPairEnergy
          n N hN beta beta_nonneg target y
        ∂C.singleLinkHeatBathIndependentPairMeasure target) =
      ∫ A,
        ∫ y : C.base.Configuration × C.base.Configuration,
          periodicHypercubicSpecialUnitaryOffTargetPairEnergy
            n N hN beta beta_nonneg target y
          ∂C.singleLinkHeatBathIndependentPairKernel target A
        ∂C.gibbsMeasure := by
      rw [ContinuousCompactOrientedGaugeWilsonSystem.singleLinkHeatBathIndependentPairMeasure,
        Measure.comp_eq_comp_const_apply]
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
