import MGAP4D.MathlibAnalytic.PeriodicHypercubicSpecialUnitaryNativeConditionalPairReferenceBCF
import MGAP4D.MathlibAnalytic.PeriodicHypercubicSpecialUnitaryHybridPairComponentResidualBCF

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory

noncomputable section

/-- The observable square difference is integrable against the Gibbs-averaged
native conditional-pair reference law. -/
theorem continuous_compact_oriented_integrable_singleLinkHeatBathIndependentPairMeasure_sqDiff
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    Integrable
      (fun y : C.base.Configuration × C.base.Configuration =>
        (O y.1 - O y.2) ^ 2)
      (C.singleLinkHeatBathIndependentPairMeasure target) := by
  letI : IsProbabilityMeasure
      (C.singleLinkHeatBathIndependentPairMeasure target) :=
    continuousCompactOriented_singleLinkHeatBathIndependentPairMeasure_isProbability
      C target
  exact
    (((O.continuous.comp continuous_fst).sub
      (O.continuous.comp continuous_snd)).pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

/-- Integrating observable square difference against the native reference law
is exactly Gibbs averaging the pointwise conditional independent-pair energy. -/
theorem continuous_compact_oriented_integral_singleLinkHeatBathIndependentPairMeasure_sqDiff
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    (∫ y : C.base.Configuration × C.base.Configuration,
        (O y.1 - O y.2) ^ 2
        ∂C.singleLinkHeatBathIndependentPairMeasure target) =
      ∫ A,
        C.singleLinkConditionalIndependentPairDifferenceEnergyBCF target O A
        ∂C.gibbsMeasure := by
  letI : IsProbabilityMeasure C.gibbsMeasure :=
    continuous_compact_oriented_gibbsMeasure_isProbabilityMeasure C
  have hIntComp : Integrable
      (fun y : C.base.Configuration × C.base.Configuration =>
        (O y.1 - O y.2) ^ 2)
      (((C.singleLinkHeatBathIndependentPairKernel target) ∘ₖ
        Kernel.const Unit C.gibbsMeasure) ()) := by
    rw [← Measure.comp_eq_comp_const_apply]
    simpa
      [ContinuousCompactOrientedGaugeWilsonSystem.singleLinkHeatBathIndependentPairMeasure]
      using
        continuous_compact_oriented_integrable_singleLinkHeatBathIndependentPairMeasure_sqDiff
          C target O
  calc
    (∫ y : C.base.Configuration × C.base.Configuration,
        (O y.1 - O y.2) ^ 2
        ∂C.singleLinkHeatBathIndependentPairMeasure target) =
        ∫ y : C.base.Configuration × C.base.Configuration,
          (O y.1 - O y.2) ^ 2
          ∂(((C.singleLinkHeatBathIndependentPairKernel target) ∘ₖ
            Kernel.const Unit C.gibbsMeasure) ()) := by
      rw [ContinuousCompactOrientedGaugeWilsonSystem.singleLinkHeatBathIndependentPairMeasure,
        Measure.comp_eq_comp_const_apply]
    _ = ∫ A,
        ∫ y : C.base.Configuration × C.base.Configuration,
          (O y.1 - O y.2) ^ 2
          ∂C.singleLinkHeatBathIndependentPairKernel target A
        ∂C.gibbsMeasure := by
      simpa [Kernel.const_apply] using
        (ProbabilityTheory.Kernel.integral_comp hIntComp)
    _ = ∫ A,
        C.singleLinkConditionalIndependentPairDifferenceEnergyBCF target O A
        ∂C.gibbsMeasure := by
      apply integral_congr_ae
      filter_upwards [] with A
      exact
        continuous_compact_oriented_integral_singleLinkHeatBathIndependentPairKernel_sqDiff
          C target O A

/-- The native conditional-pair profile squared is represented directly as
square-difference energy under the configuration-pair reference law. -/
theorem continuous_compact_oriented_integral_singleLinkHeatBathIndependentPairMeasure_sqDiff_eq_profile_sq
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    (∫ y : C.base.Configuration × C.base.Configuration,
        (O y.1 - O y.2) ^ 2
        ∂C.singleLinkHeatBathIndependentPairMeasure target) =
      (C.singleLinkConditionalPairProfileBCF target O) ^ 2 := by
  calc
    (∫ y : C.base.Configuration × C.base.Configuration,
        (O y.1 - O y.2) ^ 2
        ∂C.singleLinkHeatBathIndependentPairMeasure target) =
        ∫ A,
          C.singleLinkConditionalIndependentPairDifferenceEnergyBCF target O A
          ∂C.gibbsMeasure :=
      continuous_compact_oriented_integral_singleLinkHeatBathIndependentPairMeasure_sqDiff
        C target O
    _ = (C.singleLinkConditionalPairProfileBCF target O) ^ 2 :=
      (continuous_compact_oriented_singleLinkConditionalPairProfileBCF_sq
        C target O).symm

/-- The reference-law square-difference energy is twice the squared local
heat-bath fluctuation norm. -/
theorem continuous_compact_oriented_integral_singleLinkHeatBathIndependentPairMeasure_sqDiff_eq_two_mul_norm_sq
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    (∫ y : C.base.Configuration × C.base.Configuration,
        (O y.1 - O y.2) ^ 2
        ∂C.singleLinkHeatBathIndependentPairMeasure target) =
      2 * ‖C.singleLinkHeatBathFluctuationL2 target
        (C.gibbsL2RepresentativeBCF O)‖ ^ 2 := by
  calc
    (∫ y : C.base.Configuration × C.base.Configuration,
        (O y.1 - O y.2) ^ 2
        ∂C.singleLinkHeatBathIndependentPairMeasure target) =
        ∫ A,
          C.singleLinkConditionalIndependentPairDifferenceEnergyBCF target O A
          ∂C.gibbsMeasure :=
      continuous_compact_oriented_integral_singleLinkHeatBathIndependentPairMeasure_sqDiff
        C target O
    _ = 2 * ‖C.singleLinkHeatBathFluctuationL2 target
        (C.gibbsL2RepresentativeBCF O)‖ ^ 2 :=
      continuous_compact_oriented_integral_singleLinkConditionalIndependentPairDifferenceEnergyBCF_eq_two_mul_norm_sq
        C target O

/-- Summing the native reference-law square-difference energies over all
physical links gives twice the native heat-bath Hamiltonian quadratic form. -/
theorem continuous_compact_oriented_sum_integral_singleLinkHeatBathIndependentPairMeasure_sqDiff_eq_two_mul_hamiltonian
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    (∑ target : C.base.geometry.Edge,
      ∫ y : C.base.Configuration × C.base.Configuration,
        (O y.1 - O y.2) ^ 2
        ∂C.singleLinkHeatBathIndependentPairMeasure target) =
      2 * inner ℝ
        (C.heatBathHamiltonianL2 (C.gibbsL2RepresentativeBCF O))
        (C.gibbsL2RepresentativeBCF O) := by
  calc
    (∑ target : C.base.geometry.Edge,
      ∫ y : C.base.Configuration × C.base.Configuration,
        (O y.1 - O y.2) ^ 2
        ∂C.singleLinkHeatBathIndependentPairMeasure target) =
        ∑ target : C.base.geometry.Edge,
          ∫ A,
            C.singleLinkConditionalIndependentPairDifferenceEnergyBCF target O A
            ∂C.gibbsMeasure := by
      apply Finset.sum_congr rfl
      intro target _
      exact
        continuous_compact_oriented_integral_singleLinkHeatBathIndependentPairMeasure_sqDiff
          C target O
    _ = 2 * inner ℝ
        (C.heatBathHamiltonianL2 (C.gibbsL2RepresentativeBCF O))
        (C.gibbsL2RepresentativeBCF O) :=
      continuous_compact_oriented_sum_integral_singleLinkConditionalIndependentPairDifferenceEnergyBCF_eq_two_mul_hamiltonian
        C O

end

end MathlibAnalytic
end MGAP4D
