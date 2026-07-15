import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridBoundaryResamplingFluctuationDecompositionBCF
import MGAP4D.MathlibAnalytic.PeriodicHypercubicSpecialUnitaryHybridPairProfileEnergyBCF
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

noncomputable section

/-- The boundary-target actual/resampled coupling is a probability measure. -/
instance continuousCompactOriented_independentPairHybridBoundaryResamplingCouplingMeasure_isProbability
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    IsProbabilityMeasure
      (C.independentPairHybridBoundaryResamplingCouplingMeasure target) := by
  letI : IsProbabilityMeasure C.gibbsMeasure :=
    continuous_compact_oriented_gibbsMeasure_isProbabilityMeasure C
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridBoundaryResamplingCouplingMeasure
  infer_instance

/-- The reconstructed configuration-level actual/resampled coupling is a
probability measure. -/
instance continuousCompactOriented_independentPairHybridBoundaryResamplingConfigurationCouplingMeasure_isProbability
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    IsProbabilityMeasure
      (C.independentPairHybridBoundaryResamplingConfigurationCouplingMeasure target) := by
  letI : IsProbabilityMeasure
      (C.independentPairHybridBoundaryResamplingCouplingMeasure target) :=
    continuousCompactOriented_independentPairHybridBoundaryResamplingCouplingMeasure_isProbability
      C target
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridBoundaryResamplingConfigurationCouplingMeasure
  exact Measure.isProbabilityMeasure_map
    (continuous_compact_oriented_independentPairHybridBoundaryResamplingConfigurationCouplingMap_continuous
      C target).measurable.aemeasurable

/-- The heat-bath fluctuation difference on a configuration pair is strongly
measurable. -/
theorem continuous_compact_oriented_configurationPairHeatBathFluctuationDifferenceBCF_stronglyMeasurable
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    StronglyMeasurable
      (C.configurationPairHeatBathFluctuationDifferenceBCF target O) := by
  have hFluctuation :=
    continuous_compact_oriented_singleLinkHeatBathFluctuation_stronglyMeasurable
      C target O O.continuous.stronglyMeasurable
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.configurationPairHeatBathFluctuationDifferenceBCF
  exact
    (hFluctuation.comp_measurable measurable_snd).sub
      (hFluctuation.comp_measurable measurable_fst)

/-- The actual-side fluctuation difference is strongly measurable on the
configuration-level coupling carrier. -/
theorem continuous_compact_oriented_independentPairHybridBoundaryResamplingActualDifferenceBCF_stronglyMeasurable
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    StronglyMeasurable
      (C.independentPairHybridBoundaryResamplingActualDifferenceBCF target O) := by
  simpa
    [ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridBoundaryResamplingActualDifferenceBCF]
    using
      (continuous_compact_oriented_configurationPairHeatBathFluctuationDifferenceBCF_stronglyMeasurable
        C target O).comp_measurable measurable_fst

/-- The resampled-side fluctuation difference is strongly measurable on the
configuration-level coupling carrier. -/
theorem continuous_compact_oriented_independentPairHybridBoundaryResamplingResampledDifferenceBCF_stronglyMeasurable
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    StronglyMeasurable
      (C.independentPairHybridBoundaryResamplingResampledDifferenceBCF target O) := by
  simpa
    [ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridBoundaryResamplingResampledDifferenceBCF]
    using
      (continuous_compact_oriented_configurationPairHeatBathFluctuationDifferenceBCF_stronglyMeasurable
        C target O).comp_measurable measurable_snd

/-- The first endpoint transport residual is strongly measurable. -/
theorem continuous_compact_oriented_independentPairHybridBoundaryResamplingFirstResidualBCF_stronglyMeasurable
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    StronglyMeasurable
      (C.independentPairHybridBoundaryResamplingFirstResidualBCF target O) := by
  have hFluctuation :=
    continuous_compact_oriented_singleLinkHeatBathFluctuation_stronglyMeasurable
      C target O O.continuous.stronglyMeasurable
  have h21 : Measurable
      (fun z : (C.base.Configuration × C.base.Configuration) ×
        (C.base.Configuration × C.base.Configuration) => z.2.1) :=
    measurable_fst.comp measurable_snd
  have h11 : Measurable
      (fun z : (C.base.Configuration × C.base.Configuration) ×
        (C.base.Configuration × C.base.Configuration) => z.1.1) :=
    measurable_fst.comp measurable_fst
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridBoundaryResamplingFirstResidualBCF
  exact
    (hFluctuation.comp_measurable h21).sub
      (hFluctuation.comp_measurable h11)

/-- The second endpoint transport residual is strongly measurable. -/
theorem continuous_compact_oriented_independentPairHybridBoundaryResamplingSecondResidualBCF_stronglyMeasurable
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    StronglyMeasurable
      (C.independentPairHybridBoundaryResamplingSecondResidualBCF target O) := by
  have hFluctuation :=
    continuous_compact_oriented_singleLinkHeatBathFluctuation_stronglyMeasurable
      C target O O.continuous.stronglyMeasurable
  have h12 : Measurable
      (fun z : (C.base.Configuration × C.base.Configuration) ×
        (C.base.Configuration × C.base.Configuration) => z.1.2) :=
    measurable_snd.comp measurable_fst
  have h22 : Measurable
      (fun z : (C.base.Configuration × C.base.Configuration) ×
        (C.base.Configuration × C.base.Configuration) => z.2.2) :=
    measurable_snd.comp measurable_snd
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridBoundaryResamplingSecondResidualBCF
  exact
    (hFluctuation.comp_measurable h12).sub
      (hFluctuation.comp_measurable h22)

private theorem continuous_compact_oriented_heatBathFluctuation_sub_abs_le_four_norm
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (A B : C.base.Configuration) :
    |C.singleLinkHeatBathFluctuation target O A -
      C.singleLinkHeatBathFluctuation target O B| ≤ 4 * ‖O‖ := by
  have hOBound : ∀ X : C.base.Configuration, |O X| ≤ ‖O‖ := by
    intro X
    simpa [Real.norm_eq_abs] using O.norm_coe_le_norm X
  have hA :=
    continuous_compact_oriented_singleLinkHeatBathFluctuation_abs_le
      C target O O.continuous.stronglyMeasurable ‖O‖ (norm_nonneg O)
      hOBound A
  have hB :=
    continuous_compact_oriented_singleLinkHeatBathFluctuation_abs_le
      C target O O.continuous.stronglyMeasurable ‖O‖ (norm_nonneg O)
      hOBound B
  calc
    |C.singleLinkHeatBathFluctuation target O A -
        C.singleLinkHeatBathFluctuation target O B| ≤
      |C.singleLinkHeatBathFluctuation target O A| +
        |C.singleLinkHeatBathFluctuation target O B| := abs_sub _ _
    _ ≤ 2 * ‖O‖ + 2 * ‖O‖ := add_le_add hA hB
    _ = 4 * ‖O‖ := by ring

/-- Every configuration-pair heat-bath fluctuation difference is bounded by four
times the bounded-continuous observable norm. -/
theorem continuous_compact_oriented_configurationPairHeatBathFluctuationDifferenceBCF_abs_le
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (y : C.base.Configuration × C.base.Configuration) :
    |C.configurationPairHeatBathFluctuationDifferenceBCF target O y| ≤
      4 * ‖O‖ := by
  simpa
    [ContinuousCompactOrientedGaugeWilsonSystem.configurationPairHeatBathFluctuationDifferenceBCF]
    using
      continuous_compact_oriented_heatBathFluctuation_sub_abs_le_four_norm
        C target O y.2 y.1

/-- The first transport residual has the same uniform four-norm bound. -/
theorem continuous_compact_oriented_independentPairHybridBoundaryResamplingFirstResidualBCF_abs_le
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : (C.base.Configuration × C.base.Configuration) ×
      (C.base.Configuration × C.base.Configuration)) :
    |C.independentPairHybridBoundaryResamplingFirstResidualBCF target O z| ≤
      4 * ‖O‖ := by
  simpa
    [ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridBoundaryResamplingFirstResidualBCF]
    using
      continuous_compact_oriented_heatBathFluctuation_sub_abs_le_four_norm
        C target O z.2.1 z.1.1

/-- The second transport residual has the same uniform four-norm bound. -/
theorem continuous_compact_oriented_independentPairHybridBoundaryResamplingSecondResidualBCF_abs_le
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : (C.base.Configuration × C.base.Configuration) ×
      (C.base.Configuration × C.base.Configuration)) :
    |C.independentPairHybridBoundaryResamplingSecondResidualBCF target O z| ≤
      4 * ‖O‖ := by
  simpa
    [ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridBoundaryResamplingSecondResidualBCF]
    using
      continuous_compact_oriented_heatBathFluctuation_sub_abs_le_four_norm
        C target O z.1.2 z.2.2

private theorem continuous_compact_oriented_sq_integrable_of_abs_le_four_norm
    {C : ContinuousCompactOrientedGaugeWilsonSystem}
    {α : Type*}
    [MeasurableSpace α]
    (μ : Measure α)
    [IsFiniteMeasure μ]
    (f : α → ℝ)
    (hf : StronglyMeasurable f)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (hBound : ∀ x, |f x| ≤ 4 * ‖O‖) :
    Integrable (fun x => (f x) ^ 2) μ := by
  let M : ℝ := (4 * ‖O‖) ^ 2
  apply continuous_compact_oriented_integrable_of_uniform_bound
    μ (fun x => (f x) ^ 2)
    (by simpa [pow_two] using hf.mul hf) M
  intro x
  have hAbs := hBound x
  have hBounds := abs_le.mp hAbs
  rw [abs_of_nonneg (sq_nonneg _)]
  dsimp [M]
  nlinarith [norm_nonneg O]

/-- Squared actual-side fluctuation differences are integrable under the
configuration-level coupling. -/
theorem continuous_compact_oriented_independentPairHybridBoundaryResamplingActualDifferenceBCF_sq_integrable
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    Integrable
      (fun z =>
        (C.independentPairHybridBoundaryResamplingActualDifferenceBCF
          target O z) ^ 2)
      (C.independentPairHybridBoundaryResamplingConfigurationCouplingMeasure
        target) := by
  letI : IsProbabilityMeasure
      (C.independentPairHybridBoundaryResamplingConfigurationCouplingMeasure
        target) :=
    continuousCompactOriented_independentPairHybridBoundaryResamplingConfigurationCouplingMeasure_isProbability
      C target
  apply continuous_compact_oriented_sq_integrable_of_abs_le_four_norm
    (C.independentPairHybridBoundaryResamplingConfigurationCouplingMeasure target)
    (C.independentPairHybridBoundaryResamplingActualDifferenceBCF target O)
    (continuous_compact_oriented_independentPairHybridBoundaryResamplingActualDifferenceBCF_stronglyMeasurable
      C target O) O
  intro z
  simpa
    [ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridBoundaryResamplingActualDifferenceBCF]
    using
      continuous_compact_oriented_configurationPairHeatBathFluctuationDifferenceBCF_abs_le
        C target O z.1

/-- Squared resampled-side fluctuation differences are integrable under the
configuration-level coupling. -/
theorem continuous_compact_oriented_independentPairHybridBoundaryResamplingResampledDifferenceBCF_sq_integrable
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    Integrable
      (fun z =>
        (C.independentPairHybridBoundaryResamplingResampledDifferenceBCF
          target O z) ^ 2)
      (C.independentPairHybridBoundaryResamplingConfigurationCouplingMeasure
        target) := by
  letI : IsProbabilityMeasure
      (C.independentPairHybridBoundaryResamplingConfigurationCouplingMeasure
        target) :=
    continuousCompactOriented_independentPairHybridBoundaryResamplingConfigurationCouplingMeasure_isProbability
      C target
  apply continuous_compact_oriented_sq_integrable_of_abs_le_four_norm
    (C.independentPairHybridBoundaryResamplingConfigurationCouplingMeasure target)
    (C.independentPairHybridBoundaryResamplingResampledDifferenceBCF target O)
    (continuous_compact_oriented_independentPairHybridBoundaryResamplingResampledDifferenceBCF_stronglyMeasurable
      C target O) O
  intro z
  simpa
    [ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridBoundaryResamplingResampledDifferenceBCF]
    using
      continuous_compact_oriented_configurationPairHeatBathFluctuationDifferenceBCF_abs_le
        C target O z.2

/-- Squared first endpoint residuals are integrable under the configuration-level
coupling. -/
theorem continuous_compact_oriented_independentPairHybridBoundaryResamplingFirstResidualBCF_sq_integrable
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    Integrable
      (fun z =>
        (C.independentPairHybridBoundaryResamplingFirstResidualBCF target O z) ^ 2)
      (C.independentPairHybridBoundaryResamplingConfigurationCouplingMeasure
        target) := by
  letI : IsProbabilityMeasure
      (C.independentPairHybridBoundaryResamplingConfigurationCouplingMeasure
        target) :=
    continuousCompactOriented_independentPairHybridBoundaryResamplingConfigurationCouplingMeasure_isProbability
      C target
  exact continuous_compact_oriented_sq_integrable_of_abs_le_four_norm
    (C.independentPairHybridBoundaryResamplingConfigurationCouplingMeasure target)
    (C.independentPairHybridBoundaryResamplingFirstResidualBCF target O)
    (continuous_compact_oriented_independentPairHybridBoundaryResamplingFirstResidualBCF_stronglyMeasurable
      C target O) O
    (continuous_compact_oriented_independentPairHybridBoundaryResamplingFirstResidualBCF_abs_le
      C target O)

/-- Squared second endpoint residuals are integrable under the
configuration-level coupling. -/
theorem continuous_compact_oriented_independentPairHybridBoundaryResamplingSecondResidualBCF_sq_integrable
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    Integrable
      (fun z =>
        (C.independentPairHybridBoundaryResamplingSecondResidualBCF target O z) ^ 2)
      (C.independentPairHybridBoundaryResamplingConfigurationCouplingMeasure
        target) := by
  letI : IsProbabilityMeasure
      (C.independentPairHybridBoundaryResamplingConfigurationCouplingMeasure
        target) :=
    continuousCompactOriented_independentPairHybridBoundaryResamplingConfigurationCouplingMeasure_isProbability
      C target
  exact continuous_compact_oriented_sq_integrable_of_abs_le_four_norm
    (C.independentPairHybridBoundaryResamplingConfigurationCouplingMeasure target)
    (C.independentPairHybridBoundaryResamplingSecondResidualBCF target O)
    (continuous_compact_oriented_independentPairHybridBoundaryResamplingSecondResidualBCF_stronglyMeasurable
      C target O) O
    (continuous_compact_oriented_independentPairHybridBoundaryResamplingSecondResidualBCF_abs_le
      C target O)

/-- On every reconstructed common-boundary target pair, the difference of
heat-bath fluctuations is exactly the observable difference because the two
projection terms coincide on the common off-target fiber. -/
theorem continuous_compact_oriented_configurationPairHeatBathFluctuationDifferenceBCF_reconstruct
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.OffTargetBoundaryTargetPair target) :
    C.configurationPairHeatBathFluctuationDifferenceBCF target O
        (C.offTargetBoundaryTargetPairConfigurationPairMap target z) =
      O (C.offTargetBoundaryTargetPairConfigurationPairMap target z).2 -
        O (C.offTargetBoundaryTargetPairConfigurationPairMap target z).1 := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.configurationPairHeatBathFluctuationDifferenceBCF
    ContinuousCompactOrientedGaugeWilsonSystem.offTargetBoundaryTargetPairConfigurationPairMap
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalPairConfigurationMap
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkHeatBathFluctuation
  simp only [Pi.sub_apply]
  rw [continuous_compact_oriented_singleLinkHeatBathProjection_replaceLink
      C O (C.offTargetBoundarySection target z.1) target z.2.2,
    continuous_compact_oriented_singleLinkHeatBathProjection_replaceLink
      C O (C.offTargetBoundarySection target z.1) target z.2.1]
  ring

/-- Conditional-pair observable energy under the hybrid boundary input law. -/
def ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridBoundaryResampledConditionalPairEnergyBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) : ℝ :=
  ∫ y : C.base.Configuration × C.base.Configuration,
    (O y.2 - O y.1) ^ 2
    ∂C.independentPairHybridBoundaryResampledConfigurationPairMeasure target

/-- The resampled conditional-pair energy is nonnegative. -/
theorem continuous_compact_oriented_independentPairHybridBoundaryResampledConditionalPairEnergyBCF_nonneg
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    0 ≤ C.independentPairHybridBoundaryResampledConditionalPairEnergyBCF target O := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridBoundaryResampledConditionalPairEnergyBCF
  exact integral_nonneg fun _ => sq_nonneg _

/-- Under the reconstructed boundary-resampled law, fluctuation-difference energy
is exactly observable conditional-pair energy. -/
theorem continuous_compact_oriented_integral_independentPairHybridBoundaryResampledConfigurationPairMeasure_fluctuationDifference_sq
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    (∫ y : C.base.Configuration × C.base.Configuration,
        (C.configurationPairHeatBathFluctuationDifferenceBCF target O y) ^ 2
        ∂C.independentPairHybridBoundaryResampledConfigurationPairMeasure target) =
      C.independentPairHybridBoundaryResampledConditionalPairEnergyBCF target O := by
  have hDiffSq : StronglyMeasurable
      (fun y : C.base.Configuration × C.base.Configuration =>
        (C.configurationPairHeatBathFluctuationDifferenceBCF target O y) ^ 2) := by
    have hDiff :=
      continuous_compact_oriented_configurationPairHeatBathFluctuationDifferenceBCF_stronglyMeasurable
        C target O
    simpa [pow_two] using hDiff.mul hDiff
  have hObservableSq : StronglyMeasurable
      (fun y : C.base.Configuration × C.base.Configuration =>
        (O y.2 - O y.1) ^ 2) :=
    (((O.continuous.comp continuous_snd).sub
      (O.continuous.comp continuous_fst)).pow 2).stronglyMeasurable
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridBoundaryResampledConfigurationPairMeasure
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridBoundaryResampledConditionalPairEnergyBCF
  rw [MeasureTheory.integral_map
    (continuous_compact_oriented_offTargetBoundaryTargetPairConfigurationPairMap_measurable
      C target).aemeasurable hDiffSq.aestronglyMeasurable]
  rw [MeasureTheory.integral_map
    (continuous_compact_oriented_offTargetBoundaryTargetPairConfigurationPairMap_measurable
      C target).aemeasurable hObservableSq.aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards [] with z
  rw [continuous_compact_oriented_configurationPairHeatBathFluctuationDifferenceBCF_reconstruct
    C target O z]

/-- Mean-square first endpoint transport residual. -/
def ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridBoundaryResamplingFirstResidualEnergyBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) : ℝ :=
  ∫ z,
    (C.independentPairHybridBoundaryResamplingFirstResidualBCF target O z) ^ 2
    ∂C.independentPairHybridBoundaryResamplingConfigurationCouplingMeasure target

/-- Mean-square second endpoint transport residual. -/
def ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridBoundaryResamplingSecondResidualEnergyBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) : ℝ :=
  ∫ z,
    (C.independentPairHybridBoundaryResamplingSecondResidualBCF target O z) ^ 2
    ∂C.independentPairHybridBoundaryResamplingConfigurationCouplingMeasure target

/-- The first endpoint residual energy is nonnegative. -/
theorem continuous_compact_oriented_independentPairHybridBoundaryResamplingFirstResidualEnergyBCF_nonneg
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    0 ≤ C.independentPairHybridBoundaryResamplingFirstResidualEnergyBCF target O := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridBoundaryResamplingFirstResidualEnergyBCF
  exact integral_nonneg fun _ => sq_nonneg _

/-- The second endpoint residual energy is nonnegative. -/
theorem continuous_compact_oriented_independentPairHybridBoundaryResamplingSecondResidualEnergyBCF_nonneg
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    0 ≤ C.independentPairHybridBoundaryResamplingSecondResidualEnergyBCF target O := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridBoundaryResamplingSecondResidualEnergyBCF
  exact integral_nonneg fun _ => sq_nonneg _

/-- The actual-side coupling integral is exactly the canonical hybrid increment
energy. -/
theorem continuous_compact_oriented_integral_independentPairHybridBoundaryResamplingActualDifferenceBCF_sq_eq_incrementEnergy
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    (∫ z,
        (C.independentPairHybridBoundaryResamplingActualDifferenceBCF target O z) ^ 2
        ∂C.independentPairHybridBoundaryResamplingConfigurationCouplingMeasure target) =
      C.independentPairHybridIncrementEnergyBCF target O := by
  have hDiffSq : StronglyMeasurable
      (fun y : C.base.Configuration × C.base.Configuration =>
        (C.configurationPairHeatBathFluctuationDifferenceBCF target O y) ^ 2) := by
    have hDiff :=
      continuous_compact_oriented_configurationPairHeatBathFluctuationDifferenceBCF_stronglyMeasurable
        C target O
    simpa [pow_two] using hDiff.mul hDiff
  calc
    (∫ z,
        (C.independentPairHybridBoundaryResamplingActualDifferenceBCF target O z) ^ 2
        ∂C.independentPairHybridBoundaryResamplingConfigurationCouplingMeasure target) =
      ∫ y,
        (C.configurationPairHeatBathFluctuationDifferenceBCF target O y) ^ 2
        ∂Measure.map Prod.fst
          (C.independentPairHybridBoundaryResamplingConfigurationCouplingMeasure target) := by
      symm
      simpa
        [ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridBoundaryResamplingActualDifferenceBCF]
        using
          (MeasureTheory.integral_map measurable_fst.aemeasurable
            hDiffSq.aestronglyMeasurable)
    _ = ∫ y,
        (C.configurationPairHeatBathFluctuationDifferenceBCF target O y) ^ 2
        ∂C.independentPairHybridEndpointPairMeasure target := by
      rw [continuous_compact_oriented_map_actual_independentPairHybridBoundaryResamplingConfigurationCoupling]
    _ = C.independentPairHybridIncrementEnergyBCF target O := by
      simpa
        [ContinuousCompactOrientedGaugeWilsonSystem.configurationPairHeatBathFluctuationDifferenceBCF]
        using
          (continuous_compact_oriented_independentPairHybridIncrementEnergyBCF_eq_endpointPairMeasure
            C target O).symm

/-- The resampled-side coupling integral is exactly the hybrid-boundary-driven
conditional-pair observable energy. -/
theorem continuous_compact_oriented_integral_independentPairHybridBoundaryResamplingResampledDifferenceBCF_sq_eq_conditionalPairEnergy
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    (∫ z,
        (C.independentPairHybridBoundaryResamplingResampledDifferenceBCF target O z) ^ 2
        ∂C.independentPairHybridBoundaryResamplingConfigurationCouplingMeasure target) =
      C.independentPairHybridBoundaryResampledConditionalPairEnergyBCF target O := by
  have hDiffSq : StronglyMeasurable
      (fun y : C.base.Configuration × C.base.Configuration =>
        (C.configurationPairHeatBathFluctuationDifferenceBCF target O y) ^ 2) := by
    have hDiff :=
      continuous_compact_oriented_configurationPairHeatBathFluctuationDifferenceBCF_stronglyMeasurable
        C target O
    simpa [pow_two] using hDiff.mul hDiff
  calc
    (∫ z,
        (C.independentPairHybridBoundaryResamplingResampledDifferenceBCF target O z) ^ 2
        ∂C.independentPairHybridBoundaryResamplingConfigurationCouplingMeasure target) =
      ∫ y,
        (C.configurationPairHeatBathFluctuationDifferenceBCF target O y) ^ 2
        ∂Measure.map Prod.snd
          (C.independentPairHybridBoundaryResamplingConfigurationCouplingMeasure target) := by
      symm
      simpa
        [ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridBoundaryResamplingResampledDifferenceBCF]
        using
          (MeasureTheory.integral_map measurable_snd.aemeasurable
            hDiffSq.aestronglyMeasurable)
    _ = ∫ y,
        (C.configurationPairHeatBathFluctuationDifferenceBCF target O y) ^ 2
        ∂C.independentPairHybridBoundaryResampledConfigurationPairMeasure target := by
      rw [continuous_compact_oriented_map_resampled_independentPairHybridBoundaryResamplingConfigurationCoupling]
    _ = C.independentPairHybridBoundaryResampledConditionalPairEnergyBCF target O :=
      continuous_compact_oriented_integral_independentPairHybridBoundaryResampledConfigurationPairMeasure_fluctuationDifference_sq
        C target O

/-- Integrated form of the actual/resampled three-term square decomposition. -/
theorem continuous_compact_oriented_independentPairHybridIncrementEnergyBCF_le_three_boundaryResampling
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    C.independentPairHybridIncrementEnergyBCF target O ≤
      3 *
        (C.independentPairHybridBoundaryResamplingFirstResidualEnergyBCF target O +
         C.independentPairHybridBoundaryResampledConditionalPairEnergyBCF target O +
         C.independentPairHybridBoundaryResamplingSecondResidualEnergyBCF target O) := by
  let μ :=
    C.independentPairHybridBoundaryResamplingConfigurationCouplingMeasure target
  have hActual : Integrable
      (fun z =>
        (C.independentPairHybridBoundaryResamplingActualDifferenceBCF target O z) ^ 2) μ := by
    simpa [μ] using
      continuous_compact_oriented_independentPairHybridBoundaryResamplingActualDifferenceBCF_sq_integrable
        C target O
  have hFirst : Integrable
      (fun z =>
        (C.independentPairHybridBoundaryResamplingFirstResidualBCF target O z) ^ 2) μ := by
    simpa [μ] using
      continuous_compact_oriented_independentPairHybridBoundaryResamplingFirstResidualBCF_sq_integrable
        C target O
  have hResampled : Integrable
      (fun z =>
        (C.independentPairHybridBoundaryResamplingResampledDifferenceBCF target O z) ^ 2) μ := by
    simpa [μ] using
      continuous_compact_oriented_independentPairHybridBoundaryResamplingResampledDifferenceBCF_sq_integrable
        C target O
  have hSecond : Integrable
      (fun z =>
        (C.independentPairHybridBoundaryResamplingSecondResidualBCF target O z) ^ 2) μ := by
    simpa [μ] using
      continuous_compact_oriented_independentPairHybridBoundaryResamplingSecondResidualBCF_sq_integrable
        C target O
  have hRight : Integrable
      (fun z => 3 *
        ((C.independentPairHybridBoundaryResamplingFirstResidualBCF target O z) ^ 2 +
         (C.independentPairHybridBoundaryResamplingResampledDifferenceBCF target O z) ^ 2 +
         (C.independentPairHybridBoundaryResamplingSecondResidualBCF target O z) ^ 2)) μ :=
    ((hFirst.add hResampled).add hSecond).const_mul 3
  have hIntegrated := integral_mono hActual hRight fun z =>
    continuous_compact_oriented_independentPairHybridBoundaryResampling_actualDifference_sq_le_three
      C target O z
  calc
    C.independentPairHybridIncrementEnergyBCF target O =
        ∫ z,
          (C.independentPairHybridBoundaryResamplingActualDifferenceBCF target O z) ^ 2
          ∂μ := by
      symm
      simpa [μ] using
        continuous_compact_oriented_integral_independentPairHybridBoundaryResamplingActualDifferenceBCF_sq_eq_incrementEnergy
          C target O
    _ ≤ ∫ z, 3 *
        ((C.independentPairHybridBoundaryResamplingFirstResidualBCF target O z) ^ 2 +
         (C.independentPairHybridBoundaryResamplingResampledDifferenceBCF target O z) ^ 2 +
         (C.independentPairHybridBoundaryResamplingSecondResidualBCF target O z) ^ 2) ∂μ :=
      hIntegrated
    _ = 3 *
        (C.independentPairHybridBoundaryResamplingFirstResidualEnergyBCF target O +
         C.independentPairHybridBoundaryResampledConditionalPairEnergyBCF target O +
         C.independentPairHybridBoundaryResamplingSecondResidualEnergyBCF target O) := by
      rw [integral_const_mul]
      rw [integral_add (hFirst.add hResampled) hSecond,
        integral_add hFirst hResampled]
      rw [continuous_compact_oriented_integral_independentPairHybridBoundaryResamplingResampledDifferenceBCF_sq_eq_conditionalPairEnergy]
      rfl

end

end MathlibAnalytic
end MGAP4D