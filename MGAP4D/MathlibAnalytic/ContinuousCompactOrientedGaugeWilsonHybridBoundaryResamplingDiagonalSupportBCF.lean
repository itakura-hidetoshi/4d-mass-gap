import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridBoundaryConditionalPairEnergyBCF
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

noncomputable section

/-- Extract the two off-target boundaries from an actual/resampled
boundary-target-pair coupling point. -/
def ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridBoundaryResamplingBoundaryPairMap
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    (C.OffTargetBoundaryTargetPair target ×
      C.OffTargetBoundaryTargetPair target) →
      (C.OffTargetBoundary target × C.OffTargetBoundary target) :=
  fun z => (z.1.1, z.2.1)

/-- Boundary-pair extraction from the actual/resampled coupling carrier is
continuous. -/
theorem continuous_compact_oriented_independentPairHybridBoundaryResamplingBoundaryPairMap_continuous
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    Continuous
      (C.independentPairHybridBoundaryResamplingBoundaryPairMap target) := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridBoundaryResamplingBoundaryPairMap
  exact
    ((continuous_fst : Continuous
      (fun z : C.OffTargetBoundaryTargetPair target => z.1)).comp
      continuous_fst).prodMk
      ((continuous_fst : Continuous
        (fun z : C.OffTargetBoundaryTargetPair target => z.1)).comp
        continuous_snd)

/-- Boundary-pair extraction from the actual/resampled coupling carrier is
measurable. -/
theorem continuous_compact_oriented_independentPairHybridBoundaryResamplingBoundaryPairMap_measurable
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    Measurable
      (C.independentPairHybridBoundaryResamplingBoundaryPairMap target) :=
  (continuous_compact_oriented_independentPairHybridBoundaryResamplingBoundaryPairMap_continuous
    C target).measurable

/-- Pointwise in the independent Gibbs source pair, the actual output boundary
and the boundary used by the exact conditional resampling kernel form the
same deterministic diagonal pair. -/
theorem continuous_compact_oriented_map_boundaryPair_independentPairHybridBoundaryResamplingCouplingKernel
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    (C.independentPairHybridBoundaryResamplingCouplingKernel target).map
        (C.independentPairHybridBoundaryResamplingBoundaryPairMap target) =
      Kernel.deterministic
        (fun z : C.base.Configuration × C.base.Configuration =>
          C.offTargetBoundaryDiagonalMap target
            (C.independentPairHybridPreBoundaryMap target z))
        ((continuous_compact_oriented_offTargetBoundaryDiagonalMap_continuous
          C target).measurable.comp
          (continuous_compact_oriented_independentPairHybridPreBoundaryMap_measurable
            C target)) := by
  let hActual :=
    continuous_compact_oriented_independentPairHybridActualBoundaryTargetPairMap_measurable
      C target
  let hPre :=
    continuous_compact_oriented_independentPairHybridPreBoundaryMap_measurable
      C target
  have hActualBoundary :
      (Kernel.deterministic
          (C.independentPairHybridActualBoundaryTargetPairMap target)
          hActual).map Prod.fst =
        Kernel.deterministic
          (C.independentPairHybridPreBoundaryMap target) hPre := by
    ext z
    rw [Kernel.map_apply _ measurable_fst z,
      Kernel.deterministic_apply,
      Measure.map_dirac' measurable_fst,
      Kernel.deterministic_apply]
    rw [continuous_compact_oriented_fst_independentPairHybridActualBoundaryTargetPairMap]
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridBoundaryResamplingCouplingKernel
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridBoundaryResamplingBoundaryPairMap
  change
    ((Kernel.deterministic
        (C.independentPairHybridActualBoundaryTargetPairMap target) hActual ×ₖ
      C.independentPairHybridBoundaryResamplingKernel target).map
        (Prod.map Prod.fst Prod.fst)) = _
  rw [← Kernel.map_prod_map _ _ measurable_fst measurable_fst,
    hActualBoundary,
    continuous_compact_oriented_fst_independentPairHybridBoundaryResamplingKernel,
    Kernel.deterministic_prod_deterministic]
  rfl

/-- Averaging the common-boundary coupling kernel preserves the exact diagonal
boundary support.  The diagonal variable has precisely the actual hybrid
pre-boundary law. -/
theorem continuous_compact_oriented_map_boundaryPair_independentPairHybridBoundaryResamplingCouplingMeasure
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    Measure.map
        (C.independentPairHybridBoundaryResamplingBoundaryPairMap target)
        (C.independentPairHybridBoundaryResamplingCouplingMeasure target) =
      Measure.map (C.offTargetBoundaryDiagonalMap target)
        (C.independentPairHybridOffTargetBoundaryMeasure target) := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridBoundaryResamplingCouplingMeasure
  change
    (C.independentPairHybridBoundaryResamplingCouplingKernel target ∘ₘ
      (C.gibbsMeasure.prod C.gibbsMeasure)).map
        (C.independentPairHybridBoundaryResamplingBoundaryPairMap target) = _
  rw [Measure.map_comp
      (C.gibbsMeasure.prod C.gibbsMeasure)
      (C.independentPairHybridBoundaryResamplingCouplingKernel target)
      (continuous_compact_oriented_independentPairHybridBoundaryResamplingBoundaryPairMap_measurable
        C target),
    continuous_compact_oriented_map_boundaryPair_independentPairHybridBoundaryResamplingCouplingKernel,
    Measure.deterministic_comp_eq_map,
    continuous_compact_oriented_independentPairHybridOffTargetBoundaryMeasure_eq_map_preBoundary,
    Measure.map_map
      (continuous_compact_oriented_offTargetBoundaryDiagonalMap_continuous
        C target).measurable
      (continuous_compact_oriented_independentPairHybridPreBoundaryMap_measurable
        C target)]
  rfl

/-- Under the actual/resampled boundary-target coupling, the actual and
resampled off-target boundaries agree almost everywhere. -/
theorem continuous_compact_oriented_independentPairHybridBoundaryResamplingCoupling_boundary_eq_ae
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    ∀ᵐ z ∂C.independentPairHybridBoundaryResamplingCouplingMeasure target,
      z.1.1 = z.2.1 := by
  let boundaryPairMap :=
    C.independentPairHybridBoundaryResamplingBoundaryPairMap target
  let diagonalMap := C.offTargetBoundaryDiagonalMap target
  have hEqSet : MeasurableSet
      {z : C.OffTargetBoundary target × C.OffTargetBoundary target |
        z.1 = z.2} :=
    (isClosed_eq continuous_fst continuous_snd).measurableSet
  have hDiagonal :
      ∀ᵐ z ∂Measure.map diagonalMap
          (C.independentPairHybridOffTargetBoundaryMeasure target),
        z.1 = z.2 := by
    rw [MeasureTheory.ae_map_iff
      (continuous_compact_oriented_offTargetBoundaryDiagonalMap_continuous
        C target).measurable.aemeasurable hEqSet]
    exact Filter.Eventually.of_forall fun boundary => rfl
  have hMapped :
      ∀ᵐ z ∂Measure.map boundaryPairMap
          (C.independentPairHybridBoundaryResamplingCouplingMeasure target),
        z.1 = z.2 := by
    rw [continuous_compact_oriented_map_boundaryPair_independentPairHybridBoundaryResamplingCouplingMeasure]
    exact hDiagonal
  have hPulled := MeasureTheory.ae_of_ae_map
    (continuous_compact_oriented_independentPairHybridBoundaryResamplingBoundaryPairMap_measurable
      C target).aemeasurable hMapped
  simpa [boundaryPairMap,
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridBoundaryResamplingBoundaryPairMap]
    using hPulled

/-- Replacing one fixed target link twice leaves the conditional projection
unchanged, so the difference of the two heat-bath fluctuations is exactly the
observable difference. -/
theorem continuous_compact_oriented_singleLinkHeatBathFluctuation_replaceLink_sub_replaceLink
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (g h : C.base.Gauge) :
    C.singleLinkHeatBathFluctuation target O
        (C.base.replaceLink A target g) -
      C.singleLinkHeatBathFluctuation target O
        (C.base.replaceLink A target h) =
      O (C.base.replaceLink A target g) -
        O (C.base.replaceLink A target h) := by
  have hProjectionG :
      C.singleLinkHeatBathProjection target O
          (C.base.replaceLink A target g) =
        C.singleLinkHeatBathProjection target O A := by
    change C.singleLinkConditionalExpectation O
        (C.base.replaceLink A target g) target =
      C.singleLinkConditionalExpectation O A target
    exact continuous_compact_oriented_singleLinkConditionalExpectation_replaceLink
      C O A target g
  have hProjectionH :
      C.singleLinkHeatBathProjection target O
          (C.base.replaceLink A target h) =
        C.singleLinkHeatBathProjection target O A := by
    change C.singleLinkConditionalExpectation O
        (C.base.replaceLink A target h) target =
      C.singleLinkConditionalExpectation O A target
    exact continuous_compact_oriented_singleLinkConditionalExpectation_replaceLink
      C O A target h
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkHeatBathFluctuation
  simp only [Pi.sub_apply]
  rw [hProjectionG, hProjectionH]
  ring

/-- Observable transport difference corresponding to the first endpoint of the
actual/resampled common-boundary coupling. -/
def ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridBoundaryResamplingFirstObservableTransportBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.OffTargetBoundaryTargetPair target ×
      C.OffTargetBoundaryTargetPair target) : ℝ :=
  O (C.offTargetBoundaryTargetPairConfigurationPairMap target z.2).1 -
    O (C.offTargetBoundaryTargetPairConfigurationPairMap target z.1).1

/-- Observable transport difference corresponding to the second endpoint of the
actual/resampled common-boundary coupling. -/
def ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridBoundaryResamplingSecondObservableTransportBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.OffTargetBoundaryTargetPair target ×
      C.OffTargetBoundaryTargetPair target) : ℝ :=
  O (C.offTargetBoundaryTargetPairConfigurationPairMap target z.1).2 -
    O (C.offTargetBoundaryTargetPairConfigurationPairMap target z.2).2

/-- On diagonal boundary support, the first fluctuation residual is exactly the
first observable transport difference. -/
theorem continuous_compact_oriented_independentPairHybridBoundaryResamplingFirstResidualBCF_configurationCouplingMap_of_boundary_eq
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.OffTargetBoundaryTargetPair target ×
      C.OffTargetBoundaryTargetPair target)
    (hz : z.1.1 = z.2.1) :
    C.independentPairHybridBoundaryResamplingFirstResidualBCF target O
        (C.independentPairHybridBoundaryResamplingConfigurationCouplingMap
          target z) =
      C.independentPairHybridBoundaryResamplingFirstObservableTransportBCF
        target O z := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridBoundaryResamplingFirstResidualBCF
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridBoundaryResamplingFirstObservableTransportBCF
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridBoundaryResamplingConfigurationCouplingMap
    ContinuousCompactOrientedGaugeWilsonSystem.offTargetBoundaryTargetPairConfigurationPairMap
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalPairConfigurationMap
  rw [← hz]
  exact
    continuous_compact_oriented_singleLinkHeatBathFluctuation_replaceLink_sub_replaceLink
      C (C.offTargetBoundarySection target z.1.1) target O
        z.2.2.1 z.1.2.1

/-- On diagonal boundary support, the second fluctuation residual is exactly the
second observable transport difference. -/
theorem continuous_compact_oriented_independentPairHybridBoundaryResamplingSecondResidualBCF_configurationCouplingMap_of_boundary_eq
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.OffTargetBoundaryTargetPair target ×
      C.OffTargetBoundaryTargetPair target)
    (hz : z.1.1 = z.2.1) :
    C.independentPairHybridBoundaryResamplingSecondResidualBCF target O
        (C.independentPairHybridBoundaryResamplingConfigurationCouplingMap
          target z) =
      C.independentPairHybridBoundaryResamplingSecondObservableTransportBCF
        target O z := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridBoundaryResamplingSecondResidualBCF
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridBoundaryResamplingSecondObservableTransportBCF
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridBoundaryResamplingConfigurationCouplingMap
    ContinuousCompactOrientedGaugeWilsonSystem.offTargetBoundaryTargetPairConfigurationPairMap
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalPairConfigurationMap
  rw [← hz]
  exact
    continuous_compact_oriented_singleLinkHeatBathFluctuation_replaceLink_sub_replaceLink
      C (C.offTargetBoundarySection target z.1.1) target O
        z.1.2.2 z.2.2.2

/-- The first observable transport difference is continuous on the
boundary-target coupling carrier. -/
theorem continuous_compact_oriented_independentPairHybridBoundaryResamplingFirstObservableTransportBCF_continuous
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    Continuous
      (C.independentPairHybridBoundaryResamplingFirstObservableTransportBCF
        target O) := by
  have hResampledFirst : Continuous
      (fun z : C.OffTargetBoundaryTargetPair target ×
        C.OffTargetBoundaryTargetPair target =>
        (C.offTargetBoundaryTargetPairConfigurationPairMap target z.2).1) :=
    (continuous_fst : Continuous
      (fun y : C.base.Configuration × C.base.Configuration => y.1)).comp
      ((continuous_compact_oriented_offTargetBoundaryTargetPairConfigurationPairMap_continuous
        C target).comp continuous_snd)
  have hActualFirst : Continuous
      (fun z : C.OffTargetBoundaryTargetPair target ×
        C.OffTargetBoundaryTargetPair target =>
        (C.offTargetBoundaryTargetPairConfigurationPairMap target z.1).1) :=
    (continuous_fst : Continuous
      (fun y : C.base.Configuration × C.base.Configuration => y.1)).comp
      ((continuous_compact_oriented_offTargetBoundaryTargetPairConfigurationPairMap_continuous
        C target).comp continuous_fst)
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridBoundaryResamplingFirstObservableTransportBCF
  exact (O.continuous.comp hResampledFirst).sub
    (O.continuous.comp hActualFirst)

/-- The second observable transport difference is continuous on the
boundary-target coupling carrier. -/
theorem continuous_compact_oriented_independentPairHybridBoundaryResamplingSecondObservableTransportBCF_continuous
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    Continuous
      (C.independentPairHybridBoundaryResamplingSecondObservableTransportBCF
        target O) := by
  have hActualSecond : Continuous
      (fun z : C.OffTargetBoundaryTargetPair target ×
        C.OffTargetBoundaryTargetPair target =>
        (C.offTargetBoundaryTargetPairConfigurationPairMap target z.1).2) :=
    (continuous_snd : Continuous
      (fun y : C.base.Configuration × C.base.Configuration => y.2)).comp
      ((continuous_compact_oriented_offTargetBoundaryTargetPairConfigurationPairMap_continuous
        C target).comp continuous_fst)
  have hResampledSecond : Continuous
      (fun z : C.OffTargetBoundaryTargetPair target ×
        C.OffTargetBoundaryTargetPair target =>
        (C.offTargetBoundaryTargetPairConfigurationPairMap target z.2).2) :=
    (continuous_snd : Continuous
      (fun y : C.base.Configuration × C.base.Configuration => y.2)).comp
      ((continuous_compact_oriented_offTargetBoundaryTargetPairConfigurationPairMap_continuous
        C target).comp continuous_snd)
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridBoundaryResamplingSecondObservableTransportBCF
  exact (O.continuous.comp hActualSecond).sub
    (O.continuous.comp hResampledSecond)

/-- The first observable transport difference is bounded by twice the
bounded-continuous norm. -/
theorem continuous_compact_oriented_independentPairHybridBoundaryResamplingFirstObservableTransportBCF_abs_le
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.OffTargetBoundaryTargetPair target ×
      C.OffTargetBoundaryTargetPair target) :
    |C.independentPairHybridBoundaryResamplingFirstObservableTransportBCF
        target O z| ≤ 2 * ‖O‖ := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridBoundaryResamplingFirstObservableTransportBCF
  calc
    |O (C.offTargetBoundaryTargetPairConfigurationPairMap target z.2).1 -
        O (C.offTargetBoundaryTargetPairConfigurationPairMap target z.1).1| ≤
      |O (C.offTargetBoundaryTargetPairConfigurationPairMap target z.2).1| +
        |O (C.offTargetBoundaryTargetPairConfigurationPairMap target z.1).1| :=
      abs_sub _ _
    _ ≤ ‖O‖ + ‖O‖ := by
      exact add_le_add
        (by simpa [Real.norm_eq_abs] using
          O.norm_coe_le_norm
            (C.offTargetBoundaryTargetPairConfigurationPairMap target z.2).1)
        (by simpa [Real.norm_eq_abs] using
          O.norm_coe_le_norm
            (C.offTargetBoundaryTargetPairConfigurationPairMap target z.1).1)
    _ = 2 * ‖O‖ := (two_mul ‖O‖).symm

/-- The second observable transport difference is bounded by twice the
bounded-continuous norm. -/
theorem continuous_compact_oriented_independentPairHybridBoundaryResamplingSecondObservableTransportBCF_abs_le
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.OffTargetBoundaryTargetPair target ×
      C.OffTargetBoundaryTargetPair target) :
    |C.independentPairHybridBoundaryResamplingSecondObservableTransportBCF
        target O z| ≤ 2 * ‖O‖ := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridBoundaryResamplingSecondObservableTransportBCF
  calc
    |O (C.offTargetBoundaryTargetPairConfigurationPairMap target z.1).2 -
        O (C.offTargetBoundaryTargetPairConfigurationPairMap target z.2).2| ≤
      |O (C.offTargetBoundaryTargetPairConfigurationPairMap target z.1).2| +
        |O (C.offTargetBoundaryTargetPairConfigurationPairMap target z.2).2| :=
      abs_sub _ _
    _ ≤ ‖O‖ + ‖O‖ := by
      exact add_le_add
        (by simpa [Real.norm_eq_abs] using
          O.norm_coe_le_norm
            (C.offTargetBoundaryTargetPairConfigurationPairMap target z.1).2)
        (by simpa [Real.norm_eq_abs] using
          O.norm_coe_le_norm
            (C.offTargetBoundaryTargetPairConfigurationPairMap target z.2).2)
    _ = 2 * ‖O‖ := (two_mul ‖O‖).symm

/-- Squared first observable transport differences are integrable under the
actual/resampled boundary-target coupling. -/
theorem continuous_compact_oriented_independentPairHybridBoundaryResamplingFirstObservableTransportBCF_sq_integrable
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    Integrable
      (fun z =>
        (C.independentPairHybridBoundaryResamplingFirstObservableTransportBCF
          target O z) ^ 2)
      (C.independentPairHybridBoundaryResamplingCouplingMeasure target) := by
  letI : IsProbabilityMeasure
      (C.independentPairHybridBoundaryResamplingCouplingMeasure target) :=
    continuousCompactOriented_independentPairHybridBoundaryResamplingCouplingMeasure_isProbability
      C target
  apply continuous_compact_oriented_integrable_of_uniform_bound
    (C.independentPairHybridBoundaryResamplingCouplingMeasure target)
    (fun z =>
      (C.independentPairHybridBoundaryResamplingFirstObservableTransportBCF
        target O z) ^ 2)
    ((continuous_compact_oriented_independentPairHybridBoundaryResamplingFirstObservableTransportBCF_continuous
      C target O).pow 2).stronglyMeasurable
    ((2 * ‖O‖) ^ 2)
  intro z
  have hAbs :=
    continuous_compact_oriented_independentPairHybridBoundaryResamplingFirstObservableTransportBCF_abs_le
      C target O z
  have hBounds := abs_le.mp hAbs
  rw [abs_of_nonneg (sq_nonneg _)]
  nlinarith [norm_nonneg O]

/-- Squared second observable transport differences are integrable under the
actual/resampled boundary-target coupling. -/
theorem continuous_compact_oriented_independentPairHybridBoundaryResamplingSecondObservableTransportBCF_sq_integrable
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    Integrable
      (fun z =>
        (C.independentPairHybridBoundaryResamplingSecondObservableTransportBCF
          target O z) ^ 2)
      (C.independentPairHybridBoundaryResamplingCouplingMeasure target) := by
  letI : IsProbabilityMeasure
      (C.independentPairHybridBoundaryResamplingCouplingMeasure target) :=
    continuousCompactOriented_independentPairHybridBoundaryResamplingCouplingMeasure_isProbability
      C target
  apply continuous_compact_oriented_integrable_of_uniform_bound
    (C.independentPairHybridBoundaryResamplingCouplingMeasure target)
    (fun z =>
      (C.independentPairHybridBoundaryResamplingSecondObservableTransportBCF
        target O z) ^ 2)
    ((continuous_compact_oriented_independentPairHybridBoundaryResamplingSecondObservableTransportBCF_continuous
      C target O).pow 2).stronglyMeasurable
    ((2 * ‖O‖) ^ 2)
  intro z
  have hAbs :=
    continuous_compact_oriented_independentPairHybridBoundaryResamplingSecondObservableTransportBCF_abs_le
      C target O z
  have hBounds := abs_le.mp hAbs
  rw [abs_of_nonneg (sq_nonneg _)]
  nlinarith [norm_nonneg O]

/-- The first endpoint residual energy is exactly an observable transport energy
on the original boundary-target coupling carrier. -/
theorem continuous_compact_oriented_independentPairHybridBoundaryResamplingFirstResidualEnergyBCF_eq_observableTransport
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    C.independentPairHybridBoundaryResamplingFirstResidualEnergyBCF target O =
      ∫ z,
        (C.independentPairHybridBoundaryResamplingFirstObservableTransportBCF
          target O z) ^ 2
        ∂C.independentPairHybridBoundaryResamplingCouplingMeasure target := by
  have hResidualSq : StronglyMeasurable
      (fun z =>
        (C.independentPairHybridBoundaryResamplingFirstResidualBCF
          target O z) ^ 2) :=
    (continuous_compact_oriented_independentPairHybridBoundaryResamplingFirstResidualBCF_stronglyMeasurable
      C target O).pow 2
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridBoundaryResamplingFirstResidualEnergyBCF
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridBoundaryResamplingConfigurationCouplingMeasure
  rw [MeasureTheory.integral_map
    (continuous_compact_oriented_independentPairHybridBoundaryResamplingConfigurationCouplingMap_continuous
      C target).measurable.aemeasurable
    hResidualSq.aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards
    [continuous_compact_oriented_independentPairHybridBoundaryResamplingCoupling_boundary_eq_ae
      C target] with z hz
  rw [continuous_compact_oriented_independentPairHybridBoundaryResamplingFirstResidualBCF_configurationCouplingMap_of_boundary_eq
    C target O z hz]

/-- The second endpoint residual energy is exactly an observable transport energy
on the original boundary-target coupling carrier. -/
theorem continuous_compact_oriented_independentPairHybridBoundaryResamplingSecondResidualEnergyBCF_eq_observableTransport
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    C.independentPairHybridBoundaryResamplingSecondResidualEnergyBCF target O =
      ∫ z,
        (C.independentPairHybridBoundaryResamplingSecondObservableTransportBCF
          target O z) ^ 2
        ∂C.independentPairHybridBoundaryResamplingCouplingMeasure target := by
  have hResidualSq : StronglyMeasurable
      (fun z =>
        (C.independentPairHybridBoundaryResamplingSecondResidualBCF
          target O z) ^ 2) :=
    (continuous_compact_oriented_independentPairHybridBoundaryResamplingSecondResidualBCF_stronglyMeasurable
      C target O).pow 2
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridBoundaryResamplingSecondResidualEnergyBCF
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridBoundaryResamplingConfigurationCouplingMeasure
  rw [MeasureTheory.integral_map
    (continuous_compact_oriented_independentPairHybridBoundaryResamplingConfigurationCouplingMap_continuous
      C target).measurable.aemeasurable
    hResidualSq.aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards
    [continuous_compact_oriented_independentPairHybridBoundaryResamplingCoupling_boundary_eq_ae
      C target] with z hz
  rw [continuous_compact_oriented_independentPairHybridBoundaryResamplingSecondResidualBCF_configurationCouplingMap_of_boundary_eq
    C target O z hz]

/-- The first endpoint residual energy obeys the sharp universal
bounded-observable estimate inherited from its exact transport representation. -/
theorem continuous_compact_oriented_independentPairHybridBoundaryResamplingFirstResidualEnergyBCF_le_two_mul_norm_sq
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    C.independentPairHybridBoundaryResamplingFirstResidualEnergyBCF target O ≤
      (2 * ‖O‖) ^ 2 := by
  rw [continuous_compact_oriented_independentPairHybridBoundaryResamplingFirstResidualEnergyBCF_eq_observableTransport]
  let μ := C.independentPairHybridBoundaryResamplingCouplingMeasure target
  letI : IsProbabilityMeasure μ :=
    continuousCompactOriented_independentPairHybridBoundaryResamplingCouplingMeasure_isProbability
      C target
  have hTransport : Integrable
      (fun z =>
        (C.independentPairHybridBoundaryResamplingFirstObservableTransportBCF
          target O z) ^ 2) μ := by
    simpa [μ] using
      continuous_compact_oriented_independentPairHybridBoundaryResamplingFirstObservableTransportBCF_sq_integrable
        C target O
  have hConst : Integrable
      (fun _ : C.OffTargetBoundaryTargetPair target ×
        C.OffTargetBoundaryTargetPair target => (2 * ‖O‖) ^ 2) μ :=
    integrable_const _
  calc
    (∫ z,
        (C.independentPairHybridBoundaryResamplingFirstObservableTransportBCF
          target O z) ^ 2 ∂μ) ≤
      ∫ _z : C.OffTargetBoundaryTargetPair target ×
        C.OffTargetBoundaryTargetPair target,
        (2 * ‖O‖) ^ 2 ∂μ := by
      apply integral_mono hTransport hConst
      intro z
      have hAbs :=
        continuous_compact_oriented_independentPairHybridBoundaryResamplingFirstObservableTransportBCF_abs_le
          C target O z
      have hBounds := abs_le.mp hAbs
      nlinarith [norm_nonneg O]
    _ = (2 * ‖O‖) ^ 2 := by simp

/-- The second endpoint residual energy obeys the sharp universal
bounded-observable estimate inherited from its exact transport representation. -/
theorem continuous_compact_oriented_independentPairHybridBoundaryResamplingSecondResidualEnergyBCF_le_two_mul_norm_sq
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    C.independentPairHybridBoundaryResamplingSecondResidualEnergyBCF target O ≤
      (2 * ‖O‖) ^ 2 := by
  rw [continuous_compact_oriented_independentPairHybridBoundaryResamplingSecondResidualEnergyBCF_eq_observableTransport]
  let μ := C.independentPairHybridBoundaryResamplingCouplingMeasure target
  letI : IsProbabilityMeasure μ :=
    continuousCompactOriented_independentPairHybridBoundaryResamplingCouplingMeasure_isProbability
      C target
  have hTransport : Integrable
      (fun z =>
        (C.independentPairHybridBoundaryResamplingSecondObservableTransportBCF
          target O z) ^ 2) μ := by
    simpa [μ] using
      continuous_compact_oriented_independentPairHybridBoundaryResamplingSecondObservableTransportBCF_sq_integrable
        C target O
  have hConst : Integrable
      (fun _ : C.OffTargetBoundaryTargetPair target ×
        C.OffTargetBoundaryTargetPair target => (2 * ‖O‖) ^ 2) μ :=
    integrable_const _
  calc
    (∫ z,
        (C.independentPairHybridBoundaryResamplingSecondObservableTransportBCF
          target O z) ^ 2 ∂μ) ≤
      ∫ _z : C.OffTargetBoundaryTargetPair target ×
        C.OffTargetBoundaryTargetPair target,
        (2 * ‖O‖) ^ 2 ∂μ := by
      apply integral_mono hTransport hConst
      intro z
      have hAbs :=
        continuous_compact_oriented_independentPairHybridBoundaryResamplingSecondObservableTransportBCF_abs_le
          C target O z
      have hBounds := abs_le.mp hAbs
      nlinarith [norm_nonneg O]
    _ = (2 * ‖O‖) ^ 2 := by simp

end

end MathlibAnalytic
end MGAP4D
