import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridBoundaryConditionalPairEnergyBCF
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

noncomputable section

/-- Extract the actual and resampled off-target boundaries from one coupling
point. -/
def ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridBoundaryResamplingBoundaryPairMap
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    (C.OffTargetBoundaryTargetPair target ×
      C.OffTargetBoundaryTargetPair target) →
      C.OffTargetBoundary target × C.OffTargetBoundary target :=
  fun z => (z.1.1, z.2.1)

/-- Boundary-pair extraction is continuous. -/
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

/-- Boundary-pair extraction is measurable. -/
theorem continuous_compact_oriented_independentPairHybridBoundaryResamplingBoundaryPairMap_measurable
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    Measurable
      (C.independentPairHybridBoundaryResamplingBoundaryPairMap target) :=
  (continuous_compact_oriented_independentPairHybridBoundaryResamplingBoundaryPairMap_continuous
    C target).measurable

/-- Pointwise in the independent Gibbs source pair, the actual output boundary
and the boundary retained by exact conditional resampling form the deterministic
diagonal of the actual hybrid pre-boundary. -/
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
boundary support.  The diagonal variable has the actual hybrid pre-boundary
law. -/
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

/-- Under the actual/resampled boundary-target coupling, the two off-target
boundaries agree almost everywhere.  The explicit Hausdorff assumption is used
only to make the diagonal measurable; it is available for the actual compact
`SU(N)` gauge group. -/
theorem continuous_compact_oriented_independentPairHybridBoundaryResamplingCoupling_boundary_eq_ae
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    [T2Space C.base.Gauge]
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

/-- Observable transport difference for the first endpoint. -/
def ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridBoundaryResamplingFirstObservableTransportBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.OffTargetBoundaryTargetPair target ×
      C.OffTargetBoundaryTargetPair target) : ℝ :=
  O (C.offTargetBoundaryTargetPairConfigurationPairMap target z.2).1 -
    O (C.offTargetBoundaryTargetPairConfigurationPairMap target z.1).1

/-- Observable transport difference for the second endpoint. -/
def ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridBoundaryResamplingSecondObservableTransportBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.OffTargetBoundaryTargetPair target ×
      C.OffTargetBoundaryTargetPair target) : ℝ :=
  O (C.offTargetBoundaryTargetPairConfigurationPairMap target z.1).2 -
    O (C.offTargetBoundaryTargetPairConfigurationPairMap target z.2).2

/-- On diagonal boundary support, the first fluctuation residual is the first
observable transport difference. -/
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

/-- On diagonal boundary support, the second fluctuation residual is the second
observable transport difference. -/
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

/-- The first observable transport difference is continuous. -/
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

/-- The second observable transport difference is continuous. -/
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

private theorem continuous_compact_oriented_observable_sub_abs_le_two_norm
    {C : ContinuousCompactOrientedGaugeWilsonSystem}
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (A B : C.base.Configuration) :
    |O A - O B| ≤ 2 * ‖O‖ := by
  calc
    |O A - O B| ≤ |O A| + |O B| := abs_sub _ _
    _ ≤ ‖O‖ + ‖O‖ := by
      exact add_le_add
        (by simpa [Real.norm_eq_abs] using O.norm_coe_le_norm A)
        (by simpa [Real.norm_eq_abs] using O.norm_coe_le_norm B)
    _ = 2 * ‖O‖ := (two_mul ‖O‖).symm

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
  exact continuous_compact_oriented_observable_sub_abs_le_two_norm O
    ((C.offTargetBoundaryTargetPairConfigurationPairMap target z.2).1)
    ((C.offTargetBoundaryTargetPairConfigurationPairMap target z.1).1)

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
  exact continuous_compact_oriented_observable_sub_abs_le_two_norm O
    ((C.offTargetBoundaryTargetPairConfigurationPairMap target z.1).2)
    ((C.offTargetBoundaryTargetPairConfigurationPairMap target z.2).2)

private theorem continuous_compact_oriented_sq_integrable_of_abs_le_two_norm
    {X : Type*}
    [MeasurableSpace X]
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (μ : Measure X)
    [IsProbabilityMeasure μ]
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (f : X → ℝ)
    (hf : StronglyMeasurable f)
    (hBound : ∀ x, |f x| ≤ 2 * ‖O‖) :
    Integrable (fun x => (f x) ^ 2) μ := by
  apply continuous_compact_oriented_integrable_of_uniform_bound
    μ (fun x => (f x) ^ 2) (hf.pow 2) ((2 * ‖O‖) ^ 2)
  intro x
  have hAbs := hBound x
  have hBounds := abs_le.mp hAbs
  rw [abs_of_nonneg (sq_nonneg _)]
  nlinarith [norm_nonneg O]

/-- Squared first observable transport differences are integrable. -/
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
  exact continuous_compact_oriented_sq_integrable_of_abs_le_two_norm
    C (C.independentPairHybridBoundaryResamplingCouplingMeasure target) O
    (C.independentPairHybridBoundaryResamplingFirstObservableTransportBCF target O)
    (continuous_compact_oriented_independentPairHybridBoundaryResamplingFirstObservableTransportBCF_continuous
      C target O).stronglyMeasurable
    (continuous_compact_oriented_independentPairHybridBoundaryResamplingFirstObservableTransportBCF_abs_le
      C target O)

/-- Squared second observable transport differences are integrable. -/
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
  exact continuous_compact_oriented_sq_integrable_of_abs_le_two_norm
    C (C.independentPairHybridBoundaryResamplingCouplingMeasure target) O
    (C.independentPairHybridBoundaryResamplingSecondObservableTransportBCF target O)
    (continuous_compact_oriented_independentPairHybridBoundaryResamplingSecondObservableTransportBCF_continuous
      C target O).stronglyMeasurable
    (continuous_compact_oriented_independentPairHybridBoundaryResamplingSecondObservableTransportBCF_abs_le
      C target O)

/-- The first endpoint residual energy is exactly the first observable transport
energy on the original boundary-target coupling carrier. -/
theorem continuous_compact_oriented_independentPairHybridBoundaryResamplingFirstResidualEnergyBCF_eq_observableTransport
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    [T2Space C.base.Gauge]
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

/-- The second endpoint residual energy is exactly the second observable
transport energy on the original boundary-target coupling carrier. -/
theorem continuous_compact_oriented_independentPairHybridBoundaryResamplingSecondResidualEnergyBCF_eq_observableTransport
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    [T2Space C.base.Gauge]
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

private theorem continuous_compact_oriented_integral_sq_le_two_norm_sq
    {X : Type*}
    [MeasurableSpace X]
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (μ : Measure X)
    [IsProbabilityMeasure μ]
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (f : X → ℝ)
    (hIntegrable : Integrable (fun x => (f x) ^ 2) μ)
    (hBound : ∀ x, |f x| ≤ 2 * ‖O‖) :
    (∫ x, (f x) ^ 2 ∂μ) ≤ (2 * ‖O‖) ^ 2 := by
  have hConst : Integrable (fun _ : X => (2 * ‖O‖) ^ 2) μ :=
    integrable_const _
  calc
    (∫ x, (f x) ^ 2 ∂μ) ≤
        ∫ _x : X, (2 * ‖O‖) ^ 2 ∂μ := by
      apply integral_mono hIntegrable hConst
      intro x
      have hAbs := hBound x
      have hBounds := abs_le.mp hAbs
      nlinarith [norm_nonneg O]
    _ = (2 * ‖O‖) ^ 2 := by simp

/-- The first endpoint residual energy obeys the universal sharp transport
bound `(2 * ‖O‖)^2`. -/
theorem continuous_compact_oriented_independentPairHybridBoundaryResamplingFirstResidualEnergyBCF_le_two_mul_norm_sq
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    [T2Space C.base.Gauge]
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    C.independentPairHybridBoundaryResamplingFirstResidualEnergyBCF target O ≤
      (2 * ‖O‖) ^ 2 := by
  rw [continuous_compact_oriented_independentPairHybridBoundaryResamplingFirstResidualEnergyBCF_eq_observableTransport]
  let μ := C.independentPairHybridBoundaryResamplingCouplingMeasure target
  letI : IsProbabilityMeasure μ :=
    continuousCompactOriented_independentPairHybridBoundaryResamplingCouplingMeasure_isProbability
      C target
  apply continuous_compact_oriented_integral_sq_le_two_norm_sq
    C μ O
    (C.independentPairHybridBoundaryResamplingFirstObservableTransportBCF target O)
  · simpa [μ] using
      continuous_compact_oriented_independentPairHybridBoundaryResamplingFirstObservableTransportBCF_sq_integrable
        C target O
  · exact
      continuous_compact_oriented_independentPairHybridBoundaryResamplingFirstObservableTransportBCF_abs_le
        C target O

/-- The second endpoint residual energy obeys the universal sharp transport
bound `(2 * ‖O‖)^2`. -/
theorem continuous_compact_oriented_independentPairHybridBoundaryResamplingSecondResidualEnergyBCF_le_two_mul_norm_sq
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    [T2Space C.base.Gauge]
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    C.independentPairHybridBoundaryResamplingSecondResidualEnergyBCF target O ≤
      (2 * ‖O‖) ^ 2 := by
  rw [continuous_compact_oriented_independentPairHybridBoundaryResamplingSecondResidualEnergyBCF_eq_observableTransport]
  let μ := C.independentPairHybridBoundaryResamplingCouplingMeasure target
  letI : IsProbabilityMeasure μ :=
    continuousCompactOriented_independentPairHybridBoundaryResamplingCouplingMeasure_isProbability
      C target
  apply continuous_compact_oriented_integral_sq_le_two_norm_sq
    C μ O
    (C.independentPairHybridBoundaryResamplingSecondObservableTransportBCF target O)
  · simpa [μ] using
      continuous_compact_oriented_independentPairHybridBoundaryResamplingSecondObservableTransportBCF_sq_integrable
        C target O
  · exact
      continuous_compact_oriented_independentPairHybridBoundaryResamplingSecondObservableTransportBCF_abs_le
        C target O

end

end MathlibAnalytic
end MGAP4D
