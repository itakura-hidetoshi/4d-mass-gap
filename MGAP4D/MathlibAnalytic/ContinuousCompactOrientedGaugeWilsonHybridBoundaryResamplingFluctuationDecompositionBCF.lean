import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonActualHybridBoundaryResamplingCouplingBCF
import MGAP4D.MathlibAnalytic.PeriodicHypercubicSpecialUnitaryHybridEndpointTransportCouplingBCF
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

noncomputable section

/-- Reconstruct two full configurations from one common off-target boundary and
its two target-link values. -/
def ContinuousCompactOrientedGaugeWilsonSystem.offTargetBoundaryTargetPairConfigurationPairMap
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    C.OffTargetBoundaryTargetPair target →
      C.base.Configuration × C.base.Configuration :=
  fun z =>
    C.singleLinkConditionalPairConfigurationMap
      (C.offTargetBoundarySection target z.1) target z.2

/-- Boundary-target-pair reconstruction is continuous. -/
theorem continuous_compact_oriented_offTargetBoundaryTargetPairConfigurationPairMap_continuous
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    Continuous (C.offTargetBoundaryTargetPairConfigurationPairMap target) := by
  have hBoundary : Continuous
      (fun z : C.OffTargetBoundaryTargetPair target =>
        C.offTargetBoundarySection target z.1) :=
    (continuous_compact_oriented_offTargetBoundarySection_continuous C target).comp
      continuous_fst
  have hFirstTarget : Continuous
      (fun z : C.OffTargetBoundaryTargetPair target => z.2.1) :=
    (continuous_fst : Continuous
      (fun z : C.base.Gauge × C.base.Gauge => z.1)).comp continuous_snd
  have hSecondTarget : Continuous
      (fun z : C.OffTargetBoundaryTargetPair target => z.2.2) :=
    (continuous_snd : Continuous
      (fun z : C.base.Gauge × C.base.Gauge => z.2)).comp continuous_snd
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.offTargetBoundaryTargetPairConfigurationPairMap
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalPairConfigurationMap
  exact
    ((continuous_compact_oriented_replaceLink_prod_hybridEndpoint C target).comp
      (hBoundary.prodMk hFirstTarget)).prodMk
      ((continuous_compact_oriented_replaceLink_prod_hybridEndpoint C target).comp
        (hBoundary.prodMk hSecondTarget))

/-- Boundary-target-pair reconstruction is measurable. -/
theorem continuous_compact_oriented_offTargetBoundaryTargetPairConfigurationPairMap_measurable
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    Measurable (C.offTargetBoundaryTargetPairConfigurationPairMap target) :=
  (continuous_compact_oriented_offTargetBoundaryTargetPairConfigurationPairMap_continuous
    C target).measurable

/-- Extracting and then reconstructing a configuration pair is exact whenever
its two configurations agree away from the target link. -/
theorem continuous_compact_oriented_offTargetBoundaryTargetPairConfigurationPairMap_extract_of_agreeOffLink
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (y : C.base.Configuration × C.base.Configuration)
    (hy : C.base.AgreeOffLink y.2 y.1 target) :
    C.offTargetBoundaryTargetPairConfigurationPairMap target
        (C.offTargetBoundaryTargetPairMap target y) = y := by
  apply Prod.ext
  · funext source
    by_cases hsource : source = target
    · subst source
      simp
        [ContinuousCompactOrientedGaugeWilsonSystem.offTargetBoundaryTargetPairConfigurationPairMap,
          ContinuousCompactOrientedGaugeWilsonSystem.offTargetBoundaryTargetPairMap,
          ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalPairConfigurationMap,
          CompactOrientedGaugeWilsonSystem.replaceLink]
    · simp
        [ContinuousCompactOrientedGaugeWilsonSystem.offTargetBoundaryTargetPairConfigurationPairMap,
          ContinuousCompactOrientedGaugeWilsonSystem.offTargetBoundaryTargetPairMap,
          ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalPairConfigurationMap,
          ContinuousCompactOrientedGaugeWilsonSystem.offTargetBoundaryMap,
          CompactOrientedGaugeWilsonSystem.replaceLink,
          hsource]
  · funext source
    by_cases hsource : source = target
    · subst source
      simp
        [ContinuousCompactOrientedGaugeWilsonSystem.offTargetBoundaryTargetPairConfigurationPairMap,
          ContinuousCompactOrientedGaugeWilsonSystem.offTargetBoundaryTargetPairMap,
          ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalPairConfigurationMap,
          CompactOrientedGaugeWilsonSystem.replaceLink]
    · have hoff := hy source hsource
      simp
        [ContinuousCompactOrientedGaugeWilsonSystem.offTargetBoundaryTargetPairConfigurationPairMap,
          ContinuousCompactOrientedGaugeWilsonSystem.offTargetBoundaryTargetPairMap,
          ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalPairConfigurationMap,
          ContinuousCompactOrientedGaugeWilsonSystem.offTargetBoundaryMap,
          CompactOrientedGaugeWilsonSystem.replaceLink,
          hsource, hoff]

/-- Reconstructing the actual hybrid boundary-target output recovers the actual
pre/post endpoint pair exactly. -/
theorem continuous_compact_oriented_offTargetBoundaryTargetPairConfigurationPairMap_actualHybrid
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (z : C.base.Configuration × C.base.Configuration) :
    C.offTargetBoundaryTargetPairConfigurationPairMap target
        (C.independentPairHybridActualBoundaryTargetPairMap target z) =
      C.independentPairHybridEndpointPairMap target z := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridActualBoundaryTargetPairMap
  exact
    continuous_compact_oriented_offTargetBoundaryTargetPairConfigurationPairMap_extract_of_agreeOffLink
      C target _
      (continuous_compact_oriented_independentPairHybridEndpointPairMap_agreeOffLink
        C target z)

/-- Mapping the actual hybrid boundary-target law through reconstruction recovers
the actual hybrid endpoint-pair transport law. -/
theorem continuous_compact_oriented_map_configurationPair_independentPairHybridBoundaryTargetPairMeasure
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    Measure.map (C.offTargetBoundaryTargetPairConfigurationPairMap target)
        (C.independentPairHybridBoundaryTargetPairMeasure target) =
      C.independentPairHybridEndpointPairMeasure target := by
  rw [continuous_compact_oriented_independentPairHybridBoundaryTargetPairMeasure_eq_map_actual]
  rw [Measure.map_map
    (continuous_compact_oriented_offTargetBoundaryTargetPairConfigurationPairMap_measurable
      C target)
    (continuous_compact_oriented_independentPairHybridActualBoundaryTargetPairMap_measurable
      C target)]
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridEndpointPairMeasure
  apply Measure.map_congr
  exact Filter.Eventually.of_forall fun z =>
    continuous_compact_oriented_offTargetBoundaryTargetPairConfigurationPairMap_actualHybrid
      C target z

/-- Configuration-pair law obtained by reconstructing the hybrid-boundary-driven
native conditional target pair. -/
def ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridBoundaryResampledConfigurationPairMeasure
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    Measure (C.base.Configuration × C.base.Configuration) :=
  Measure.map (C.offTargetBoundaryTargetPairConfigurationPairMap target)
    (C.independentPairHybridBoundaryDrivenTargetPairMeasure target)

/-- Map the common-boundary coupling to a coupling of actual and resampled full
configuration pairs. -/
def ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridBoundaryResamplingConfigurationCouplingMap
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    (C.OffTargetBoundaryTargetPair target ×
      C.OffTargetBoundaryTargetPair target) →
      ((C.base.Configuration × C.base.Configuration) ×
        (C.base.Configuration × C.base.Configuration)) :=
  fun z =>
    (C.offTargetBoundaryTargetPairConfigurationPairMap target z.1,
      C.offTargetBoundaryTargetPairConfigurationPairMap target z.2)

/-- The configuration-level coupling map is continuous. -/
theorem continuous_compact_oriented_independentPairHybridBoundaryResamplingConfigurationCouplingMap_continuous
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    Continuous
      (C.independentPairHybridBoundaryResamplingConfigurationCouplingMap target) := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridBoundaryResamplingConfigurationCouplingMap
  exact
    ((continuous_compact_oriented_offTargetBoundaryTargetPairConfigurationPairMap_continuous
      C target).comp continuous_fst).prodMk
      ((continuous_compact_oriented_offTargetBoundaryTargetPairConfigurationPairMap_continuous
        C target).comp continuous_snd)

/-- Configuration-level actual/resampled coupling measure. -/
def ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridBoundaryResamplingConfigurationCouplingMeasure
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    Measure
      ((C.base.Configuration × C.base.Configuration) ×
        (C.base.Configuration × C.base.Configuration)) :=
  Measure.map
    (C.independentPairHybridBoundaryResamplingConfigurationCouplingMap target)
    (C.independentPairHybridBoundaryResamplingCouplingMeasure target)

/-- The first marginal of the configuration-level coupling is the actual hybrid
endpoint-pair law. -/
theorem continuous_compact_oriented_map_actual_independentPairHybridBoundaryResamplingConfigurationCoupling
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    Measure.map Prod.fst
        (C.independentPairHybridBoundaryResamplingConfigurationCouplingMeasure target) =
      C.independentPairHybridEndpointPairMeasure target := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridBoundaryResamplingConfigurationCouplingMeasure
  rw [Measure.map_map measurable_fst
    (continuous_compact_oriented_independentPairHybridBoundaryResamplingConfigurationCouplingMap_continuous
      C target).measurable]
  change Measure.map
      (C.offTargetBoundaryTargetPairConfigurationPairMap target ∘ Prod.fst)
      (C.independentPairHybridBoundaryResamplingCouplingMeasure target) =
    C.independentPairHybridEndpointPairMeasure target
  rw [← Measure.map_map
    (continuous_compact_oriented_offTargetBoundaryTargetPairConfigurationPairMap_measurable
      C target) measurable_fst]
  rw [continuous_compact_oriented_map_actual_independentPairHybridBoundaryResamplingCoupling]
  exact
    continuous_compact_oriented_map_configurationPair_independentPairHybridBoundaryTargetPairMeasure
      C target

/-- The second marginal of the configuration-level coupling is the reconstructed
hybrid-boundary-driven native conditional-pair law. -/
theorem continuous_compact_oriented_map_resampled_independentPairHybridBoundaryResamplingConfigurationCoupling
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    Measure.map Prod.snd
        (C.independentPairHybridBoundaryResamplingConfigurationCouplingMeasure target) =
      C.independentPairHybridBoundaryResampledConfigurationPairMeasure target := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridBoundaryResamplingConfigurationCouplingMeasure
  rw [Measure.map_map measurable_snd
    (continuous_compact_oriented_independentPairHybridBoundaryResamplingConfigurationCouplingMap_continuous
      C target).measurable]
  change Measure.map
      (C.offTargetBoundaryTargetPairConfigurationPairMap target ∘ Prod.snd)
      (C.independentPairHybridBoundaryResamplingCouplingMeasure target) =
    C.independentPairHybridBoundaryResampledConfigurationPairMeasure target
  rw [← Measure.map_map
    (continuous_compact_oriented_offTargetBoundaryTargetPairConfigurationPairMap_measurable
      C target) measurable_snd]
  rw [continuous_compact_oriented_map_resampled_independentPairHybridBoundaryResamplingCoupling]
  rfl

/-- Difference of native heat-bath fluctuations across one configuration pair. -/
def ContinuousCompactOrientedGaugeWilsonSystem.configurationPairHeatBathFluctuationDifferenceBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (y : C.base.Configuration × C.base.Configuration) : ℝ :=
  C.singleLinkHeatBathFluctuation target O y.2 -
    C.singleLinkHeatBathFluctuation target O y.1

/-- Actual-side fluctuation difference on the configuration-level coupling. -/
def ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridBoundaryResamplingActualDifferenceBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : (C.base.Configuration × C.base.Configuration) ×
      (C.base.Configuration × C.base.Configuration)) : ℝ :=
  C.configurationPairHeatBathFluctuationDifferenceBCF target O z.1

/-- Resampled-side fluctuation difference on the configuration-level coupling. -/
def ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridBoundaryResamplingResampledDifferenceBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : (C.base.Configuration × C.base.Configuration) ×
      (C.base.Configuration × C.base.Configuration)) : ℝ :=
  C.configurationPairHeatBathFluctuationDifferenceBCF target O z.2

/-- Transport residual for the first endpoint. -/
def ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridBoundaryResamplingFirstResidualBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : (C.base.Configuration × C.base.Configuration) ×
      (C.base.Configuration × C.base.Configuration)) : ℝ :=
  C.singleLinkHeatBathFluctuation target O z.2.1 -
    C.singleLinkHeatBathFluctuation target O z.1.1

/-- Transport residual for the second endpoint. -/
def ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridBoundaryResamplingSecondResidualBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : (C.base.Configuration × C.base.Configuration) ×
      (C.base.Configuration × C.base.Configuration)) : ℝ :=
  C.singleLinkHeatBathFluctuation target O z.1.2 -
    C.singleLinkHeatBathFluctuation target O z.2.2

/-- Exact three-term decomposition of the actual fluctuation difference into the
resampled conditional-pair difference and the two endpoint transport residuals. -/
theorem continuous_compact_oriented_independentPairHybridBoundaryResampling_difference_decomposition
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : (C.base.Configuration × C.base.Configuration) ×
      (C.base.Configuration × C.base.Configuration)) :
    C.independentPairHybridBoundaryResamplingActualDifferenceBCF target O z =
      C.independentPairHybridBoundaryResamplingFirstResidualBCF target O z +
      C.independentPairHybridBoundaryResamplingResampledDifferenceBCF target O z +
      C.independentPairHybridBoundaryResamplingSecondResidualBCF target O z := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridBoundaryResamplingActualDifferenceBCF
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridBoundaryResamplingResampledDifferenceBCF
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridBoundaryResamplingFirstResidualBCF
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridBoundaryResamplingSecondResidualBCF
    ContinuousCompactOrientedGaugeWilsonSystem.configurationPairHeatBathFluctuationDifferenceBCF
  ring

/-- Pointwise square control obtained from the exact three-term decomposition. -/
theorem continuous_compact_oriented_independentPairHybridBoundaryResampling_actualDifference_sq_le_three
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : (C.base.Configuration × C.base.Configuration) ×
      (C.base.Configuration × C.base.Configuration)) :
    (C.independentPairHybridBoundaryResamplingActualDifferenceBCF target O z) ^ 2 ≤
      3 *
        ((C.independentPairHybridBoundaryResamplingFirstResidualBCF target O z) ^ 2 +
         (C.independentPairHybridBoundaryResamplingResampledDifferenceBCF target O z) ^ 2 +
         (C.independentPairHybridBoundaryResamplingSecondResidualBCF target O z) ^ 2) := by
  rw [continuous_compact_oriented_independentPairHybridBoundaryResampling_difference_decomposition
    C target O z]
  nlinarith
    [sq_nonneg
      (C.independentPairHybridBoundaryResamplingFirstResidualBCF target O z -
        C.independentPairHybridBoundaryResamplingResampledDifferenceBCF target O z),
     sq_nonneg
      (C.independentPairHybridBoundaryResamplingFirstResidualBCF target O z -
        C.independentPairHybridBoundaryResamplingSecondResidualBCF target O z),
     sq_nonneg
      (C.independentPairHybridBoundaryResamplingResampledDifferenceBCF target O z -
        C.independentPairHybridBoundaryResamplingSecondResidualBCF target O z)]

end

end MathlibAnalytic
end MGAP4D