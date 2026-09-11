import MGAP4D.MathlibAnalytic.PeriodicHypercubicSpecialUnitaryHybridNativeOneLinkSupportBCF
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

noncomputable section

/-- The off-target boundary carrier for one physical link. -/
abbrev ContinuousCompactOrientedGaugeWilsonSystem.OffTargetBoundary
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) : Type :=
  {source : C.base.geometry.Edge // source ≠ target} → C.base.Gauge

/-- Restrict a full configuration to all physical links except the target. -/
def ContinuousCompactOrientedGaugeWilsonSystem.offTargetBoundaryMap
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    C.base.Configuration → C.OffTargetBoundary target :=
  fun A source => A source.1

/-- The off-target boundary restriction is continuous. -/
theorem continuous_compact_oriented_offTargetBoundaryMap_continuous
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    Continuous (C.offTargetBoundaryMap target) := by
  apply continuous_pi
  intro source
  exact continuous_apply source.1

/-- The off-target boundary restriction is measurable. -/
theorem continuous_compact_oriented_offTargetBoundaryMap_measurable
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    Measurable (C.offTargetBoundaryMap target) :=
  (continuous_compact_oriented_offTargetBoundaryMap_continuous C target).measurable

/-- Restrict both members of a configuration pair to the off-target boundary. -/
def ContinuousCompactOrientedGaugeWilsonSystem.offTargetBoundaryPairMap
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    C.base.Configuration × C.base.Configuration →
      C.OffTargetBoundary target × C.OffTargetBoundary target :=
  fun y =>
    (C.offTargetBoundaryMap target y.1,
      C.offTargetBoundaryMap target y.2)

/-- The pair-valued boundary restriction is continuous. -/
theorem continuous_compact_oriented_offTargetBoundaryPairMap_continuous
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    Continuous (C.offTargetBoundaryPairMap target) := by
  exact
    ((continuous_compact_oriented_offTargetBoundaryMap_continuous C target).comp
      continuous_fst).prodMk
      ((continuous_compact_oriented_offTargetBoundaryMap_continuous C target).comp
        continuous_snd)

/-- The pair-valued boundary restriction is measurable. -/
theorem continuous_compact_oriented_offTargetBoundaryPairMap_measurable
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    Measurable (C.offTargetBoundaryPairMap target) :=
  (continuous_compact_oriented_offTargetBoundaryPairMap_continuous C target).measurable

/-- Diagonal embedding of one off-target boundary into a boundary pair. -/
def ContinuousCompactOrientedGaugeWilsonSystem.offTargetBoundaryDiagonalMap
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    C.OffTargetBoundary target →
      C.OffTargetBoundary target × C.OffTargetBoundary target :=
  fun boundary => (boundary, boundary)

/-- The boundary diagonal embedding is continuous. -/
theorem continuous_compact_oriented_offTargetBoundaryDiagonalMap_continuous
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    Continuous (C.offTargetBoundaryDiagonalMap target) :=
  continuous_id.prodMk continuous_id

/-- Agreement away from the target is exactly equality of boundary restrictions. -/
theorem continuous_compact_oriented_offTargetBoundaryMap_eq_of_agreeOffLink
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (B A : C.base.Configuration)
    (hAgree : C.base.AgreeOffLink B A target) :
    C.offTargetBoundaryMap target B =
      C.offTargetBoundaryMap target A := by
  funext source
  exact hAgree source.1 source.2

/-- Every canonical hybrid endpoint pair restricts to a diagonal boundary pair. -/
theorem continuous_compact_oriented_offTargetBoundaryPairMap_hybridEndpointPairMap
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (z : C.base.Configuration × C.base.Configuration) :
    C.offTargetBoundaryPairMap target
        (C.independentPairHybridEndpointPairMap target z) =
      C.offTargetBoundaryDiagonalMap target
        (C.offTargetBoundaryMap target
          (C.independentPairHybridEndpointPairMap target z).1) := by
  apply Prod.ext
  · rfl
  · exact
      continuous_compact_oriented_offTargetBoundaryMap_eq_of_agreeOffLink
        C target _ _
        (continuous_compact_oriented_independentPairHybridEndpointPairMap_agreeOffLink
          C target z)

/-- Every native two-sample conditional pair also restricts to the diagonal
boundary of its common background. -/
theorem continuous_compact_oriented_offTargetBoundaryPairMap_singleLinkConditionalPairConfigurationMap
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (A : C.base.Configuration)
    (z : C.base.Gauge × C.base.Gauge) :
    C.offTargetBoundaryPairMap target
        (C.singleLinkConditionalPairConfigurationMap A target z) =
      C.offTargetBoundaryDiagonalMap target
        (C.offTargetBoundaryMap target A) := by
  apply Prod.ext <;> funext source
  · simp [ContinuousCompactOrientedGaugeWilsonSystem.offTargetBoundaryPairMap,
      ContinuousCompactOrientedGaugeWilsonSystem.offTargetBoundaryDiagonalMap,
      ContinuousCompactOrientedGaugeWilsonSystem.offTargetBoundaryMap,
      ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalPairConfigurationMap,
      CompactOrientedGaugeWilsonSystem.replaceLink, source.2]
  · simp [ContinuousCompactOrientedGaugeWilsonSystem.offTargetBoundaryPairMap,
      ContinuousCompactOrientedGaugeWilsonSystem.offTargetBoundaryDiagonalMap,
      ContinuousCompactOrientedGaugeWilsonSystem.offTargetBoundaryMap,
      ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalPairConfigurationMap,
      CompactOrientedGaugeWilsonSystem.replaceLink, source.2]

/-- Boundary law of the pre-step endpoint in the canonical independent-pair
hybrid construction. -/
def ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridOffTargetBoundaryMeasure
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    Measure (C.OffTargetBoundary target) :=
  Measure.map (C.offTargetBoundaryMap target)
    (C.independentPairHybridPreEndpointMeasure target)

/-- The boundary-pair pushforward of the hybrid endpoint transport plan is the
diagonal embedding of its pre-endpoint boundary law. -/
theorem continuous_compact_oriented_map_offTargetBoundaryPairMap_independentPairHybridEndpointPairMeasure
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    Measure.map (C.offTargetBoundaryPairMap target)
        (C.independentPairHybridEndpointPairMeasure target) =
      Measure.map (C.offTargetBoundaryDiagonalMap target)
        (C.independentPairHybridOffTargetBoundaryMeasure target) := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridEndpointPairMeasure
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridOffTargetBoundaryMeasure
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridPreEndpointMeasure
  rw [Measure.map_map
    (continuous_compact_oriented_offTargetBoundaryPairMap_measurable C target)
    (continuous_compact_oriented_independentPairHybridEndpointPairMap_measurable
      C target)]
  rw [Measure.map_map
    (continuous_compact_oriented_offTargetBoundaryDiagonalMap_continuous
      C target).measurable
    (continuous_compact_oriented_offTargetBoundaryMap_measurable C target)]
  rw [Measure.map_map
    ((continuous_compact_oriented_offTargetBoundaryDiagonalMap_continuous
      C target).comp
      (continuous_compact_oriented_offTargetBoundaryMap_continuous
        C target)).measurable
    (continuous_compact_oriented_independentPairHybridPreEndpointMap_measurable
      C target)]
  apply Measure.map_congr
  exact Filter.Eventually.of_forall fun z =>
    continuous_compact_oriented_offTargetBoundaryPairMap_hybridEndpointPairMap
      C target z

/-- At every Gibbs background, the native independent conditional-pair kernel
has a deterministic diagonal off-target boundary law. -/
theorem continuous_compact_oriented_map_offTargetBoundaryPairMap_singleLinkHeatBathIndependentPairKernel
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (A : C.base.Configuration) :
    Measure.map (C.offTargetBoundaryPairMap target)
        (C.singleLinkHeatBathIndependentPairKernel target A) =
      Measure.dirac
        (C.offTargetBoundaryDiagonalMap target
          (C.offTargetBoundaryMap target A)) := by
  letI : IsProbabilityMeasure (C.singleLinkConditionalMeasure A target) :=
    continuous_compact_oriented_singleLinkConditionalMeasure_isProbabilityMeasure
      C A target
  rw [continuous_compact_oriented_singleLinkHeatBathIndependentPairKernel_apply]
  rw [Measure.map_map
    (continuous_compact_oriented_offTargetBoundaryPairMap_measurable C target)
    (continuous_compact_oriented_singleLinkConditionalPairConfigurationMap_continuous
      C A target).measurable]
  calc
    Measure.map
        (C.offTargetBoundaryPairMap target ∘
          C.singleLinkConditionalPairConfigurationMap A target)
        ((C.singleLinkConditionalMeasure A target).prod
          (C.singleLinkConditionalMeasure A target)) =
      Measure.map
        (fun _ : C.base.Gauge × C.base.Gauge =>
          C.offTargetBoundaryDiagonalMap target
            (C.offTargetBoundaryMap target A))
        ((C.singleLinkConditionalMeasure A target).prod
          (C.singleLinkConditionalMeasure A target)) := by
      apply Measure.map_congr
      exact Filter.Eventually.of_forall fun z =>
        continuous_compact_oriented_offTargetBoundaryPairMap_singleLinkConditionalPairConfigurationMap
          C target A z
    _ = Measure.dirac
        (C.offTargetBoundaryDiagonalMap target
          (C.offTargetBoundaryMap target A)) := by
      simp

end

end MathlibAnalytic
end MGAP4D
