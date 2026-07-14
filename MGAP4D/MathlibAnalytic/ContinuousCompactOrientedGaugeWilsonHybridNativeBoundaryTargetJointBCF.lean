import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridNativeOffTargetBoundaryBCF
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

noncomputable section

/-- Common carrier recording one off-target boundary together with the two
values at the updated physical link. -/
abbrev ContinuousCompactOrientedGaugeWilsonSystem.OffTargetBoundaryTargetPair
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) : Type :=
  C.OffTargetBoundary target × (C.base.Gauge × C.base.Gauge)

/-- Extract the first configuration's off-target boundary and both target-link
values from a configuration pair.  On either the hybrid or native one-link
support, the first boundary is also the second boundary. -/
def ContinuousCompactOrientedGaugeWilsonSystem.offTargetBoundaryTargetPairMap
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    C.base.Configuration × C.base.Configuration →
      C.OffTargetBoundaryTargetPair target :=
  fun y =>
    (C.offTargetBoundaryMap target y.1,
      (y.1 target, y.2 target))

/-- The boundary-target-pair extraction map is continuous. -/
theorem continuous_compact_oriented_offTargetBoundaryTargetPairMap_continuous
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    Continuous (C.offTargetBoundaryTargetPairMap target) := by
  exact
    ((continuous_compact_oriented_offTargetBoundaryMap_continuous C target).comp
      continuous_fst).prodMk
      (((continuous_apply target).comp continuous_fst).prodMk
        ((continuous_apply target).comp continuous_snd))

/-- The boundary-target-pair extraction map is measurable. -/
theorem continuous_compact_oriented_offTargetBoundaryTargetPairMap_measurable
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    Measurable (C.offTargetBoundaryTargetPairMap target) :=
  (continuous_compact_oriented_offTargetBoundaryTargetPairMap_continuous
    C target).measurable

/-- Insert one fixed off-target background boundary beside a pair of target-link
values. -/
def ContinuousCompactOrientedGaugeWilsonSystem.offTargetBoundaryTargetPairInsertMap
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (A : C.base.Configuration) :
    C.base.Gauge × C.base.Gauge → C.OffTargetBoundaryTargetPair target :=
  fun z => (C.offTargetBoundaryMap target A, z)

/-- Inserting a fixed boundary beside a target pair is continuous. -/
theorem continuous_compact_oriented_offTargetBoundaryTargetPairInsertMap_continuous
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (A : C.base.Configuration) :
    Continuous (C.offTargetBoundaryTargetPairInsertMap target A) := by
  exact
    (continuous_const : Continuous
      (fun _ : C.base.Gauge × C.base.Gauge =>
        C.offTargetBoundaryMap target A)).prodMk continuous_id

/-- Inserting a fixed boundary beside a target pair is measurable. -/
theorem continuous_compact_oriented_offTargetBoundaryTargetPairInsertMap_measurable
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (A : C.base.Configuration) :
    Measurable (C.offTargetBoundaryTargetPairInsertMap target A) :=
  (continuous_compact_oriented_offTargetBoundaryTargetPairInsertMap_continuous
    C target A).measurable

/-- On a canonical hybrid step, the common boundary is the pre-step boundary and
the two target values are the left and right Gibbs coordinates. -/
theorem continuous_compact_oriented_offTargetBoundaryTargetPairMap_hybridEndpointPairMap
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (z : C.base.Configuration × C.base.Configuration) :
    C.offTargetBoundaryTargetPairMap target
        (C.independentPairHybridEndpointPairMap target z) =
      (C.offTargetBoundaryMap target
          (C.independentPairHybridPreEndpointMap target z),
        (z.1 target, z.2 target)) := by
  simp
    [ContinuousCompactOrientedGaugeWilsonSystem.offTargetBoundaryTargetPairMap,
      ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridEndpointPairMap]

/-- On a native conditional pair generated from one background, the joint
boundary-target extraction is exactly the fixed background boundary beside the
sampled target pair. -/
theorem continuous_compact_oriented_offTargetBoundaryTargetPairMap_singleLinkConditionalPairConfigurationMap
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (A : C.base.Configuration)
    (z : C.base.Gauge × C.base.Gauge) :
    C.offTargetBoundaryTargetPairMap target
        (C.singleLinkConditionalPairConfigurationMap A target z) =
      C.offTargetBoundaryTargetPairInsertMap target A z := by
  apply Prod.ext
  · funext source
    simp
      [ContinuousCompactOrientedGaugeWilsonSystem.offTargetBoundaryTargetPairMap,
        ContinuousCompactOrientedGaugeWilsonSystem.offTargetBoundaryTargetPairInsertMap,
        ContinuousCompactOrientedGaugeWilsonSystem.offTargetBoundaryMap,
        ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalPairConfigurationMap,
        CompactOrientedGaugeWilsonSystem.replaceLink, source.2]
  · apply Prod.ext <;>
      simp
        [ContinuousCompactOrientedGaugeWilsonSystem.offTargetBoundaryTargetPairMap,
          ContinuousCompactOrientedGaugeWilsonSystem.offTargetBoundaryTargetPairInsertMap,
          ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalPairConfigurationMap,
          CompactOrientedGaugeWilsonSystem.replaceLink]

/-- The canonical hybrid law on the common boundary-target-pair carrier. -/
def ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridBoundaryTargetPairMeasure
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    Measure (C.OffTargetBoundaryTargetPair target) :=
  Measure.map (C.offTargetBoundaryTargetPairMap target)
    (C.independentPairHybridEndpointPairMeasure target)

/-- The hybrid boundary-target-pair law is the direct pushforward of two
independent Gibbs configurations by the explicit hybrid joint map. -/
theorem continuous_compact_oriented_independentPairHybridBoundaryTargetPairMeasure_eq_map_gibbsProd
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    C.independentPairHybridBoundaryTargetPairMeasure target =
      Measure.map
        (fun z : C.base.Configuration × C.base.Configuration =>
          (C.offTargetBoundaryMap target
              (C.independentPairHybridPreEndpointMap target z),
            (z.1 target, z.2 target)))
        (C.gibbsMeasure.prod C.gibbsMeasure) := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridBoundaryTargetPairMeasure
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridEndpointPairMeasure
  rw [Measure.map_map
    (continuous_compact_oriented_offTargetBoundaryTargetPairMap_measurable C target)
    (continuous_compact_oriented_independentPairHybridEndpointPairMap_measurable
      C target)]
  apply Measure.map_congr
  exact Filter.Eventually.of_forall fun z =>
    continuous_compact_oriented_offTargetBoundaryTargetPairMap_hybridEndpointPairMap
      C target z

/-- The off-target boundary marginal of the hybrid joint law is exactly the
previously defined hybrid pre-endpoint boundary law. -/
theorem continuous_compact_oriented_map_fst_independentPairHybridBoundaryTargetPairMeasure
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    Measure.map Prod.fst
        (C.independentPairHybridBoundaryTargetPairMeasure target) =
      C.independentPairHybridOffTargetBoundaryMeasure target := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridBoundaryTargetPairMeasure
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridEndpointPairMeasure
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridOffTargetBoundaryMeasure
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridPreEndpointMeasure
  rw [Measure.map_map measurable_fst
    (continuous_compact_oriented_offTargetBoundaryTargetPairMap_measurable C target)]
  rw [Measure.map_map
    (((continuous_fst : Continuous
      (fun x : C.OffTargetBoundaryTargetPair target => x.1)).comp
        (continuous_compact_oriented_offTargetBoundaryTargetPairMap_continuous
          C target)).measurable)
    (continuous_compact_oriented_independentPairHybridEndpointPairMap_measurable
      C target)]
  rw [Measure.map_map
    (continuous_compact_oriented_offTargetBoundaryMap_measurable C target)
    (continuous_compact_oriented_independentPairHybridPreEndpointMap_measurable
      C target)]
  apply Measure.map_congr
  exact Filter.Eventually.of_forall fun z => by
    rfl

/-- The two target-link values under the hybrid joint law are independent and
both have the genuine Gibbs target-coordinate marginal. -/
theorem continuous_compact_oriented_map_snd_independentPairHybridBoundaryTargetPairMeasure
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    Measure.map Prod.snd
        (C.independentPairHybridBoundaryTargetPairMeasure target) =
      (C.gibbsTargetCoordinateMeasure target).prod
        (C.gibbsTargetCoordinateMeasure target) := by
  letI : IsProbabilityMeasure C.gibbsMeasure :=
    continuous_compact_oriented_gibbsMeasure_isProbabilityMeasure C
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridBoundaryTargetPairMeasure
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridEndpointPairMeasure
    ContinuousCompactOrientedGaugeWilsonSystem.gibbsTargetCoordinateMeasure
  rw [Measure.map_map measurable_snd
    (continuous_compact_oriented_offTargetBoundaryTargetPairMap_measurable C target)]
  rw [Measure.map_map
    (((continuous_snd : Continuous
      (fun x : C.OffTargetBoundaryTargetPair target => x.2)).comp
        (continuous_compact_oriented_offTargetBoundaryTargetPairMap_continuous
          C target)).measurable)
    (continuous_compact_oriented_independentPairHybridEndpointPairMap_measurable
      C target)]
  calc
    Measure.map
        (Prod.snd ∘ C.offTargetBoundaryTargetPairMap target ∘
          C.independentPairHybridEndpointPairMap target)
        (C.gibbsMeasure.prod C.gibbsMeasure) =
      Measure.map
        (Prod.map
          (fun A : C.base.Configuration => A target)
          (fun A : C.base.Configuration => A target))
        (C.gibbsMeasure.prod C.gibbsMeasure) := by
      apply Measure.map_congr
      exact Filter.Eventually.of_forall fun z => by
        simp
          [ContinuousCompactOrientedGaugeWilsonSystem.offTargetBoundaryTargetPairMap,
            ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridEndpointPairMap,
            Prod.map]
    _ = (Measure.map (fun A : C.base.Configuration => A target) C.gibbsMeasure).prod
        (Measure.map (fun A : C.base.Configuration => A target) C.gibbsMeasure) := by
      simpa using
        (Measure.map_prod_map
          C.gibbsMeasure C.gibbsMeasure
          (continuous_apply target).measurable
          (continuous_apply target).measurable).symm

/-- The native boundary-target-pair kernel is obtained by mapping the native
configuration-pair kernel to the common joint carrier. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkHeatBathBoundaryTargetPairKernel
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    Kernel C.base.Configuration (C.OffTargetBoundaryTargetPair target) :=
  (C.singleLinkHeatBathIndependentPairKernel target).map
    (C.offTargetBoundaryTargetPairMap target)

/-- The native boundary-target-pair kernel is Markov. -/
instance continuousCompactOriented_singleLinkHeatBathBoundaryTargetPairKernel_isMarkov
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    IsMarkovKernel (C.singleLinkHeatBathBoundaryTargetPairKernel target) := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkHeatBathBoundaryTargetPairKernel
  infer_instance

/-- Pointwise in the Gibbs background, the native joint kernel is exactly the
pushforward of two independent conditional target samples beside the fixed
background boundary. -/
theorem continuous_compact_oriented_singleLinkHeatBathBoundaryTargetPairKernel_apply
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (A : C.base.Configuration) :
    C.singleLinkHeatBathBoundaryTargetPairKernel target A =
      Measure.map (C.offTargetBoundaryTargetPairInsertMap target A)
        ((C.singleLinkConditionalMeasure A target).prod
          (C.singleLinkConditionalMeasure A target)) := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkHeatBathBoundaryTargetPairKernel
  rw [Kernel.map_apply _
    (continuous_compact_oriented_offTargetBoundaryTargetPairMap_measurable C target)
    A]
  rw [continuous_compact_oriented_singleLinkHeatBathIndependentPairKernel_apply]
  rw [Measure.map_map
    (continuous_compact_oriented_offTargetBoundaryTargetPairMap_measurable C target)
    (continuous_compact_oriented_singleLinkConditionalPairConfigurationMap_continuous
      C A target).measurable]
  apply Measure.map_congr
  exact Filter.Eventually.of_forall fun z =>
    continuous_compact_oriented_offTargetBoundaryTargetPairMap_singleLinkConditionalPairConfigurationMap
      C target A z

/-- The boundary marginal of the native joint kernel is the Dirac mass at the
background's off-target boundary. -/
theorem continuous_compact_oriented_map_fst_singleLinkHeatBathBoundaryTargetPairKernel_apply
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (A : C.base.Configuration) :
    Measure.map Prod.fst
        (C.singleLinkHeatBathBoundaryTargetPairKernel target A) =
      Measure.dirac (C.offTargetBoundaryMap target A) := by
  letI : IsProbabilityMeasure (C.singleLinkConditionalMeasure A target) :=
    continuous_compact_oriented_singleLinkConditionalMeasure_isProbabilityMeasure
      C A target
  rw [continuous_compact_oriented_singleLinkHeatBathBoundaryTargetPairKernel_apply]
  rw [Measure.map_map measurable_fst
    (continuous_compact_oriented_offTargetBoundaryTargetPairInsertMap_measurable
      C target A)]
  simp
    [ContinuousCompactOrientedGaugeWilsonSystem.offTargetBoundaryTargetPairInsertMap]

/-- The target-pair marginal of the native joint kernel is exactly the product
of the two native one-link conditional measures. -/
theorem continuous_compact_oriented_map_snd_singleLinkHeatBathBoundaryTargetPairKernel_apply
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (A : C.base.Configuration) :
    Measure.map Prod.snd
        (C.singleLinkHeatBathBoundaryTargetPairKernel target A) =
      (C.singleLinkConditionalMeasure A target).prod
        (C.singleLinkConditionalMeasure A target) := by
  rw [continuous_compact_oriented_singleLinkHeatBathBoundaryTargetPairKernel_apply]
  rw [Measure.map_map measurable_snd
    (continuous_compact_oriented_offTargetBoundaryTargetPairInsertMap_measurable
      C target A)]
  simp
    [ContinuousCompactOrientedGaugeWilsonSystem.offTargetBoundaryTargetPairInsertMap]

/-- The Gibbs-averaged native law on the same boundary-target-pair carrier. -/
def ContinuousCompactOrientedGaugeWilsonSystem.singleLinkHeatBathBoundaryTargetPairMeasure
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    Measure (C.OffTargetBoundaryTargetPair target) :=
  Measure.map (C.offTargetBoundaryTargetPairMap target)
    (C.singleLinkHeatBathIndependentPairMeasure target)

/-- Gibbs off-target boundary marginal at one physical target link. -/
def ContinuousCompactOrientedGaugeWilsonSystem.gibbsOffTargetBoundaryMeasure
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    Measure (C.OffTargetBoundary target) :=
  Measure.map (C.offTargetBoundaryMap target) C.gibbsMeasure

/-- The Gibbs-averaged native joint law is the composition of the native joint
kernel with the Gibbs measure. -/
theorem continuous_compact_oriented_singleLinkHeatBathBoundaryTargetPairMeasure_eq_kernel_comp
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    C.singleLinkHeatBathBoundaryTargetPairMeasure target =
      C.singleLinkHeatBathBoundaryTargetPairKernel target ∘ₘ C.gibbsMeasure := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkHeatBathBoundaryTargetPairMeasure
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkHeatBathIndependentPairMeasure
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkHeatBathBoundaryTargetPairKernel
  rw [Measure.map_comp C.gibbsMeasure
    (C.singleLinkHeatBathIndependentPairKernel target)
    (continuous_compact_oriented_offTargetBoundaryTargetPairMap_measurable C target)]

/-- The off-target boundary marginal of the Gibbs-averaged native joint law is
the genuine Gibbs boundary marginal. -/
theorem continuous_compact_oriented_map_fst_singleLinkHeatBathBoundaryTargetPairMeasure
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    Measure.map Prod.fst
        (C.singleLinkHeatBathBoundaryTargetPairMeasure target) =
      C.gibbsOffTargetBoundaryMeasure target := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkHeatBathBoundaryTargetPairMeasure
    ContinuousCompactOrientedGaugeWilsonSystem.gibbsOffTargetBoundaryMeasure
  rw [Measure.map_map measurable_fst
    (continuous_compact_oriented_offTargetBoundaryTargetPairMap_measurable C target)]
  calc
    Measure.map
        (Prod.fst ∘ C.offTargetBoundaryTargetPairMap target)
        (C.singleLinkHeatBathIndependentPairMeasure target) =
      Measure.map
        (C.offTargetBoundaryMap target ∘ Prod.fst)
        (C.singleLinkHeatBathIndependentPairMeasure target) := by
      apply Measure.map_congr
      exact Filter.Eventually.of_forall fun _ => rfl
    _ = Measure.map (C.offTargetBoundaryMap target)
        (Measure.map Prod.fst
          (C.singleLinkHeatBathIndependentPairMeasure target)) := by
      rw [Measure.map_map
        (continuous_compact_oriented_offTargetBoundaryMap_measurable C target)
        measurable_fst]
    _ = Measure.map (C.offTargetBoundaryMap target) C.gibbsMeasure := by
      rw [continuous_compact_oriented_map_fst_singleLinkHeatBathIndependentPairMeasure]

end

end MathlibAnalytic
end MGAP4D