import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonBoundaryKernelRNDerivativeBCF
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

noncomputable section

/-- Source-pair map to the actual off-target boundary immediately before the
canonical hybrid update at `target`. -/
def ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridPreBoundaryMap
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    C.base.Configuration × C.base.Configuration → C.OffTargetBoundary target :=
  fun z => C.offTargetBoundaryMap target
    (C.independentPairHybridPreEndpointMap target z)

/-- The actual hybrid pre-boundary map is measurable. -/
theorem continuous_compact_oriented_independentPairHybridPreBoundaryMap_measurable
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    Measurable (C.independentPairHybridPreBoundaryMap target) :=
  (continuous_compact_oriented_offTargetBoundaryMap_measurable C target).comp
    (continuous_compact_oriented_independentPairHybridPreEndpointMap_measurable
      C target)

/-- Source-pair map to the actual hybrid boundary-target-pair output. -/
def ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridActualBoundaryTargetPairMap
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    C.base.Configuration × C.base.Configuration →
      C.OffTargetBoundaryTargetPair target :=
  fun z => C.offTargetBoundaryTargetPairMap target
    (C.independentPairHybridEndpointPairMap target z)

/-- The actual hybrid boundary-target-pair map is measurable. -/
theorem continuous_compact_oriented_independentPairHybridActualBoundaryTargetPairMap_measurable
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    Measurable (C.independentPairHybridActualBoundaryTargetPairMap target) :=
  (continuous_compact_oriented_offTargetBoundaryTargetPairMap_measurable
    C target).comp
    (continuous_compact_oriented_independentPairHybridEndpointPairMap_measurable
      C target)

/-- The first coordinate of the actual hybrid joint map is exactly the boundary
used to index the resampling kernel. -/
theorem continuous_compact_oriented_fst_independentPairHybridActualBoundaryTargetPairMap
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (z : C.base.Configuration × C.base.Configuration) :
    (C.independentPairHybridActualBoundaryTargetPairMap target z).1 =
      C.independentPairHybridPreBoundaryMap target z := by
  simpa
    [ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridActualBoundaryTargetPairMap,
      ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridPreBoundaryMap]
    using congrArg Prod.fst
      (continuous_compact_oriented_offTargetBoundaryTargetPairMap_hybridEndpointPairMap
        C target z)

/-- The actual hybrid joint law is the pushforward of the independent Gibbs
source pair by the named actual joint map. -/
theorem continuous_compact_oriented_independentPairHybridBoundaryTargetPairMeasure_eq_map_actual
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    C.independentPairHybridBoundaryTargetPairMeasure target =
      Measure.map (C.independentPairHybridActualBoundaryTargetPairMap target)
        (C.gibbsMeasure.prod C.gibbsMeasure) := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridBoundaryTargetPairMeasure
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridEndpointPairMeasure
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridActualBoundaryTargetPairMap
  rw [Measure.map_map
    (continuous_compact_oriented_offTargetBoundaryTargetPairMap_measurable C target)
    (continuous_compact_oriented_independentPairHybridEndpointPairMap_measurable
      C target)]

/-- The hybrid off-target boundary law is the pushforward of the independent
Gibbs source pair by the named pre-boundary map. -/
theorem continuous_compact_oriented_independentPairHybridOffTargetBoundaryMeasure_eq_map_preBoundary
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    C.independentPairHybridOffTargetBoundaryMeasure target =
      Measure.map (C.independentPairHybridPreBoundaryMap target)
        (C.gibbsMeasure.prod C.gibbsMeasure) := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridOffTargetBoundaryMeasure
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridPreEndpointMeasure
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridPreBoundaryMap
  rw [Measure.map_map
    (continuous_compact_oriented_offTargetBoundaryMap_measurable C target)
    (continuous_compact_oriented_independentPairHybridPreEndpointMap_measurable
      C target)]

/-- Given an independent Gibbs source pair, retain its actual hybrid pre-boundary
and resample two exact native target-link values conditionally on that boundary. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridBoundaryResamplingKernel
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    Kernel (C.base.Configuration × C.base.Configuration)
      (C.OffTargetBoundaryTargetPair target) :=
  C.singleLinkBoundaryTargetPairKernel target ∘ₖ
    Kernel.deterministic (C.independentPairHybridPreBoundaryMap target)
      (continuous_compact_oriented_independentPairHybridPreBoundaryMap_measurable
        C target)

/-- The hybrid boundary-resampling kernel is Markov. -/
instance continuousCompactOriented_independentPairHybridBoundaryResamplingKernel_isMarkov
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    IsMarkovKernel (C.independentPairHybridBoundaryResamplingKernel target) := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridBoundaryResamplingKernel
  infer_instance

/-- The resampling kernel keeps exactly the actual hybrid pre-boundary. -/
theorem continuous_compact_oriented_fst_independentPairHybridBoundaryResamplingKernel
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    (C.independentPairHybridBoundaryResamplingKernel target).map Prod.fst =
      Kernel.deterministic (C.independentPairHybridPreBoundaryMap target)
        (continuous_compact_oriented_independentPairHybridPreBoundaryMap_measurable
          C target) := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridBoundaryResamplingKernel
  rw [Kernel.map_comp,
    continuous_compact_oriented_map_fst_singleLinkBoundaryTargetPairKernel,
    Kernel.id_comp]

/-- Coupling kernel whose first output is the actual hybrid joint point and whose
second output is an exact native conditional pair resampled at the same boundary. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridBoundaryResamplingCouplingKernel
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    Kernel (C.base.Configuration × C.base.Configuration)
      (C.OffTargetBoundaryTargetPair target ×
        C.OffTargetBoundaryTargetPair target) :=
  Kernel.deterministic
      (C.independentPairHybridActualBoundaryTargetPairMap target)
      (continuous_compact_oriented_independentPairHybridActualBoundaryTargetPairMap_measurable
        C target) ×ₖ
    C.independentPairHybridBoundaryResamplingKernel target

/-- The actual/resampled hybrid coupling kernel is Markov. -/
instance continuousCompactOriented_independentPairHybridBoundaryResamplingCouplingKernel_isMarkov
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    IsMarkovKernel
      (C.independentPairHybridBoundaryResamplingCouplingKernel target) := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridBoundaryResamplingCouplingKernel
  infer_instance

/-- Coupling measure obtained by averaging the common-boundary coupling kernel
over two independent genuine Gibbs configurations. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridBoundaryResamplingCouplingMeasure
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    Measure
      (C.OffTargetBoundaryTargetPair target ×
        C.OffTargetBoundaryTargetPair target) :=
  C.independentPairHybridBoundaryResamplingCouplingKernel target ∘ₘ
    (C.gibbsMeasure.prod C.gibbsMeasure)

/-- The first marginal of the common-boundary coupling is the actual canonical
hybrid boundary-target-pair law. -/
theorem continuous_compact_oriented_map_actual_independentPairHybridBoundaryResamplingCoupling
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    Measure.map Prod.fst
        (C.independentPairHybridBoundaryResamplingCouplingMeasure target) =
      C.independentPairHybridBoundaryTargetPairMeasure target := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridBoundaryResamplingCouplingMeasure
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridBoundaryResamplingCouplingKernel
  rw [Measure.map_comp (C.gibbsMeasure.prod C.gibbsMeasure) _ measurable_fst]
  change
    (Kernel.fst
      (Kernel.deterministic
          (C.independentPairHybridActualBoundaryTargetPairMap target)
          (continuous_compact_oriented_independentPairHybridActualBoundaryTargetPairMap_measurable
            C target) ×ₖ
        C.independentPairHybridBoundaryResamplingKernel target)) ∘ₘ
        (C.gibbsMeasure.prod C.gibbsMeasure) =
      C.independentPairHybridBoundaryTargetPairMeasure target
  rw [Kernel.fst_prod, Measure.deterministic_comp_eq_map]
  exact
    (continuous_compact_oriented_independentPairHybridBoundaryTargetPairMeasure_eq_map_actual
      C target).symm

/-- The second marginal of the common-boundary coupling is the hybrid
boundary-driven law obtained by exact conditional-pair resampling. -/
theorem continuous_compact_oriented_map_resampled_independentPairHybridBoundaryResamplingCoupling
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    Measure.map Prod.snd
        (C.independentPairHybridBoundaryResamplingCouplingMeasure target) =
      C.independentPairHybridBoundaryDrivenTargetPairMeasure target := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridBoundaryResamplingCouplingMeasure
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridBoundaryResamplingCouplingKernel
  rw [Measure.map_comp (C.gibbsMeasure.prod C.gibbsMeasure) _ measurable_snd]
  change
    (Kernel.snd
      (Kernel.deterministic
          (C.independentPairHybridActualBoundaryTargetPairMap target)
          (continuous_compact_oriented_independentPairHybridActualBoundaryTargetPairMap_measurable
            C target) ×ₖ
        C.independentPairHybridBoundaryResamplingKernel target)) ∘ₘ
        (C.gibbsMeasure.prod C.gibbsMeasure) =
      C.independentPairHybridBoundaryDrivenTargetPairMeasure target
  rw [Kernel.snd_prod]
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridBoundaryResamplingKernel
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridBoundaryDrivenTargetPairMeasure
  rw [← Measure.comp_assoc, Measure.deterministic_comp_eq_map,
    ← continuous_compact_oriented_independentPairHybridOffTargetBoundaryMeasure_eq_map_preBoundary]

end

end MathlibAnalytic
end MGAP4D
