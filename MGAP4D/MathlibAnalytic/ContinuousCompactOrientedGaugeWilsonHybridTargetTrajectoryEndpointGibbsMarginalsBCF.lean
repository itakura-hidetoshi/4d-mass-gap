import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryEndpointCouplingBCF
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory Finset Preorder Function
open scoped ProbabilityTheory BigOperators

noncomputable section

/-- Markov kernel obtained by retaining the original configuration pair, sampling
its complete coupled target trajectory, and reconstructing the two endpoint
configurations. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryCanonicalEndpointConfigurationPairKernel
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    Kernel (C.base.Configuration × C.base.Configuration)
      (C.base.Configuration × C.base.Configuration) :=
  ((Kernel.id ×ₖ
      C.independentPairHybridTargetTrajectoryKernel target
        (Fintype.card C.base.geometry.Edge)).map
    (C.independentPairHybridTargetTrajectoryCanonicalEndpointConfigurationPairMap
      target))

instance continuousCompactOriented_independentPairHybridTargetTrajectoryCanonicalEndpointConfigurationPairKernel_isMarkov
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    IsMarkovKernel
      (C.independentPairHybridTargetTrajectoryCanonicalEndpointConfigurationPairKernel
        target) := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryCanonicalEndpointConfigurationPairKernel
  exact Kernel.IsMarkovKernel.map _
    (continuous_compact_oriented_independentPairHybridTargetTrajectoryCanonicalEndpointConfigurationPairMap_continuous
      C target).measurable

/-- Every fiber of the global endpoint kernel is exactly the fixed-original-pair
endpoint coupling constructed previously. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryCanonicalEndpointConfigurationPairKernel_apply
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (z : C.base.Configuration × C.base.Configuration) :
    C.independentPairHybridTargetTrajectoryCanonicalEndpointConfigurationPairKernel
        target z =
      C.independentPairHybridTargetTrajectoryCanonicalEndpointConfigurationPairFiberMeasure
        target z := by
  let n := Fintype.card C.base.geometry.Edge
  have hEndpoint : Measurable
      (C.independentPairHybridTargetTrajectoryCanonicalEndpointConfigurationPairMap
        target) :=
    (continuous_compact_oriented_independentPairHybridTargetTrajectoryCanonicalEndpointConfigurationPairMap_continuous
      C target).measurable
  have hFiber : Measurable
      (C.independentPairHybridTargetTrajectoryCanonicalEndpointConfigurationPairFiberMap
        target z) :=
    (continuous_compact_oriented_independentPairHybridTargetTrajectoryCanonicalEndpointConfigurationPairFiberMap_continuous
      C target z).measurable
  ext s hs
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryCanonicalEndpointConfigurationPairKernel
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryCanonicalEndpointConfigurationPairFiberMeasure
  rw [Kernel.map_apply' _ hEndpoint z hs]
  rw [Kernel.id_prod_apply' _ z (hEndpoint hs)]
  rw [continuous_compact_oriented_independentPairHybridTargetTrajectoryKernel_apply_of_le
    C target n le_rfl z]
  rw [Measure.map_apply hFiber hs]
  rfl

/-- The first projection of the endpoint kernel is the exact one-link heat-bath
kernel applied to the first original configuration. -/
theorem continuous_compact_oriented_map_fst_independentPairHybridTargetTrajectoryCanonicalEndpointConfigurationPairKernel
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    (C.independentPairHybridTargetTrajectoryCanonicalEndpointConfigurationPairKernel
        target).map Prod.fst =
      (C.singleLinkHeatBathKernel target).comap Prod.fst measurable_fst := by
  ext z : 1
  rw [Kernel.map_apply _ measurable_fst z]
  rw [continuous_compact_oriented_independentPairHybridTargetTrajectoryCanonicalEndpointConfigurationPairKernel_apply]
  rw [continuous_compact_oriented_map_fst_independentPairHybridTargetTrajectoryCanonicalEndpointConfigurationPairFiberMeasure]
  rfl

/-- The second projection of the endpoint kernel is the exact one-link heat-bath
kernel applied to the second original configuration. -/
theorem continuous_compact_oriented_map_snd_independentPairHybridTargetTrajectoryCanonicalEndpointConfigurationPairKernel
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    (C.independentPairHybridTargetTrajectoryCanonicalEndpointConfigurationPairKernel
        target).map Prod.snd =
      (C.singleLinkHeatBathKernel target).comap Prod.snd measurable_snd := by
  ext z : 1
  rw [Kernel.map_apply _ measurable_snd z]
  rw [continuous_compact_oriented_independentPairHybridTargetTrajectoryCanonicalEndpointConfigurationPairKernel_apply]
  rw [continuous_compact_oriented_map_snd_independentPairHybridTargetTrajectoryCanonicalEndpointConfigurationPairFiberMeasure]
  rfl

/-- The global endpoint configuration-pair law is the endpoint reconstruction
kernel averaged over the independent Gibbs configuration pair. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryCanonicalEndpointConfigurationPairMeasure_eq_kernel_comp
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    C.independentPairHybridTargetTrajectoryCanonicalEndpointConfigurationPairMeasure
        target =
      C.independentPairHybridTargetTrajectoryCanonicalEndpointConfigurationPairKernel
          target ∘ₘ
        (C.gibbsMeasure.prod C.gibbsMeasure) := by
  have hEndpoint : Measurable
      (C.independentPairHybridTargetTrajectoryCanonicalEndpointConfigurationPairMap
        target) :=
    (continuous_compact_oriented_independentPairHybridTargetTrajectoryCanonicalEndpointConfigurationPairMap_continuous
      C target).measurable
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryCanonicalEndpointConfigurationPairMeasure
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryJointMeasure
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryCanonicalEndpointConfigurationPairKernel
  rw [Measure.compProd_eq_comp_prod]
  exact Measure.map_comp
    (C.gibbsMeasure.prod C.gibbsMeasure)
    (Kernel.id ×ₖ
      C.independentPairHybridTargetTrajectoryKernel target
        (Fintype.card C.base.geometry.Edge))
    hEndpoint

/-- The first global endpoint marginal is exactly the Wilson Gibbs measure. -/
theorem continuous_compact_oriented_map_fst_independentPairHybridTargetTrajectoryCanonicalEndpointConfigurationPairMeasure
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    Measure.map Prod.fst
        (C.independentPairHybridTargetTrajectoryCanonicalEndpointConfigurationPairMeasure
          target) =
      C.gibbsMeasure := by
  letI : IsProbabilityMeasure C.gibbsMeasure :=
    continuous_compact_oriented_gibbsMeasure_isProbabilityMeasure C
  let μ := C.gibbsMeasure.prod C.gibbsMeasure
  calc
    Measure.map Prod.fst
        (C.independentPairHybridTargetTrajectoryCanonicalEndpointConfigurationPairMeasure
          target) =
      ((C.independentPairHybridTargetTrajectoryCanonicalEndpointConfigurationPairKernel
          target).map Prod.fst) ∘ₘ μ := by
        rw [continuous_compact_oriented_independentPairHybridTargetTrajectoryCanonicalEndpointConfigurationPairMeasure_eq_kernel_comp]
        exact Measure.map_comp μ
          (C.independentPairHybridTargetTrajectoryCanonicalEndpointConfigurationPairKernel
            target) measurable_fst
    _ = ((C.singleLinkHeatBathKernel target).comap Prod.fst measurable_fst) ∘ₘ μ := by
      rw [continuous_compact_oriented_map_fst_independentPairHybridTargetTrajectoryCanonicalEndpointConfigurationPairKernel]
    _ = C.singleLinkHeatBathKernel target ∘ₘ Measure.map Prod.fst μ :=
      HybridTargetTrajectory.comap_comp_measure_eq_comp_map
        μ (C.singleLinkHeatBathKernel target) Prod.fst measurable_fst
    _ = C.singleLinkHeatBathKernel target ∘ₘ C.gibbsMeasure := by
      unfold μ
      rw [Measure.map_fst_prod, measure_univ, one_smul]
    _ = C.gibbsMeasure :=
      continuous_compact_oriented_singleLinkHeatBathKernel_stationary C target

/-- The second global endpoint marginal is exactly the Wilson Gibbs measure. -/
theorem continuous_compact_oriented_map_snd_independentPairHybridTargetTrajectoryCanonicalEndpointConfigurationPairMeasure
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    Measure.map Prod.snd
        (C.independentPairHybridTargetTrajectoryCanonicalEndpointConfigurationPairMeasure
          target) =
      C.gibbsMeasure := by
  letI : IsProbabilityMeasure C.gibbsMeasure :=
    continuous_compact_oriented_gibbsMeasure_isProbabilityMeasure C
  let μ := C.gibbsMeasure.prod C.gibbsMeasure
  calc
    Measure.map Prod.snd
        (C.independentPairHybridTargetTrajectoryCanonicalEndpointConfigurationPairMeasure
          target) =
      ((C.independentPairHybridTargetTrajectoryCanonicalEndpointConfigurationPairKernel
          target).map Prod.snd) ∘ₘ μ := by
        rw [continuous_compact_oriented_independentPairHybridTargetTrajectoryCanonicalEndpointConfigurationPairMeasure_eq_kernel_comp]
        exact Measure.map_comp μ
          (C.independentPairHybridTargetTrajectoryCanonicalEndpointConfigurationPairKernel
            target) measurable_snd
    _ = ((C.singleLinkHeatBathKernel target).comap Prod.snd measurable_snd) ∘ₘ μ := by
      rw [continuous_compact_oriented_map_snd_independentPairHybridTargetTrajectoryCanonicalEndpointConfigurationPairKernel]
    _ = C.singleLinkHeatBathKernel target ∘ₘ Measure.map Prod.snd μ :=
      HybridTargetTrajectory.comap_comp_measure_eq_comp_map
        μ (C.singleLinkHeatBathKernel target) Prod.snd measurable_snd
    _ = C.singleLinkHeatBathKernel target ∘ₘ C.gibbsMeasure := by
      unfold μ
      rw [Measure.map_snd_prod, measure_univ, one_smul]
    _ = C.gibbsMeasure :=
      continuous_compact_oriented_singleLinkHeatBathKernel_stationary C target

/-- The full trajectory endpoint law is therefore a Gibbs self-coupling. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryCanonicalEndpointConfigurationPairMeasure_gibbs_marginals
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    Measure.map Prod.fst
        (C.independentPairHybridTargetTrajectoryCanonicalEndpointConfigurationPairMeasure
          target) = C.gibbsMeasure ∧
      Measure.map Prod.snd
        (C.independentPairHybridTargetTrajectoryCanonicalEndpointConfigurationPairMeasure
          target) = C.gibbsMeasure := by
  exact ⟨
    continuous_compact_oriented_map_fst_independentPairHybridTargetTrajectoryCanonicalEndpointConfigurationPairMeasure
      C target,
    continuous_compact_oriented_map_snd_independentPairHybridTargetTrajectoryCanonicalEndpointConfigurationPairMeasure
      C target⟩

/-- The new full-trajectory endpoint coupling and the native conditional-pair
reference law have the same first marginal. -/
theorem continuous_compact_oriented_map_fst_independentPairHybridTargetTrajectoryCanonicalEndpointConfigurationPairMeasure_eq_native
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    Measure.map Prod.fst
        (C.independentPairHybridTargetTrajectoryCanonicalEndpointConfigurationPairMeasure
          target) =
      Measure.map Prod.fst
        (C.singleLinkHeatBathIndependentPairMeasure target) := by
  rw [continuous_compact_oriented_map_fst_independentPairHybridTargetTrajectoryCanonicalEndpointConfigurationPairMeasure,
    continuous_compact_oriented_map_fst_singleLinkHeatBathIndependentPairMeasure]

/-- The new full-trajectory endpoint coupling and the native conditional-pair
reference law have the same second marginal. -/
theorem continuous_compact_oriented_map_snd_independentPairHybridTargetTrajectoryCanonicalEndpointConfigurationPairMeasure_eq_native
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    Measure.map Prod.snd
        (C.independentPairHybridTargetTrajectoryCanonicalEndpointConfigurationPairMeasure
          target) =
      Measure.map Prod.snd
        (C.singleLinkHeatBathIndependentPairMeasure target) := by
  rw [continuous_compact_oriented_map_snd_independentPairHybridTargetTrajectoryCanonicalEndpointConfigurationPairMeasure,
    continuous_compact_oriented_map_snd_singleLinkHeatBathIndependentPairMeasure]

end

end MathlibAnalytic
end MGAP4D
