import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonConditionalOverlapTransportEnergyBCF
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.Probability.Kernel.WithDensity
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

noncomputable section

/-- The common one-link conditional density, now indexed measurably by a pair
of full background configurations. -/
def ContinuousCompactOrientedGaugeWilsonSystem.configurationPairConditionalOverlapDensity
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (z : C.base.Configuration × C.base.Configuration)
    (g : C.base.Gauge) : ℝ≥0∞ :=
  C.singleLinkConditionalOverlapDensity z.1 z.2 target g

/-- Left residual one-link density indexed by a background pair. -/
def ContinuousCompactOrientedGaugeWilsonSystem.configurationPairConditionalLeftResidualDensity
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (z : C.base.Configuration × C.base.Configuration)
    (g : C.base.Gauge) : ℝ≥0∞ :=
  C.singleLinkConditionalLeftResidualDensity z.1 z.2 target g

/-- Right residual one-link density indexed by a background pair. -/
def ContinuousCompactOrientedGaugeWilsonSystem.configurationPairConditionalRightResidualDensity
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (z : C.base.Configuration × C.base.Configuration)
    (g : C.base.Gauge) : ℝ≥0∞ :=
  C.singleLinkConditionalRightResidualDensity z.1 z.2 target g

/-- The background-pair overlap density is jointly measurable in both
backgrounds and the inserted target-link value. -/
theorem measurable_compact_oriented_configurationPairConditionalOverlapDensity_uncurry
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    Measurable (Function.uncurry
      (C.configurationPairConditionalOverlapDensity target)) := by
  have hLeftPair : Measurable
      (fun w : (C.base.Configuration × C.base.Configuration) × C.base.Gauge =>
        (w.1.1, w.2)) :=
    (measurable_fst.comp measurable_fst).prodMk measurable_snd
  have hRightPair : Measurable
      (fun w : (C.base.Configuration × C.base.Configuration) × C.base.Gauge =>
        (w.1.2, w.2)) :=
    (measurable_snd.comp measurable_fst).prodMk measurable_snd
  have hLeft :=
    (measurable_compact_oriented_singleLinkConditionalDensity_uncurry
      C target).comp hLeftPair
  have hRight :=
    (measurable_compact_oriented_singleLinkConditionalDensity_uncurry
      C target).comp hRightPair
  simpa [Function.uncurry,
    ContinuousCompactOrientedGaugeWilsonSystem.configurationPairConditionalOverlapDensity,
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalOverlapDensity]
    using hLeft.min hRight

/-- The left residual density is jointly measurable. -/
theorem measurable_compact_oriented_configurationPairConditionalLeftResidualDensity_uncurry
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    Measurable (Function.uncurry
      (C.configurationPairConditionalLeftResidualDensity target)) := by
  have hLeftPair : Measurable
      (fun w : (C.base.Configuration × C.base.Configuration) × C.base.Gauge =>
        (w.1.1, w.2)) :=
    (measurable_fst.comp measurable_fst).prodMk measurable_snd
  have hLeft :=
    (measurable_compact_oriented_singleLinkConditionalDensity_uncurry
      C target).comp hLeftPair
  have hOverlap :=
    measurable_compact_oriented_configurationPairConditionalOverlapDensity_uncurry
      C target
  simpa [Function.uncurry,
    ContinuousCompactOrientedGaugeWilsonSystem.configurationPairConditionalLeftResidualDensity,
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalLeftResidualDensity,
    ContinuousCompactOrientedGaugeWilsonSystem.configurationPairConditionalOverlapDensity]
    using hLeft.sub hOverlap

/-- The right residual density is jointly measurable. -/
theorem measurable_compact_oriented_configurationPairConditionalRightResidualDensity_uncurry
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    Measurable (Function.uncurry
      (C.configurationPairConditionalRightResidualDensity target)) := by
  have hRightPair : Measurable
      (fun w : (C.base.Configuration × C.base.Configuration) × C.base.Gauge =>
        (w.1.2, w.2)) :=
    (measurable_snd.comp measurable_fst).prodMk measurable_snd
  have hRight :=
    (measurable_compact_oriented_singleLinkConditionalDensity_uncurry
      C target).comp hRightPair
  have hOverlap :=
    measurable_compact_oriented_configurationPairConditionalOverlapDensity_uncurry
      C target
  simpa [Function.uncurry,
    ContinuousCompactOrientedGaugeWilsonSystem.configurationPairConditionalRightResidualDensity,
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalRightResidualDensity,
    ContinuousCompactOrientedGaugeWilsonSystem.configurationPairConditionalOverlapDensity]
    using hRight.sub hOverlap

/-- Measurable kernel of common overlap measures for pairs of backgrounds. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonSystem.configurationPairConditionalOverlapKernel
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    Kernel (C.base.Configuration × C.base.Configuration) C.base.Gauge :=
  Kernel.withDensity
    (Kernel.const (C.base.Configuration × C.base.Configuration)
      (normalizedCompactHaar C.base.Gauge))
    (C.configurationPairConditionalOverlapDensity target)

/-- Measurable kernel of left residual measures. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonSystem.configurationPairConditionalLeftResidualKernel
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    Kernel (C.base.Configuration × C.base.Configuration) C.base.Gauge :=
  Kernel.withDensity
    (Kernel.const (C.base.Configuration × C.base.Configuration)
      (normalizedCompactHaar C.base.Gauge))
    (C.configurationPairConditionalLeftResidualDensity target)

/-- Measurable kernel of right residual measures. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonSystem.configurationPairConditionalRightResidualKernel
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    Kernel (C.base.Configuration × C.base.Configuration) C.base.Gauge :=
  Kernel.withDensity
    (Kernel.const (C.base.Configuration × C.base.Configuration)
      (normalizedCompactHaar C.base.Gauge))
    (C.configurationPairConditionalRightResidualDensity target)

/-- Every overlap-kernel fiber is the fixed overlap measure constructed earlier. -/
theorem continuous_compact_oriented_configurationPairConditionalOverlapKernel_apply
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (z : C.base.Configuration × C.base.Configuration) :
    C.configurationPairConditionalOverlapKernel target z =
      C.singleLinkConditionalOverlapMeasure z.1 z.2 target := by
  rw [ContinuousCompactOrientedGaugeWilsonSystem.configurationPairConditionalOverlapKernel,
    Kernel.withDensity_apply _
      (measurable_compact_oriented_configurationPairConditionalOverlapDensity_uncurry
        C target),
    Kernel.const_apply]
  rfl

/-- Every left-residual-kernel fiber is the fixed left residual measure. -/
theorem continuous_compact_oriented_configurationPairConditionalLeftResidualKernel_apply
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (z : C.base.Configuration × C.base.Configuration) :
    C.configurationPairConditionalLeftResidualKernel target z =
      C.singleLinkConditionalLeftResidualMeasure z.1 z.2 target := by
  rw [ContinuousCompactOrientedGaugeWilsonSystem.configurationPairConditionalLeftResidualKernel,
    Kernel.withDensity_apply _
      (measurable_compact_oriented_configurationPairConditionalLeftResidualDensity_uncurry
        C target),
    Kernel.const_apply]
  rfl

/-- Every right-residual-kernel fiber is the fixed right residual measure. -/
theorem continuous_compact_oriented_configurationPairConditionalRightResidualKernel_apply
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (z : C.base.Configuration × C.base.Configuration) :
    C.configurationPairConditionalRightResidualKernel target z =
      C.singleLinkConditionalRightResidualMeasure z.1 z.2 target := by
  rw [ContinuousCompactOrientedGaugeWilsonSystem.configurationPairConditionalRightResidualKernel,
    Kernel.withDensity_apply _
      (measurable_compact_oriented_configurationPairConditionalRightResidualDensity_uncurry
        C target),
    Kernel.const_apply]
  rfl

/-- The overlap kernel is uniformly finite, with total mass at most one. -/
instance continuousCompactOriented_configurationPairConditionalOverlapKernel_isFinite
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    IsFiniteKernel (C.configurationPairConditionalOverlapKernel target) := by
  refine ⟨⟨1, ENNReal.one_lt_top, fun z => ?_⟩⟩
  rw [continuous_compact_oriented_configurationPairConditionalOverlapKernel_apply]
  letI : IsProbabilityMeasure (C.singleLinkConditionalMeasure z.1 target) :=
    continuous_compact_oriented_singleLinkConditionalMeasure_isProbabilityMeasure
      C z.1 target
  have hle : C.singleLinkConditionalOverlapMeasure z.1 z.2 target ≤
      C.singleLinkConditionalMeasure z.1 target := by
    rw [← continuous_compact_oriented_singleLinkConditionalOverlapMeasure_add_leftResidual
      C z.1 z.2 target]
    exact Measure.le_add_right le_rfl
  exact (hle univ).trans_eq measure_univ

/-- The left residual kernel is uniformly finite, with total mass at most one. -/
instance continuousCompactOriented_configurationPairConditionalLeftResidualKernel_isFinite
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    IsFiniteKernel (C.configurationPairConditionalLeftResidualKernel target) := by
  refine ⟨⟨1, ENNReal.one_lt_top, fun z => ?_⟩⟩
  rw [continuous_compact_oriented_configurationPairConditionalLeftResidualKernel_apply]
  letI : IsProbabilityMeasure (C.singleLinkConditionalMeasure z.1 target) :=
    continuous_compact_oriented_singleLinkConditionalMeasure_isProbabilityMeasure
      C z.1 target
  have hle : C.singleLinkConditionalLeftResidualMeasure z.1 z.2 target ≤
      C.singleLinkConditionalMeasure z.1 target := by
    rw [← continuous_compact_oriented_singleLinkConditionalOverlapMeasure_add_leftResidual
      C z.1 z.2 target]
    exact Measure.le_add_left le_rfl
  exact (hle univ).trans_eq measure_univ

/-- The right residual kernel is uniformly finite, with total mass at most one. -/
instance continuousCompactOriented_configurationPairConditionalRightResidualKernel_isFinite
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    IsFiniteKernel (C.configurationPairConditionalRightResidualKernel target) := by
  refine ⟨⟨1, ENNReal.one_lt_top, fun z => ?_⟩⟩
  rw [continuous_compact_oriented_configurationPairConditionalRightResidualKernel_apply]
  letI : IsProbabilityMeasure (C.singleLinkConditionalMeasure z.2 target) :=
    continuous_compact_oriented_singleLinkConditionalMeasure_isProbabilityMeasure
      C z.2 target
  have hle : C.singleLinkConditionalRightResidualMeasure z.1 z.2 target ≤
      C.singleLinkConditionalMeasure z.2 target := by
    rw [← continuous_compact_oriented_singleLinkConditionalOverlapMeasure_add_rightResidual
      C z.1 z.2 target]
    exact Measure.le_add_left le_rfl
  exact (hle univ).trans_eq measure_univ

/-- The unmatched mass as a measurable function of the two backgrounds. -/
def ContinuousCompactOrientedGaugeWilsonSystem.configurationPairConditionalResidualMass
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (z : C.base.Configuration × C.base.Configuration) : ℝ≥0∞ :=
  C.singleLinkConditionalResidualMass z.1 z.2 target

/-- The unmatched mass is measurable in the background pair. -/
theorem continuous_compact_oriented_configurationPairConditionalResidualMass_measurable
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    Measurable (C.configurationPairConditionalResidualMass target) := by
  have hKernel :=
    (C.configurationPairConditionalLeftResidualKernel target).measurable_coe
      MeasurableSet.univ
  simpa [ContinuousCompactOrientedGaugeWilsonSystem.configurationPairConditionalResidualMass,
    continuous_compact_oriented_configurationPairConditionalLeftResidualKernel_apply]
    using hKernel

/-- Measurable normalization weight for the residual product.  The zero-mass
fiber is assigned weight zero, matching the fixed coupling definition. -/
def ContinuousCompactOrientedGaugeWilsonSystem.configurationPairConditionalResidualWeight
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (z : C.base.Configuration × C.base.Configuration) : ℝ≥0∞ :=
  if C.configurationPairConditionalResidualMass target z = 0 then 0
  else (C.configurationPairConditionalResidualMass target z)⁻¹

/-- The residual normalization weight is measurable. -/
theorem continuous_compact_oriented_configurationPairConditionalResidualWeight_measurable
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    Measurable (C.configurationPairConditionalResidualWeight target) := by
  let δ := C.configurationPairConditionalResidualMass target
  have hδ : Measurable δ :=
    continuous_compact_oriented_configurationPairConditionalResidualMass_measurable
      C target
  have hZero : MeasurableSet {z | δ z = 0} := by
    exact hδ (measurableSet_singleton 0)
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.configurationPairConditionalResidualWeight
  exact Measurable.ite hZero measurable_const hδ.inv

/-- Product kernel of the two unnormalized residual measures. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonSystem.configurationPairConditionalResidualProductKernel
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    Kernel (C.base.Configuration × C.base.Configuration)
      (C.base.Gauge × C.base.Gauge) :=
  C.configurationPairConditionalLeftResidualKernel target ×ₖ
    C.configurationPairConditionalRightResidualKernel target

/-- The residual-product fiber is the product of the two fixed residual measures. -/
theorem continuous_compact_oriented_configurationPairConditionalResidualProductKernel_apply
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (z : C.base.Configuration × C.base.Configuration) :
    C.configurationPairConditionalResidualProductKernel target z =
      (C.singleLinkConditionalLeftResidualMeasure z.1 z.2 target).prod
        (C.singleLinkConditionalRightResidualMeasure z.1 z.2 target) := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.configurationPairConditionalResidualProductKernel
  rw [Kernel.prod_apply,
    continuous_compact_oriented_configurationPairConditionalLeftResidualKernel_apply,
    continuous_compact_oriented_configurationPairConditionalRightResidualKernel_apply]

/-- The residual-product kernel is uniformly finite. -/
instance continuousCompactOriented_configurationPairConditionalResidualProductKernel_isFinite
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    IsFiniteKernel (C.configurationPairConditionalResidualProductKernel target) := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.configurationPairConditionalResidualProductKernel
  infer_instance

/-- The residual product, normalized fiberwise by the common unmatched mass. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonSystem.configurationPairConditionalNormalizedResidualProductKernel
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    Kernel (C.base.Configuration × C.base.Configuration)
      (C.base.Gauge × C.base.Gauge) :=
  Kernel.withDensity
    (C.configurationPairConditionalResidualProductKernel target)
    (fun z (_ : C.base.Gauge × C.base.Gauge) =>
      C.configurationPairConditionalResidualWeight target z)

/-- Pointwise, normalized residual-product fibers have exactly the branchwise
form used in the fixed overlap coupling. -/
theorem continuous_compact_oriented_configurationPairConditionalNormalizedResidualProductKernel_apply
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (z : C.base.Configuration × C.base.Configuration) :
    C.configurationPairConditionalNormalizedResidualProductKernel target z =
      if C.singleLinkConditionalResidualMass z.1 z.2 target = 0 then
        (0 : Measure (C.base.Gauge × C.base.Gauge))
      else
        ((C.singleLinkConditionalResidualMass z.1 z.2 target)⁻¹ : ℝ≥0∞) •
          ((C.singleLinkConditionalLeftResidualMeasure z.1 z.2 target).prod
            (C.singleLinkConditionalRightResidualMeasure z.1 z.2 target)) := by
  have hWeightUncurry : Measurable (Function.uncurry
      (fun z : C.base.Configuration × C.base.Configuration =>
        fun _ : C.base.Gauge × C.base.Gauge =>
          C.configurationPairConditionalResidualWeight target z)) := by
    simpa [Function.uncurry] using
      (continuous_compact_oriented_configurationPairConditionalResidualWeight_measurable
        C target).comp measurable_fst
  rw [ContinuousCompactOrientedGaugeWilsonSystem.configurationPairConditionalNormalizedResidualProductKernel,
    Kernel.withDensity_apply _ hWeightUncurry,
    continuous_compact_oriented_configurationPairConditionalResidualProductKernel_apply,
    MeasureTheory.withDensity_const]
  by_cases hδ : C.singleLinkConditionalResidualMass z.1 z.2 target = 0
  · simp [ContinuousCompactOrientedGaugeWilsonSystem.configurationPairConditionalResidualWeight,
      ContinuousCompactOrientedGaugeWilsonSystem.configurationPairConditionalResidualMass,
      hδ]
  · simp [ContinuousCompactOrientedGaugeWilsonSystem.configurationPairConditionalResidualWeight,
      ContinuousCompactOrientedGaugeWilsonSystem.configurationPairConditionalResidualMass,
      hδ]

/-- Diagonal pushforward kernel of the common overlap measure. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonSystem.configurationPairConditionalDiagonalOverlapKernel
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    Kernel (C.base.Configuration × C.base.Configuration)
      (C.base.Gauge × C.base.Gauge) :=
  (C.configurationPairConditionalOverlapKernel target).map
    (fun g : C.base.Gauge => (g, g))

/-- Every diagonal-overlap fiber is the diagonal pushforward of the fixed
common measure. -/
theorem continuous_compact_oriented_configurationPairConditionalDiagonalOverlapKernel_apply
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (z : C.base.Configuration × C.base.Configuration) :
    C.configurationPairConditionalDiagonalOverlapKernel target z =
      Measure.map (fun g : C.base.Gauge => (g, g))
        (C.singleLinkConditionalOverlapMeasure z.1 z.2 target) := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.configurationPairConditionalDiagonalOverlapKernel
  calc
    ((C.configurationPairConditionalOverlapKernel target).map
        (fun g : C.base.Gauge => (g, g))) z =
      Measure.map (fun g : C.base.Gauge => (g, g))
        (C.configurationPairConditionalOverlapKernel target z) := by
          exact Kernel.map_apply _ (measurable_id.prodMk measurable_id) z
    _ = Measure.map (fun g : C.base.Gauge => (g, g))
        (C.singleLinkConditionalOverlapMeasure z.1 z.2 target) := by
          rw [continuous_compact_oriented_configurationPairConditionalOverlapKernel_apply]

/-- Measurable exact overlap-coupling kernel indexed by a pair of full
background configurations. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonSystem.configurationPairConditionalOverlapCouplingKernel
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    Kernel (C.base.Configuration × C.base.Configuration)
      (C.base.Gauge × C.base.Gauge) :=
  C.configurationPairConditionalDiagonalOverlapKernel target +
    C.configurationPairConditionalNormalizedResidualProductKernel target

/-- Every coupling-kernel fiber is exactly the fixed overlap coupling from the
preceding construction. -/
theorem continuous_compact_oriented_configurationPairConditionalOverlapCouplingKernel_apply
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (z : C.base.Configuration × C.base.Configuration) :
    C.configurationPairConditionalOverlapCouplingKernel target z =
      C.singleLinkConditionalOverlapCouplingMeasure z.1 z.2 target := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.configurationPairConditionalOverlapCouplingKernel
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalOverlapCouplingMeasure
  rw [Kernel.add_apply,
    continuous_compact_oriented_configurationPairConditionalDiagonalOverlapKernel_apply,
    continuous_compact_oriented_configurationPairConditionalNormalizedResidualProductKernel_apply]

/-- The measurable configuration-pair indexed overlap coupling is Markov. -/
instance continuousCompactOriented_configurationPairConditionalOverlapCouplingKernel_isMarkov
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    IsMarkovKernel (C.configurationPairConditionalOverlapCouplingKernel target) :=
  ⟨fun z => by
    rw [continuous_compact_oriented_configurationPairConditionalOverlapCouplingKernel_apply]
    exact
      continuousCompactOriented_singleLinkConditionalOverlapCouplingMeasure_isProbability
        C z.1 z.2 target⟩

/-- Fiberwise first marginal is the exact conditional law at the first
background. -/
theorem continuous_compact_oriented_map_fst_configurationPairConditionalOverlapCouplingKernel_apply
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (z : C.base.Configuration × C.base.Configuration) :
    Measure.map Prod.fst
        (C.configurationPairConditionalOverlapCouplingKernel target z) =
      C.singleLinkConditionalMeasure z.1 target := by
  rw [continuous_compact_oriented_configurationPairConditionalOverlapCouplingKernel_apply]
  exact
    continuous_compact_oriented_map_fst_singleLinkConditionalOverlapCouplingMeasure
      C z.1 z.2 target

/-- Fiberwise second marginal is the exact conditional law at the second
background. -/
theorem continuous_compact_oriented_map_snd_configurationPairConditionalOverlapCouplingKernel_apply
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (z : C.base.Configuration × C.base.Configuration) :
    Measure.map Prod.snd
        (C.configurationPairConditionalOverlapCouplingKernel target z) =
      C.singleLinkConditionalMeasure z.2 target := by
  rw [continuous_compact_oriented_configurationPairConditionalOverlapCouplingKernel_apply]
  exact
    continuous_compact_oriented_map_snd_singleLinkConditionalOverlapCouplingMeasure
      C z.1 z.2 target

end

end MathlibAnalytic
end MGAP4D