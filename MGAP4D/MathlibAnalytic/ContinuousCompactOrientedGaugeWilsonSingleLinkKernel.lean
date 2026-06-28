import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonSingleLinkFiberInvariance
import Mathlib.Probability.Kernel.WithDensity
import Mathlib.MeasureTheory.Integral.Prod

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

/-- Joint continuity of physical-link replacement in the background
configuration and inserted compact-group value. -/
theorem continuous_compact_oriented_replaceLink_uncurry
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    Continuous (fun z : C.base.Configuration × C.base.Gauge =>
      C.base.replaceLink z.1 target z.2) := by
  apply continuous_pi
  intro e
  by_cases h : e = target
  · subst e
    simp [CompactOrientedGaugeWilsonSystem.replaceLink]
    fun_prop
  · simp [CompactOrientedGaugeWilsonSystem.replaceLink, h]
    fun_prop

/-- The exact one-link Boltzmann factor is jointly continuous in the
background configuration and inserted link value. -/
theorem continuous_compact_oriented_singleLinkBoltzmannFactor_uncurry
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    Continuous (Function.uncurry
      (fun A : C.base.Configuration =>
        C.singleLinkBoltzmannFactor A target)) := by
  unfold Function.uncurry
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkBoltzmannFactor
  exact Real.continuous_exp.comp
    ((continuous_compact_oriented_gibbsExponent C).comp
      (continuous_compact_oriented_replaceLink_uncurry C target))

/-- The one-link partition function is measurable in the background
configuration. -/
theorem measurable_compact_oriented_singleLinkPartitionFunction
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    Measurable (fun A : C.base.Configuration =>
      C.singleLinkPartitionFunction A target) := by
  have hStrong : StronglyMeasurable
      (Function.uncurry
        (fun A : C.base.Configuration =>
          C.singleLinkBoltzmannFactor A target)) :=
    (continuous_compact_oriented_singleLinkBoltzmannFactor_uncurry
      C target).stronglyMeasurable
  simpa [ContinuousCompactOrientedGaugeWilsonSystem.singleLinkPartitionFunction]
    using hStrong.integral_prod_right.measurable

/-- Normalized one-link Haar density as a jointly measurable function. -/
def ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalDensity
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (A : C.base.Configuration)
    (g : C.base.Gauge) : ℝ≥0∞ :=
  ENNReal.ofReal
    (C.singleLinkBoltzmannFactor A target g /
      C.singleLinkPartitionFunction A target)

/-- The normalized one-link Haar density is jointly measurable. -/
theorem measurable_compact_oriented_singleLinkConditionalDensity_uncurry
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    Measurable (Function.uncurry
      (C.singleLinkConditionalDensity target)) := by
  unfold Function.uncurry
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalDensity
  apply ENNReal.measurable_ofReal.comp
  exact
    (continuous_compact_oriented_singleLinkBoltzmannFactor_uncurry
      C target).measurable.div
      ((measurable_compact_oriented_singleLinkPartitionFunction C target).
        comp measurable_fst)

/-- Markov kernel of exact Haar resampling at one physical positive link. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalKernel
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    Kernel C.base.Configuration C.base.Gauge :=
  Kernel.withDensity
    (Kernel.const C.base.Configuration
      (normalizedCompactHaar C.base.Gauge))
    (C.singleLinkConditionalDensity target)

/-- Pointwise identification of the kernel with the previously constructed
exact conditional measure. -/
theorem continuous_compact_oriented_singleLinkConditionalKernel_apply
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (A : C.base.Configuration) :
    C.singleLinkConditionalKernel target A =
      C.singleLinkConditionalMeasure A target := by
  rw [ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalKernel,
    Kernel.withDensity_apply _
      (measurable_compact_oriented_singleLinkConditionalDensity_uncurry
        C target),
    Kernel.const_apply]
  exact
    (continuous_compact_oriented_singleLinkConditionalMeasure_eq_withDensity
      C A target).symm

/-- Exact one-link Haar resampling is a Markov kernel. -/
instance continuousCompactOriented_singleLinkConditionalKernel_isMarkov
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    IsMarkovKernel (C.singleLinkConditionalKernel target) :=
  ⟨fun A => by
    rw [continuous_compact_oriented_singleLinkConditionalKernel_apply]
    exact
      continuous_compact_oriented_singleLinkConditionalMeasure_isProbabilityMeasure
        C A target⟩

end

end MathlibAnalytic
end MGAP4D
