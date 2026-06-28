import MGAP4D.MathlibAnalytic.CompactOrientedGaugeWilsonSingleLink
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.MeasureTheory.Integral.CompactlySupported

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set

noncomputable section

/-- Varying one physical link while holding all other links fixed is a
continuous map from the compact gauge group into configuration space. -/
theorem continuous_compact_oriented_replaceLink
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A : C.base.Configuration)
    (target : C.base.geometry.Edge) :
    Continuous (fun g : C.base.Gauge =>
      C.base.replaceLink A target g) := by
  apply continuous_pi
  intro e
  by_cases h : e = target
  · subst e
    simpa [CompactOrientedGaugeWilsonSystem.replaceLink] using
      (continuous_id' : Continuous (fun g : C.base.Gauge => g))
  · simpa [CompactOrientedGaugeWilsonSystem.replaceLink, h] using
      (continuous_const : Continuous
        (fun _g : C.base.Gauge => A e))

/-- The one-link Wilson Gibbs exponent is continuous in the inserted compact
group variable. -/
theorem continuous_compact_oriented_singleLinkGibbsExponent
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A : C.base.Configuration)
    (target : C.base.geometry.Edge) :
    Continuous (fun g : C.base.Gauge =>
      C.base.gibbsExponent (C.base.replaceLink A target g)) :=
  (continuous_compact_oriented_gibbsExponent C).comp
    (continuous_compact_oriented_replaceLink C A target)

/-- The exact one-link Boltzmann factor for a compact oriented Wilson system. -/
def ContinuousCompactOrientedGaugeWilsonSystem.singleLinkBoltzmannFactor
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (g : C.base.Gauge) : ℝ :=
  Real.exp (C.base.gibbsExponent
    (C.base.replaceLink A target g))

/-- The one-link Boltzmann factor is continuous. -/
theorem continuous_compact_oriented_singleLinkBoltzmannFactor
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A : C.base.Configuration)
    (target : C.base.geometry.Edge) :
    Continuous (C.singleLinkBoltzmannFactor A target) :=
  Real.continuous_exp.comp
    (continuous_compact_oriented_singleLinkGibbsExponent C A target)

/-- The one-link Boltzmann factor is automatically Haar integrable by
compactness. -/
theorem continuous_compact_oriented_singleLinkBoltzmannIntegrable
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A : C.base.Configuration)
    (target : C.base.geometry.Edge) :
    Integrable (C.singleLinkBoltzmannFactor A target)
      (normalizedCompactHaar C.base.Gauge) := by
  exact
    (continuous_compact_oriented_singleLinkBoltzmannFactor C A target).
      integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)

/-- Exact one-link conditional partition function with respect to normalized
Haar measure. -/
def ContinuousCompactOrientedGaugeWilsonSystem.singleLinkPartitionFunction
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A : C.base.Configuration)
    (target : C.base.geometry.Edge) : ℝ :=
  ∫ g, C.singleLinkBoltzmannFactor A target g
    ∂normalizedCompactHaar C.base.Gauge

/-- The compact one-link conditional partition function is strictly positive. -/
theorem continuous_compact_oriented_singleLinkPartitionFunction_pos
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A : C.base.Configuration)
    (target : C.base.geometry.Edge) :
    0 < C.singleLinkPartitionFunction A target := by
  unfold ContinuousCompactOrientedGaugeWilsonSystem.singleLinkPartitionFunction
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkBoltzmannFactor
  exact integral_exp_pos
    (continuous_compact_oriented_singleLinkBoltzmannIntegrable C A target)

/-- Exact Haar conditional law for resampling one physical positive link. -/
def ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalMeasure
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A : C.base.Configuration)
    (target : C.base.geometry.Edge) : Measure C.base.Gauge :=
  (normalizedCompactHaar C.base.Gauge).tilted
    (fun g => C.base.gibbsExponent
      (C.base.replaceLink A target g))

/-- Every exact compact one-link conditional law is a probability measure. -/
theorem continuous_compact_oriented_singleLinkConditionalMeasure_isProbabilityMeasure
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A : C.base.Configuration)
    (target : C.base.geometry.Edge) :
    IsProbabilityMeasure
      (C.singleLinkConditionalMeasure A target) := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalMeasure
  exact MeasureTheory.isProbabilityMeasure_tilted
    (continuous_compact_oriented_singleLinkBoltzmannIntegrable C A target)

/-- Density formula for the exact compact one-link conditional law. -/
theorem continuous_compact_oriented_singleLinkConditionalMeasure_eq_withDensity
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A : C.base.Configuration)
    (target : C.base.geometry.Edge) :
    C.singleLinkConditionalMeasure A target =
      (normalizedCompactHaar C.base.Gauge).withDensity
        (fun g => ENNReal.ofReal
          (C.singleLinkBoltzmannFactor A target g /
            C.singleLinkPartitionFunction A target)) := by
  rfl

end

end MathlibAnalytic
end MGAP4D
