import MGAP4D.MathlibAnalytic.RealIntegralWeightedProbabilityNormalization
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Compact-domain continuity of the existing weighted probability normalization

The parameter space is an arbitrary topological space. Compactness belongs
only to the integration domain, so the compact-support integral theorem is
used instead of a parameter theorem requiring first countability or local
compactness. The normalized law is the existing realIntegralWeightedProbabilityMeasure.
Its actual positive mass is retained; no uniform mass floor is assumed.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory Set

noncomputable section

/-- Joint continuity on a compact integration domain gives continuity of the
integral, without any countability assumption on the parameter space. -/
theorem continuous_integral_compact_domain
    {P X : Type*} [TopologicalSpace P] [TopologicalSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] [CompactSpace X]
    (mu : Measure X) [IsFiniteMeasure mu] (f : P → X → ℝ)
    (hf : Continuous (Function.uncurry f)) :
    Continuous (fun p => ∫ x, f p x ∂mu) := by
  apply continuousOn_univ.mp
  exact continuousOn_integral_of_compact_support
    (μ := mu) (s := Set.univ) (k := Set.univ)
    isCompact_univ hf.continuousOn
    (by intro p x hp hx; exact (hx (Set.mem_univ x)).elim)

/-- The density normalized by its actual integral is jointly continuous.
Positivity is used pointwise, not replaced by a uniform lower-bound input. -/
theorem realIntegralWeightedDensity_joint_continuous
    {P X : Type*} [TopologicalSpace P] [TopologicalSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] [CompactSpace X]
    (mu : Measure X) [IsFiniteMeasure mu] (w : P → X → ℝ)
    (hw : Continuous (Function.uncurry w))
    (hMassPos : ∀ p, 0 < ∫ x, w p x ∂mu) :
    Continuous (fun q : P × X => (∫ x, w q.1 x ∂mu)⁻¹ * w q.1 q.2) := by
  have hMass := continuous_integral_compact_domain mu w hw
  exact ((hMass.inv₀ (fun p => (hMassPos p).ne')).comp continuous_fst).mul hw

/-- Expectations of jointly continuous observables under the existing
normalized weighted law depend continuously on the parameter. -/
theorem realIntegralWeightedProbabilityMeasure_integral_continuous
    {P X : Type*} [TopologicalSpace P] [TopologicalSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] [CompactSpace X]
    (mu : Measure X) [IsFiniteMeasure mu] (w f : P → X → ℝ)
    (hw : Continuous (Function.uncurry w))
    (hf : Continuous (Function.uncurry f))
    (hwNonneg : ∀ p x, 0 ≤ w p x)
    (hMassPos : ∀ p, 0 < ∫ x, w p x ∂mu) :
    Continuous (fun p => ∫ x, f p x ∂realIntegralWeightedProbabilityMeasure mu (w p)) := by
  have hMass := continuous_integral_compact_domain mu w hw
  have hNumerator : Continuous (fun p => ∫ x, w p x * f p x ∂mu) :=
    continuous_integral_compact_domain mu (fun p x => w p x * f p x) (hw.mul hf)
  have hNormalized : Continuous
      (fun p => (∫ x, w p x ∂mu)⁻¹ * ∫ x, w p x * f p x ∂mu) :=
    (hMass.inv₀ (fun p => (hMassPos p).ne')).mul hNumerator
  have hIntegral (p : P) : Integrable (w p) mu := by
    have hSlice : Continuous (w p) :=
      hw.comp (continuous_const.prodMk continuous_id)
    exact integrableOn_univ.mp
      (ContinuousOn.integrableOn_compact' isCompact_univ MeasurableSet.univ
        hSlice.continuousOn)
  have heq :
      (fun p => (∫ x, w p x ∂mu)⁻¹ * ∫ x, w p x * f p x ∂mu) =
      (fun p => ∫ x, f p x ∂realIntegralWeightedProbabilityMeasure mu (w p)) := by
    funext p
    exact (realIntegralWeightedProbabilityMeasure_integral mu (w p) (f p)
      (hIntegral p) (Filter.Eventually.of_forall (hwNonneg p)) (hMassPos p)).symm
  exact Eq.mp (congrArg (fun g : P → ℝ => Continuous g) heq) hNormalized

end

end MGAP4D.MathlibAnalytic
