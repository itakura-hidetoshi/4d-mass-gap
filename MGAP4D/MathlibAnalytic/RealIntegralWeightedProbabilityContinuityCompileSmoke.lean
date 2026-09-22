import MGAP4D.MathlibAnalytic.RealIntegralWeightedProbabilityContinuity
import Mathlib.MeasureTheory.Integral.Bochner.Set

namespace MGAP4D.MathlibAnalytic

open MeasureTheory Set

noncomputable section

-- No first-countability, metrizability, or local compactness of P is assumed.
example {P X : Type*} [TopologicalSpace P] [TopologicalSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] [CompactSpace X]
    (mu : Measure X) [IsFiniteMeasure mu] (f : P → X → ℝ)
    (hf : Continuous (Function.uncurry f)) :
    Continuous (fun p => ∫ x, f p x ∂mu) :=
  continuous_integral_compact_domain mu f hf

-- Use the literal existing normalized probability measure, not a new law.
example {P X : Type*} [TopologicalSpace P] [TopologicalSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] [CompactSpace X]
    (mu : Measure X) [IsFiniteMeasure mu] (w f : P → X → ℝ)
    (hw : Continuous (Function.uncurry w))
    (hf : Continuous (Function.uncurry f))
    (hwNonneg : ∀ p x, 0 ≤ w p x)
    (hMassPos : ∀ p, 0 < ∫ x, w p x ∂mu) :
    Continuous (fun p => ∫ x, f p x ∂realIntegralWeightedProbabilityMeasure mu (w p)) :=
  realIntegralWeightedProbabilityMeasure_integral_continuous
    mu w f hw hf hwNonneg hMassPos

-- The normalized density is jointly continuous, with its actual mass retained.
example {P X : Type*} [TopologicalSpace P] [TopologicalSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] [CompactSpace X]
    (mu : Measure X) [IsFiniteMeasure mu] (w : P → X → ℝ)
    (hw : Continuous (Function.uncurry w))
    (hMassPos : ∀ p, 0 < ∫ x, w p x ∂mu) :
    Continuous (fun q : P × X => (∫ x, w q.1 x ∂mu)⁻¹ * w q.1 q.2) :=
  realIntegralWeightedDensity_joint_continuous mu w hw hMassPos

end

end MGAP4D.MathlibAnalytic
