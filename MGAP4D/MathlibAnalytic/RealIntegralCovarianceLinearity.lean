import MGAP4D.MathlibAnalytic.RealIntegralWeightedProbabilityNormalization
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

private theorem memLp_two_integrable_probability
    {alpha : Type*}
    [MeasurableSpace alpha]
    {mu : Measure alpha}
    [IsProbabilityMeasure mu]
    {f : alpha -> Real}
    (hf : MemLp f 2 mu) :
    Integrable f mu :=
  memLp_one_iff_integrable.1 (hf.mono_exponent one_le_two)

/-- Real covariance is additive in its left slot for square-integrable
observables over a probability measure. -/
theorem realIntegralCovariance_add_left_of_memLp_two
    {alpha : Type*}
    [MeasurableSpace alpha]
    (mu : Measure alpha)
    [IsProbabilityMeasure mu]
    (f g h : alpha -> Real)
    (hf : MemLp f 2 mu)
    (hg : MemLp g 2 mu)
    (hh : MemLp h 2 mu) :
    realIntegralCovariance mu (f + g) h =
      realIntegralCovariance mu f h +
        realIntegralCovariance mu g h := by
  have hfInt := memLp_two_integrable_probability hf
  have hgInt := memLp_two_integrable_probability hg
  have hfhInt : Integrable (f * h) mu := hf.integrable_mul hh
  have hghInt : Integrable (g * h) mu := hg.integrable_mul hh
  unfold realIntegralCovariance
  rw [show
      (∫ x, (f x + g x) * h x ∂mu) =
        (∫ x, f x * h x ∂mu) + ∫ x, g x * h x ∂mu by
      simpa [add_mul] using integral_add hfhInt hghInt]
  rw [show
      (∫ x, f x + g x ∂mu) =
        (∫ x, f x ∂mu) + ∫ x, g x ∂mu by
      simpa using integral_add hfInt hgInt]
  ring

/-- Real covariance is additive in its right slot for square-integrable
observables over a probability measure. -/
theorem realIntegralCovariance_add_right_of_memLp_two
    {alpha : Type*}
    [MeasurableSpace alpha]
    (mu : Measure alpha)
    [IsProbabilityMeasure mu]
    (f g h : alpha -> Real)
    (hf : MemLp f 2 mu)
    (hg : MemLp g 2 mu)
    (hh : MemLp h 2 mu) :
    realIntegralCovariance mu h (f + g) =
      realIntegralCovariance mu h f +
        realIntegralCovariance mu h g := by
  have hfInt := memLp_two_integrable_probability hf
  have hgInt := memLp_two_integrable_probability hg
  have hhfInt : Integrable (h * f) mu := hh.integrable_mul hf
  have hhgInt : Integrable (h * g) mu := hh.integrable_mul hg
  unfold realIntegralCovariance
  rw [show
      (∫ x, h x * (f x + g x) ∂mu) =
        (∫ x, h x * f x ∂mu) + ∫ x, h x * g x ∂mu by
      simpa [mul_add] using integral_add hhfInt hhgInt]
  rw [show
      (∫ x, f x + g x ∂mu) =
        (∫ x, f x ∂mu) + ∫ x, g x ∂mu by
      simpa using integral_add hfInt hgInt]
  ring

/-- Real covariance is compatible with subtraction in its left slot for
square-integrable observables over a probability measure. -/
theorem realIntegralCovariance_sub_left_of_memLp_two
    {alpha : Type*}
    [MeasurableSpace alpha]
    (mu : Measure alpha)
    [IsProbabilityMeasure mu]
    (f g h : alpha -> Real)
    (hf : MemLp f 2 mu)
    (hg : MemLp g 2 mu)
    (hh : MemLp h 2 mu) :
    realIntegralCovariance mu (f - g) h =
      realIntegralCovariance mu f h -
        realIntegralCovariance mu g h := by
  have hfInt := memLp_two_integrable_probability hf
  have hgInt := memLp_two_integrable_probability hg
  have hfhInt : Integrable (f * h) mu := hf.integrable_mul hh
  have hghInt : Integrable (g * h) mu := hg.integrable_mul hh
  unfold realIntegralCovariance
  rw [show
      (∫ x, (f x - g x) * h x ∂mu) =
        (∫ x, f x * h x ∂mu) - ∫ x, g x * h x ∂mu by
      simpa [sub_mul] using integral_sub hfhInt hghInt]
  rw [show
      (∫ x, f x - g x ∂mu) =
        (∫ x, f x ∂mu) - ∫ x, g x ∂mu by
      simpa using integral_sub hfInt hgInt]
  ring

/-- Real covariance is compatible with subtraction in its right slot for
square-integrable observables over a probability measure. -/
theorem realIntegralCovariance_sub_right_of_memLp_two
    {alpha : Type*}
    [MeasurableSpace alpha]
    (mu : Measure alpha)
    [IsProbabilityMeasure mu]
    (f g h : alpha -> Real)
    (hf : MemLp f 2 mu)
    (hg : MemLp g 2 mu)
    (hh : MemLp h 2 mu) :
    realIntegralCovariance mu h (f - g) =
      realIntegralCovariance mu h f -
        realIntegralCovariance mu h g := by
  have hfInt := memLp_two_integrable_probability hf
  have hgInt := memLp_two_integrable_probability hg
  have hhfInt : Integrable (h * f) mu := hh.integrable_mul hf
  have hhgInt : Integrable (h * g) mu := hh.integrable_mul hg
  unfold realIntegralCovariance
  rw [show
      (∫ x, h x * (f x - g x) ∂mu) =
        (∫ x, h x * f x ∂mu) - ∫ x, h x * g x ∂mu by
      simpa [mul_sub] using integral_sub hhfInt hhgInt]
  rw [show
      (∫ x, f x - g x ∂mu) =
        (∫ x, f x ∂mu) - ∫ x, g x ∂mu by
      simpa using integral_sub hfInt hgInt]
  ring

end

end MathlibAnalytic
end MGAP4D
