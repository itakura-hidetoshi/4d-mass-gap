import MGAP4D.MathlibAnalytic.RealIntegralCovarianceLinearity
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

private theorem memLp_two_integrable_probability_finiteLinearity
    {alpha : Type*}
    [MeasurableSpace alpha]
    {mu : Measure alpha}
    [IsProbabilityMeasure mu]
    {f : alpha -> Real}
    (hf : MemLp f 2 mu) :
    Integrable f mu :=
  memLp_one_iff_integrable.1 (hf.mono_exponent one_le_two)

/-- Real covariance is linear under real scalar multiplication in its right
slot for square-integrable observables over a probability measure. -/
theorem realIntegralCovariance_const_mul_right_of_memLp_two
    {alpha : Type*}
    [MeasurableSpace alpha]
    (mu : Measure alpha)
    [IsProbabilityMeasure mu]
    (c : Real)
    (f g : alpha -> Real)
    (hf : MemLp f 2 mu)
    (hg : MemLp g 2 mu) :
    realIntegralCovariance mu f (fun x => c * g x) =
      c * realIntegralCovariance mu f g := by
  have hgInt : Integrable g mu :=
    memLp_two_integrable_probability_finiteLinearity hg
  have hfgInt : Integrable (f * g) mu :=
    hf.integrable_mul hg
  unfold realIntegralCovariance
  rw [show
      (∫ x, f x * (c * g x) ∂mu) =
        c * ∫ x, f x * g x ∂mu by
      calc
        (∫ x, f x * (c * g x) ∂mu) =
            ∫ x, c * (f x * g x) ∂mu := by
          apply integral_congr_ae
          filter_upwards [] with x
          ring
        _ = c * ∫ x, f x * g x ∂mu := by
          rw [integral_const_mul]]
  rw [show
      (∫ x, c * g x ∂mu) =
        c * ∫ x, g x ∂mu by
      rw [integral_const_mul]]
  ring

/-- Real covariance commutes with a finite sum in its right slot when every
summand is square-integrable. -/
theorem realIntegralCovariance_finset_sum_right_of_memLp_two
    {alpha ι : Type*}
    [MeasurableSpace alpha]
    [DecidableEq ι]
    (mu : Measure alpha)
    [IsProbabilityMeasure mu]
    (s : Finset ι)
    (f : alpha -> Real)
    (g : ι -> alpha -> Real)
    (hf : MemLp f 2 mu)
    (hg : forall i, i ∈ s -> MemLp (g i) 2 mu) :
    realIntegralCovariance mu f (fun x => ∑ i in s, g i x) =
      ∑ i in s, realIntegralCovariance mu f (g i) := by
  have hGInt :
      forall i, i ∈ s -> Integrable (g i) mu := by
    intro i hi
    exact
      memLp_two_integrable_probability_finiteLinearity
        (hg i hi)
  have hFGInt :
      forall i, i ∈ s -> Integrable (f * g i) mu := by
    intro i hi
    exact hf.integrable_mul (hg i hi)
  unfold realIntegralCovariance
  rw [show
      (∫ x, f x * (∑ i in s, g i x) ∂mu) =
        ∑ i in s, ∫ x, f x * g i x ∂mu by
      have hPointwise :
          (fun x => f x * (∑ i in s, g i x)) =
            fun x => ∑ i in s, f x * g i x := by
        funext x
        rw [Finset.mul_sum]
      rw [hPointwise]
      exact integral_finset_sum s hFGInt]
  rw [show
      (∫ x, ∑ i in s, g i x ∂mu) =
        ∑ i in s, ∫ x, g i x ∂mu by
      exact integral_finset_sum s hGInt]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]

/-- Fintype specialization of finite-sum covariance linearity in the right
slot. -/
theorem realIntegralCovariance_fintype_sum_right_of_memLp_two
    {alpha ι : Type*}
    [MeasurableSpace alpha]
    [Fintype ι]
    (mu : Measure alpha)
    [IsProbabilityMeasure mu]
    (f : alpha -> Real)
    (g : ι -> alpha -> Real)
    (hf : MemLp f 2 mu)
    (hg : forall i, MemLp (g i) 2 mu) :
    realIntegralCovariance mu f (fun x => ∑ i : ι, g i x) =
      ∑ i : ι, realIntegralCovariance mu f (g i) := by
  classical
  simpa using
    realIntegralCovariance_finset_sum_right_of_memLp_two
      mu Finset.univ f g hf (fun i _ => hg i)

end

end MathlibAnalytic
end MGAP4D
