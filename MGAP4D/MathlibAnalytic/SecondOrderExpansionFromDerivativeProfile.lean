import MGAP4D.MathlibAnalytic.NonzeroSecondOrderSmallPositive
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Filter Set TopologicalSpace

noncomputable section

/-- A convenient second-order Peano criterion tailored to the finite Boltzmann
families used below.

If `g` is an everywhere-defined derivative profile for `f`, both `f` and `g`
vanish at zero, and `g'(0)=d₂`, then

`f(β) / β² → d₂ / 2`

from the positive side.  The proof uses the derivative-as-slope theorem once
for `g(β)/β` and L'Hôpital once for `f(β)/β²`.

This avoids introducing a separate global `ContDiff` package merely to obtain
the second-order Peano expansion needed by Package Y. -/
theorem hasSecondOrderExpansionAtZero_of_derivativeProfile
    {f g : ℝ → ℝ}
    {d₂ : ℝ}
    (hf : ∀ x : ℝ, HasDerivAt f (g x) x)
    (hf0 : f 0 = 0)
    (hg0 : g 0 = 0)
    (hg : HasDerivAt g d₂ 0) :
    HasSecondOrderExpansionAtZero f d₂ := by
  refine ⟨hf0, ?_, ?_⟩
  · simpa [hg0] using hf 0
  · have hSlope :
        Tendsto (fun β : ℝ => g β / β)
          (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds d₂) := by
      have h := hg.tendsto_slope_zero_right
      simpa [hg0, div_eq_mul_inv, mul_comm] using h
    have hRatio :
        Tendsto (fun β : ℝ => g β / (2 * β))
          (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds (d₂ / 2)) := by
      have h := hSlope.div_const (2 : ℝ)
      simpa [div_eq_mul_inv, mul_assoc] using h
    have hfTendsto :
        Tendsto f (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0) := by
      have h := (hf 0).continuousAt
      have ht := h.tendsto.mono_left inf_le_left
      simpa [hf0] using ht
    have hsqTendsto :
        Tendsto (fun β : ℝ => β ^ 2)
          (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0) := by
      have h : ContinuousAt (fun β : ℝ => β ^ 2) 0 :=
        continuousAt_id.pow 2
      simpa using h.tendsto.mono_left inf_le_left
    apply HasDerivAt.lhopital_zero_right_on_Ioo
      (a := (0 : ℝ)) (b := (1 : ℝ))
      (f := f) (f' := g)
      (g := fun β : ℝ => β ^ 2)
      (g' := fun β : ℝ => 2 * β)
      zero_lt_one
    · intro x hx
      exact hf x
    · intro x hx
      simpa [pow_two, two_mul] using
        (hasDerivAt_id (x := x)).mul (hasDerivAt_id (x := x))
    · intro x hx
      exact mul_ne_zero (by norm_num) (ne_of_gt hx.1)
    · exact hfTendsto
    · exact hsqTendsto
    · exact hRatio

end

end MathlibAnalytic
end MGAP4D
