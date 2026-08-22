import MGAP4D.MathlibAnalytic.PeriodicHypercubicSpecialUnitarySingleLinkTVInfluence
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

/-!
# High-beta limit of the current compact SU(N) active-TV majorant

The current same-root finite-volume Dobrushin route uses the explicit active
single-link total-variation majorant

`q(beta) = (exp (4 beta) - 1) / (exp (4 beta) + 1)`.

This file records its large-coupling behavior.  As `beta → +∞`, `q(beta) → 1`,
so the four-dimensional row coefficient `18 * q(beta)` tends to `18`, not to a
number below one.

Consequently, for any coupling sequence with `beta_n → +∞`, neither the finite
Dobrushin threshold `18 * q(beta_n) < 1` nor any scale-independent bound
`18 * q(beta_n) ≤ rhoBar < 1` can hold eventually.

This is a route-diagnostic theorem only.  It does not assert that the current
abstract continuum coupling sequence tends to infinity; when that asymptotic is
supplied by a concrete physical scaling, it shows that the present
high-temperature Dobrushin comparison cannot be the continuum clustering
mechanism.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter

noncomputable section

/-- The rational function `(x-1)/(x+1)` tends to one as `x → +∞`. -/
theorem tendsto_sub_one_div_add_one_atTop :
    Tendsto (fun x : ℝ => (x - 1) / (x + 1)) atTop (nhds 1) := by
  have hinv : Tendsto (fun x : ℝ => x⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero
  have hratio :
      Tendsto (fun x : ℝ => (1 - x⁻¹) / (1 + x⁻¹)) atTop (nhds 1) := by
    have hnum : Tendsto (fun x : ℝ => 1 - x⁻¹) atTop (nhds 1) := by
      simpa using (tendsto_const_nhds.sub hinv)
    have hden : Tendsto (fun x : ℝ => 1 + x⁻¹) atTop (nhds 1) := by
      simpa using (tendsto_const_nhds.add hinv)
    simpa using hnum.div hden (by norm_num)
  apply hratio.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  field_simp [ne_of_gt hx]

/-- The explicit active one-link TV majorant tends to one at large coupling. -/
theorem periodicHypercubicSpecialUnitaryActiveTVMajorant_tendsto_one_atTop :
    Tendsto periodicHypercubicSpecialUnitaryActiveTVMajorant atTop (nhds 1) := by
  have hlin : Tendsto (fun beta : ℝ => beta * 4) atTop atTop :=
    (tendsto_id : Tendsto (fun beta : ℝ => beta) atTop atTop).atTop_mul_const
      (by norm_num)
  have hexp : Tendsto (fun beta : ℝ => Real.exp (beta * 4)) atTop atTop :=
    Real.tendsto_exp_atTop.comp hlin
  simpa [periodicHypercubicSpecialUnitaryActiveTVMajorant] using
    tendsto_sub_one_div_add_one_atTop.comp hexp

/-- Along every coupling sequence diverging to `+∞`, the current active-TV
majorant converges to one. -/
theorem periodicHypercubicSpecialUnitaryActiveTVMajorant_tendsto_one_of_beta_tendsto_atTop
    (beta : ℕ → ℝ)
    (hbeta : Tendsto beta atTop atTop) :
    Tendsto
      (fun n => periodicHypercubicSpecialUnitaryActiveTVMajorant (beta n))
      atTop (nhds 1) :=
  periodicHypercubicSpecialUnitaryActiveTVMajorant_tendsto_one_atTop.comp hbeta

/-- Hence the concrete four-dimensional Dobrushin row coefficient tends to
`18`, rather than remaining below one, along any `beta_n → +∞` sequence. -/
theorem periodicHypercubicSpecialUnitary_eighteen_mul_activeTVMajorant_tendsto_eighteen_of_beta_tendsto_atTop
    (beta : ℕ → ℝ)
    (hbeta : Tendsto beta atTop atTop) :
    Tendsto
      (fun n => 18 * periodicHypercubicSpecialUnitaryActiveTVMajorant (beta n))
      atTop (nhds 18) := by
  have hq :=
    periodicHypercubicSpecialUnitaryActiveTVMajorant_tendsto_one_of_beta_tendsto_atTop
      beta hbeta
  simpa using tendsto_const_nhds.mul hq

/-- If `beta_n → +∞`, the current finite-volume Dobrushin threshold cannot hold
eventually. -/
theorem periodicHypercubicSpecialUnitary_not_eventually_threshold_of_beta_tendsto_atTop
    (beta : ℕ → ℝ)
    (hbeta : Tendsto beta atTop atTop) :
    ¬ ∀ᶠ n : ℕ in atTop,
      18 * periodicHypercubicSpecialUnitaryActiveTVMajorant (beta n) < 1 := by
  have h18 :=
    periodicHypercubicSpecialUnitary_eighteen_mul_activeTVMajorant_tendsto_eighteen_of_beta_tendsto_atTop
      beta hbeta
  have hgt :
      ∀ᶠ n : ℕ in atTop,
        1 < 18 * periodicHypercubicSpecialUnitaryActiveTVMajorant (beta n) :=
    (tendsto_order.1 h18).1 1 (by norm_num)
  intro hlt
  rcases (hlt.and hgt).exists with ⟨n, hnlt, hngt⟩
  exact (lt_asymm hnlt hngt).elim

/-- More strongly, if `beta_n → +∞`, no fixed `rhoBar < 1` can eventually
majorize the scale-dependent Dobrushin row coefficients. -/
theorem periodicHypercubicSpecialUnitary_not_eventually_eighteen_mul_activeTVMajorant_le_of_beta_tendsto_atTop
    (beta : ℕ → ℝ)
    (hbeta : Tendsto beta atTop atTop)
    (rhoBar : ℝ)
    (hrhoBar : rhoBar < 1) :
    ¬ ∀ᶠ n : ℕ in atTop,
      18 * periodicHypercubicSpecialUnitaryActiveTVMajorant (beta n) ≤ rhoBar := by
  have h18 :=
    periodicHypercubicSpecialUnitary_eighteen_mul_activeTVMajorant_tendsto_eighteen_of_beta_tendsto_atTop
      beta hbeta
  have hrho18 : rhoBar < 18 := hrhoBar.trans (by norm_num)
  have hgt :
      ∀ᶠ n : ℕ in atTop,
        rhoBar < 18 * periodicHypercubicSpecialUnitaryActiveTVMajorant (beta n) :=
    (tendsto_order.1 h18).1 rhoBar hrho18
  intro hle
  rcases (hle.and hgt).exists with ⟨n, hnle, hngt⟩
  exact (not_lt_of_ge hnle) hngt

end

end MathlibAnalytic
end MGAP4D
