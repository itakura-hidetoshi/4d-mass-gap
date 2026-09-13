import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- A pairwise cross-ratio bound survives integration against two arbitrary
nonnegative left weights without worsening its coefficient.

This is the integral analogue of the normalized-Doob cross-ratio transport:
if the source-conditioned factors `r,s` satisfy
`r x * s y ≤ K * s x * r y` for every pair of base points, then testing them
against two possibly different nonnegative weights `p,q` preserves the same
coefficient `K` after integration.

The four explicit integrability hypotheses are exactly the four one-variable
integrals appearing in the conclusion; no probability normalization or
independence assumption is used. -/
theorem real_integral_crossRatio_le_of_pairwise_crossRatio
    {α : Type*}
    [MeasurableSpace α]
    {μ : Measure α}
    [SFinite μ]
    (p q r s : α → ℝ)
    (K : ℝ)
    (hpr : Integrable (fun x => p x * r x) μ)
    (hqs : Integrable (fun x => q x * s x) μ)
    (hps : Integrable (fun x => p x * s x) μ)
    (hqr : Integrable (fun x => q x * r x) μ)
    (hp : ∀ x, 0 ≤ p x)
    (hq : ∀ x, 0 ≤ q x)
    (hcross : ∀ x y, r x * s y ≤ K * (s x * r y)) :
    (∫ x, p x * r x ∂μ) * (∫ y, q y * s y ∂μ) ≤
      K * ((∫ x, p x * s x ∂μ) * (∫ y, q y * r y ∂μ)) := by
  rw [← integral_prod_mul, ← integral_prod_mul]

end

end MathlibAnalytic
end MGAP4D
