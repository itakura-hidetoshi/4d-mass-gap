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
  have hleftInt : Integrable
      (fun z : α × α => (p z.1 * r z.1) * (q z.2 * s z.2))
      (μ.prod μ) :=
    hpr.mul_prod hqs
  have hrightBaseInt : Integrable
      (fun z : α × α => (p z.1 * s z.1) * (q z.2 * r z.2))
      (μ.prod μ) :=
    hps.mul_prod hqr
  rw [← integral_const_mul]
  apply integral_mono_ae hleftInt (hrightBaseInt.const_mul K)
  filter_upwards with z
  have hw : 0 ≤ p z.1 * q z.2 := mul_nonneg (hp z.1) (hq z.2)
  calc
    p z.1 * r z.1 * (q z.2 * s z.2) =
        (p z.1 * q z.2) * (r z.1 * s z.2) := by ring
    _ ≤ (p z.1 * q z.2) * (K * (s z.1 * r z.2)) :=
      mul_le_mul_of_nonneg_left (hcross z.1 z.2) hw
    _ = K * (p z.1 * s z.1 * (q z.2 * r z.2)) := by ring

end

end MathlibAnalytic
end MGAP4D
