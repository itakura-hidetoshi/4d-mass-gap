import Mathlib

/-!
# PZ37M — quantitative scalar, Haar integration and eighth-order minor estimates

These are proved estimates, not added analytic assumptions. Seventh-order row
errors multiply first-order differences; their quadratic products are retained.
-/
open MeasureTheory
open scoped BigOperators
noncomputable section
namespace MGAP4D.MathlibAnalytic.PZ37MEstimates

def expTaylor6 (x : ℝ) : ℝ :=
  1 + x + x^2/2 + x^3/6 + x^4/24 + x^5/120 + x^6/720

theorem expTaylor6_continuous : Continuous expTaylor6 := by
  unfold expTaylor6
  fun_prop

theorem expTaylor6_remainder (x : ℝ) (hx : ‖x‖ ≤ 1) :
    ‖Real.exp x - expTaylor6 x‖ ≤ ‖x‖^7 := by
  have h := Real.exp_bound (x := x) (n := 7)
    (by simpa only [Real.norm_eq_abs] using hx) (by norm_num)
  have hs : (∑ m ∈ Finset.range 7, x^m/(m.factorial : ℝ)) = expTaylor6 x := by
    norm_num [Finset.sum_range_succ, expTaylor6]
  rw [hs] at h
  norm_num at h
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  nlinarith [pow_nonneg (abs_nonneg x) 7]

theorem polynomial_tail (beta : ℝ) (hb : ‖beta‖ ≤ 1)
    (m n : ℕ) (a : Fin n → ℝ) :
    ‖∑ i : Fin n, beta^(m+i.val)*a i‖ ≤ ‖beta‖^m * ∑ i, ‖a i‖ := by
  calc
    _ ≤ ∑ i : Fin n, ‖beta^(m+i.val)*a i‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin n, ‖beta‖^m * ‖a i‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_mul, norm_pow]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_of_le_one (norm_nonneg _) hb (by omega)) (norm_nonneg _)
    _ = _ := by rw [Finset.mul_sum]

section Integrals
variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsProbabilityMeasure μ]

private theorem int_cont (f : X → ℝ) (hf : Continuous f) : Integrable f μ :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem integral_error (f g : X → ℝ) (hf : Continuous f) (hg : Continuous g)
    (E : ℝ) (h : ∀ x, ‖f x - g x‖ ≤ E) :
    ‖(∫ x, f x ∂μ) - ∫ x, g x ∂μ‖ ≤ E := by
  rw [← integral_sub (int_cont μ f hf) (int_cont μ g hg)]
  simpa using norm_integral_le_of_norm_le_const (μ := μ) (Filter.Eventually.of_forall h)

theorem integral_first_continuous (f : X × X → ℝ) (hf : Continuous f) :
    Continuous (fun a => ∫ x, f (x,a) ∂μ) := by
  let F : C(X × X, ℝ) := ⟨f,hf⟩
  let v : C(X, C(X, ℝ)) := F.curry
  have hv : Integrable (fun x => v x) μ :=
    v.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have heq : (fun a => ∫ x, f (x,a) ∂μ) =
      (fun a => (∫ x, v x ∂μ) a) := by
    funext a
    rw [ContinuousMap.integral_apply hv a]
    rfl
  rw [heq]
  exact (∫ x, v x ∂μ).continuous

theorem double_integral_add (f g : X × X → ℝ)
    (hf : Continuous f) (hg : Continuous g) :
    (∫ a, ∫ x, (f (x,a) + g (x,a)) ∂μ ∂μ) =
      (∫ a, ∫ x, f (x,a) ∂μ ∂μ) + ∫ a, ∫ x, g (x,a) ∂μ ∂μ := by
  have hInner (a : X) : (∫ x, (f (x,a) + g (x,a)) ∂μ) =
      (∫ x, f (x,a) ∂μ) + ∫ x, g (x,a) ∂μ :=
    integral_add
      (int_cont μ _ (hf.comp (continuous_id.prodMk continuous_const)))
      (int_cont μ _ (hg.comp (continuous_id.prodMk continuous_const)))
  simp_rw [hInner]
  exact integral_add
    (int_cont μ _ (integral_first_continuous μ f hf))
    (int_cont μ _ (integral_first_continuous μ g hg))

theorem double_integral_error (f g : X × X → ℝ)
    (hf : Continuous f) (hg : Continuous g) (E : ℝ)
    (h : ∀ x a, ‖f (x,a) - g (x,a)‖ ≤ E) :
    ‖(∫ a, ∫ x, f (x,a) ∂μ ∂μ) - ∫ a, ∫ x, g (x,a) ∂μ ∂μ‖ ≤ E := by
  apply integral_error μ _ _
    (integral_first_continuous μ f hf) (integral_first_continuous μ g hg) E
  intro a
  exact integral_error μ _ _
    (hf.comp (continuous_id.prodMk continuous_const))
    (hg.comp (continuous_id.prodMk continuous_const)) E (fun x => h x a)
end Integrals
theorem minor_eighthOrder_stability
    (r L E₁ E₂ Q : ℝ)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hE₁ : 0 ≤ E₁) (hE₂ : 0 ≤ E₂)
    (x y u v ex ey eu ev target : ℝ)
    (hx : ‖x‖ ≤ r * L) (hy : ‖y‖ ≤ r * L)
    (hu : ‖u‖ ≤ r * L) (hv : ‖v‖ ≤ r * L)
    (hex : ‖ex‖ ≤ r ^ 7 * E₁)
    (hey : ‖ey‖ ≤ r ^ 7 * E₁)
    (heu : ‖eu‖ ≤ r ^ 7 * E₂)
    (hev : ‖ev‖ ≤ r ^ 7 * E₂)
    (hDet : ‖x * u - y * v - target‖ ≤ r ^ 8 * Q) :
    ‖(x + ex) * (u + eu) - (y + ey) * (v + ev) - target‖ ≤
      r ^ 8 * (Q + 2 * E₁ * L + 2 * E₂ * L + 2 * E₁ * E₂) := by
  have hr6 : r ^ 6 ≤ 1 := by
    calc
      r ^ 6 ≤ (1 : ℝ) ^ 6 := pow_le_pow_left₀ hr0 hr1 6
      _ = 1 := by norm_num
  have hr14 : r ^ 14 ≤ r ^ 8 := by
    calc
      r ^ 14 = r ^ 8 * r ^ 6 := by ring
      _ ≤ r ^ 8 * 1 :=
        mul_le_mul_of_nonneg_left hr6 (pow_nonneg hr0 8)
      _ = r ^ 8 := by ring
  have h71 (e z : ℝ)
      (he : ‖e‖ ≤ r ^ 7 * E₁) (hz : ‖z‖ ≤ r * L) :
      ‖e * z‖ ≤ r ^ 8 * E₁ * L := by
    calc
      ‖e * z‖ = ‖e‖ * ‖z‖ := norm_mul _ _
      _ ≤ (r ^ 7 * E₁) * (r * L) :=
        mul_le_mul he hz (norm_nonneg _) (by positivity)
      _ = r ^ 8 * E₁ * L := by ring
  have h17 (z e : ℝ)
      (hz : ‖z‖ ≤ r * L) (he : ‖e‖ ≤ r ^ 7 * E₂) :
      ‖z * e‖ ≤ r ^ 8 * E₂ * L := by
    calc
      ‖z * e‖ = ‖e * z‖ := by rw [mul_comm]
      _ ≤ r ^ 8 * E₂ * L := by
        calc
          ‖e * z‖ = ‖e‖ * ‖z‖ := norm_mul _ _
          _ ≤ (r ^ 7 * E₂) * (r * L) :=
            mul_le_mul he hz (norm_nonneg _) (by positivity)
          _ = r ^ 8 * E₂ * L := by ring
  have h77 (e f : ℝ)
      (he : ‖e‖ ≤ r ^ 7 * E₁)
      (hf : ‖f‖ ≤ r ^ 7 * E₂) :
      ‖e * f‖ ≤ r ^ 8 * E₁ * E₂ := by
    calc
      ‖e * f‖ = ‖e‖ * ‖f‖ := norm_mul _ _
      _ ≤ (r ^ 7 * E₁) * (r ^ 7 * E₂) :=
        mul_le_mul he hf (norm_nonneg _) (by positivity)
      _ = r ^ 14 * (E₁ * E₂) := by ring
      _ ≤ r ^ 8 * (E₁ * E₂) :=
        mul_le_mul_of_nonneg_right hr14 (mul_nonneg hE₁ hE₂)
      _ = r ^ 8 * E₁ * E₂ := by ring
  have hTerm₁ := h71 ex u hex hu
  have hTerm₂ := h17 x eu hx heu
  have hTerm₃ := h77 ex eu hex heu
  have hTerm₄ := h71 ey v hey hv
  have hTerm₅ := h17 y ev hy hev
  have hTerm₆ := h77 ey ev hey hev
  have hTri :
      ‖(x + ex) * (u + eu) - (y + ey) * (v + ev) - target‖ ≤
        ‖x * u - y * v - target‖ +
          ‖ex * u‖ + ‖x * eu‖ + ‖ex * eu‖ +
          ‖ey * v‖ + ‖y * ev‖ + ‖ey * ev‖ := by
    have hEq :
        (x + ex) * (u + eu) - (y + ey) * (v + ev) - target =
          (x * u - y * v - target) +
            ((ex * u + x * eu + ex * eu) -
              (ey * v + y * ev + ey * ev)) := by ring
    rw [hEq]
    have h1 := norm_add_le (x * u - y * v - target)
      ((ex * u + x * eu + ex * eu) - (ey * v + y * ev + ey * ev))
    have h2 := norm_sub_le (ex * u + x * eu + ex * eu)
      (ey * v + y * ev + ey * ev)
    have h3 := norm_add_le (ex * u + x * eu) (ex * eu)
    have h4 := norm_add_le (ex * u) (x * eu)
    have h5 := norm_add_le (ey * v + y * ev) (ey * ev)
    have h6 := norm_add_le (ey * v) (y * ev)
    linarith
  calc
    ‖(x + ex) * (u + eu) - (y + ey) * (v + ev) - target‖ ≤
        ‖x * u - y * v - target‖ +
          ‖ex * u‖ + ‖x * eu‖ + ‖ex * eu‖ +
          ‖ey * v‖ + ‖y * ev‖ + ‖ey * ev‖ := hTri
    _ ≤ r ^ 8 * Q +
          2 * (r ^ 8 * E₁ * L) + 2 * (r ^ 8 * E₂ * L) +
          2 * (r ^ 8 * E₁ * E₂) := by linarith
    _ = r ^ 8 *
      (Q + 2 * E₁ * L + 2 * E₂ * L + 2 * E₁ * E₂) := by ring

end MGAP4D.MathlibAnalytic.PZ37MEstimates

#print axioms MGAP4D.MathlibAnalytic.PZ37MEstimates.expTaylor6_continuous
#print axioms MGAP4D.MathlibAnalytic.PZ37MEstimates.expTaylor6_remainder
#print axioms MGAP4D.MathlibAnalytic.PZ37MEstimates.polynomial_tail
#print axioms MGAP4D.MathlibAnalytic.PZ37MEstimates.integral_error
#print axioms MGAP4D.MathlibAnalytic.PZ37MEstimates.integral_first_continuous
#print axioms MGAP4D.MathlibAnalytic.PZ37MEstimates.double_integral_add
#print axioms MGAP4D.MathlibAnalytic.PZ37MEstimates.double_integral_error
#print axioms MGAP4D.MathlibAnalytic.PZ37MEstimates.minor_eighthOrder_stability
