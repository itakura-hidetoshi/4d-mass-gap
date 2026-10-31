import MGAP4D.MathlibAnalytic.CompactEnergyMismatchOptimization

/-!
# Regression-defect control of the full energy mismatch

The two optimized orientation budgets have product equal to the squared
coupling times the actual regression defect.  This gives an exact threshold
criterion and a defect bound for the full mismatch in the favorable covariance
direction.  The ratio criterion is stated without dividing by a standard
deviation, so its zero endpoints are retained.  Scalar identities do not assume
the covariance Cauchy bound unless it is explicitly stated; in particular,
zero scalar variance alone does not imply zero scalar covariance.

These results do not assert that the actual regression defect is small.
-/

namespace MGAP4D.MathlibAnalytic.CompactEnergyMismatchMoment

open MeasureTheory
noncomputable section
set_option autoImplicit false

/-- The two orientation budgets retain the entire standard deviation. -/
theorem optimalBudget_add_opposite (b s v C : ℝ) :
    optimalBudget b s v C + optimalBudget b (-s) v C =
      2 * b * Real.sqrt v := by
  unfold optimalBudget
  ring

/-- An exact product identity, including zero coupling and variance. -/
theorem optimalBudget_mul_opposite (b s v C : ℝ)
    (hv : 0 ≤ v) (hs : s ^ 2 = 1) :
    optimalBudget b s v C * optimalBudget b (-s) v C =
      b ^ 2 * (v - 4 * C ^ 2) := by
  unfold optimalBudget
  calc
    _ = b ^ 2 * ((Real.sqrt v) ^ 2 - 4 * s ^ 2 * C ^ 2) := by ring
    _ = _ := by simp only [Real.sq_sqrt hv, hs, mul_one]

/-- Rationalization is used only with an explicitly nonzero denominator. -/
theorem optimalBudget_eq_defect_div (b s v C : ℝ)
    (hv : 0 ≤ v) (hs : s ^ 2 = 1)
    (hden : Real.sqrt v - 2 * s * C ≠ 0) :
    optimalBudget b s v C =
      b * (v - 4 * C ^ 2) / (Real.sqrt v - 2 * s * C) := by
  apply (eq_div_iff hden).2
  unfold optimalBudget
  calc
    _ = b * ((Real.sqrt v) ^ 2 - 4 * s ^ 2 * C ^ 2) := by ring
    _ = _ := by simp only [Real.sq_sqrt hv, hs, mul_one]

/-- The strict threshold criterion has an explicit sign condition.  It does
not assume the scalar covariance inequality or positivity of the threshold. -/
theorem optimalBudget_lt_iff_defect (b s v C t : ℝ)
    (hb : 0 ≤ b) (hv : 0 ≤ v) (hs : s ^ 2 = 1) :
    optimalBudget b s v C < t ↔
      0 < t - 2 * b * s * C ∧
        b ^ 2 * (v - 4 * C ^ 2) < t * (t - 4 * b * s * C) := by
  let x : ℝ := b * Real.sqrt v
  let y : ℝ := t - 2 * b * s * C
  have hx : 0 ≤ x := mul_nonneg hb (Real.sqrt_nonneg v)
  have hsq : y ^ 2 - x ^ 2 =
      t * (t - 4 * b * s * C) - b ^ 2 * (v - 4 * C ^ 2) := by
    dsimp [x, y]
    calc
      _ = t * (t - 4 * b * s * C) -
          b ^ 2 * ((Real.sqrt v) ^ 2 - 4 * s ^ 2 * C ^ 2) := by ring
      _ = _ := by simp only [Real.sq_sqrt hv, hs, mul_one]
  have hB : optimalBudget b s v C = x + 2 * b * s * C := by
    dsimp [optimalBudget, x]
    ring
  rw [hB]
  change x + 2 * b * s * C < t ↔
    0 < y ∧ b ^ 2 * (v - 4 * C ^ 2) < t * (t - 4 * b * s * C)
  constructor
  · intro h
    have hxy : x < y := by dsimp [y]; linarith
    have hy : 0 < y := hx.trans_lt hxy
    have hp : 0 < (y - x) * (y + x) :=
      mul_pos (sub_pos.mpr hxy) (add_pos_of_pos_of_nonneg hy hx)
    have hsq' : x ^ 2 < y ^ 2 := by nlinarith [hp]
    exact ⟨hy, by linarith [hsq]⟩
  · rintro ⟨hy, hd⟩
    have hsq' : x ^ 2 < y ^ 2 := by linarith [hsq]
    have hxy : x < y := by
      by_contra hn
      have hle : y ≤ x := le_of_not_gt hn
      have hp : 0 ≤ (x - y) * (x + y) :=
        mul_nonneg (sub_nonneg.mpr hle) (add_nonneg hx hy.le)
      nlinarith [hp]
    dsimp [y] at hxy
    linarith

/-- For a favorable covariance and a positive threshold, the sign condition
is automatic.  The equivalence also includes b=0 and v=0. -/
theorem optimalBudget_lt_iff_defect_of_nonpos (b s v C t : ℝ)
    (hb : 0 ≤ b) (hv : 0 ≤ v) (hs : s ^ 2 = 1)
    (hC : s * C ≤ 0) (ht : 0 < t) :
    optimalBudget b s v C < t ↔
      b ^ 2 * (v - 4 * C ^ 2) < t * (t - 4 * b * s * C) := by
  have hbc : b * s * C ≤ 0 := by
    calc
      _ = b * (s * C) := by ring
      _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hb hC
  have hsign : 0 < t - 2 * b * s * C := by nlinarith
  rw [optimalBudget_lt_iff_defect b s v C t hb hv hs]
  constructor
  · exact fun h => h.2
  · exact fun h => ⟨hsign, h⟩

/-- Favorable covariance converts the optimized coefficient into a square-root
defect bound.  The covariance inequality makes the coefficient nonnegative. -/
theorem optimalBudget_le_sqrt_defect (b s v C : ℝ)
    (hb : 0 ≤ b) (hv : 0 ≤ v) (hs : s ^ 2 = 1)
    (hcov : 4 * C ^ 2 ≤ v) (hC : s * C ≤ 0) :
    optimalBudget b s v C ≤ b * Real.sqrt (v - 4 * C ^ 2) := by
  have hc2 : (s * C) ^ 2 = C ^ 2 := by rw [mul_pow, hs, one_mul]
  have hsquare : (-2 * s * C) ^ 2 ≤ v := by
    calc
      _ = 4 * C ^ 2 := by norm_num [mul_pow, hs]
      _ ≤ v := hcov
  have hcoef : 0 ≤ Real.sqrt v + 2 * s * C := by
    have h := Real.le_sqrt_of_sq_le hsquare
    linarith
  have hp : (s * C) * (Real.sqrt v + 2 * s * C) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hC hcoef
  have hsq : (Real.sqrt v + 2 * s * C) ^ 2 ≤ v - 4 * C ^ 2 := by
    nlinarith [Real.sq_sqrt hv, hc2]
  exact mul_le_mul_of_nonneg_left (Real.le_sqrt_of_sq_le hsq) hb

/-- At positive coupling, budget saturation requires both exact regression
and the favorable orientation.  No scalar Cauchy hypothesis is needed. -/
theorem optimalBudget_eq_zero_iff (b s v C : ℝ)
    (hb : 0 < b) (hv : 0 ≤ v) (hs : s ^ 2 = 1) :
    optimalBudget b s v C = 0 ↔ v - 4 * C ^ 2 = 0 ∧ s * C ≤ 0 := by
  constructor
  · intro hB
    unfold optimalBudget at hB
    have hcoef : Real.sqrt v + 2 * s * C = 0 :=
      (mul_eq_zero.mp hB).resolve_left hb.ne'
    have hroot : Real.sqrt v = -2 * s * C := by linarith
    have hvC : v = 4 * C ^ 2 := by
      calc
        v = (Real.sqrt v) ^ 2 := (Real.sq_sqrt hv).symm
        _ = (-2 * s * C) ^ 2 := by rw [hroot]
        _ = 4 * C ^ 2 := by norm_num [mul_pow, hs]
    refine ⟨sub_eq_zero.mpr hvC, ?_⟩
    have hn := Real.sqrt_nonneg v
    linarith
  · rintro ⟨hd, hC⟩
    have hvC : v = 4 * C ^ 2 := sub_eq_zero.mp hd
    have hn : 0 ≤ -2 * s * C := by nlinarith
    have hroot : Real.sqrt v = -2 * s * C := by
      apply (Real.sqrt_eq_iff_eq_sq hv hn).2
      calc
        v = 4 * C ^ 2 := hvC
        _ = (-2 * s * C) ^ 2 := by norm_num [mul_pow, hs]
    unfold optimalBudget
    rw [hroot]
    ring

/-- A ratio of the two actual optimized orientation budgets is exactly a
linear condition on standard deviation and oriented covariance. -/
theorem optimalBudget_lt_mul_opposite_iff_linear (b s v C r : ℝ)
    (hb : 0 < b) :
    optimalBudget b s v C < r * optimalBudget b (-s) v C ↔
      (1 - r) * Real.sqrt v + 2 * (1 + r) * s * C < 0 := by
  have hrw : r * optimalBudget b (-s) v C =
      b * (r * (Real.sqrt v - 2 * s * C)) := by
    unfold optimalBudget
    ring
  rw [hrw]
  change b * (Real.sqrt v + 2 * s * C) <
      b * (r * (Real.sqrt v - 2 * s * C)) ↔ _
  rw [mul_lt_mul_iff_right₀ hb]
  constructor
  · intro h
    nlinarith
  · intro h
    nlinarith

/-- Exact relative-defect criterion for orientation ratios up to one.
No division by variance and no scalar Cauchy hypothesis is used. -/
theorem optimalBudget_lt_mul_opposite_iff_defect (b s v C r : ℝ)
    (hb : 0 < b) (hv : 0 ≤ v) (hs : s ^ 2 = 1)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    optimalBudget b s v C < r * optimalBudget b (-s) v C ↔
      s * C < 0 ∧ (1 + r) ^ 2 * (v - 4 * C ^ 2) < 4 * r * v := by
  rw [optimalBudget_lt_mul_opposite_iff_linear b s v C r hb]
  let x : ℝ := (1 - r) * Real.sqrt v
  let y : ℝ := 2 * (1 + r) * s * C
  have hx : 0 ≤ x := mul_nonneg (sub_nonneg.mpr hr1) (Real.sqrt_nonneg v)
  have hc : 0 < 2 * (1 + r) := by linarith
  have hyexpr : y = (2 * (1 + r)) * (s * C) := by dsimp [y]; ring
  have hfactor : (1 + r) ^ 2 * (v - 4 * C ^ 2) - 4 * r * v =
      (x + y) * (x - y) := by
    dsimp [x, y]
    calc
      _ = (1 - r) ^ 2 * v - 4 * (1 + r) ^ 2 * C ^ 2 := by ring
      _ = (1 - r) ^ 2 * (Real.sqrt v) ^ 2 -
          4 * (1 + r) ^ 2 * s ^ 2 * C ^ 2 := by
        simp only [Real.sq_sqrt hv, hs, mul_one]
      _ = _ := by ring
  change x + y < 0 ↔
    s * C < 0 ∧ (1 + r) ^ 2 * (v - 4 * C ^ 2) < 4 * r * v
  constructor
  · intro h
    have hy : y < 0 := by linarith
    have hC : s * C < 0 := by
      by_contra hn
      have hc0 : 0 ≤ s * C := le_of_not_gt hn
      have hyn : 0 ≤ y := by rw [hyexpr]; exact mul_nonneg hc.le hc0
      linarith
    have hpos : 0 < x - y := by linarith
    have hp : (x + y) * (x - y) < 0 := mul_neg_of_neg_of_pos h hpos
    exact ⟨hC, by linarith [hfactor]⟩
  · rintro ⟨hC, hd⟩
    have hy : y < 0 := by rw [hyexpr]; exact mul_neg_of_pos_of_neg hc hC
    have hpos : 0 < x - y := by linarith
    have hp : (x + y) * (x - y) < 0 := by linarith [hfactor]
    by_contra hn
    have hnonneg : 0 ≤ x + y := le_of_not_gt hn
    exact (not_lt_of_ge (mul_nonneg hnonneg hpos.le)) hp

section Probability

variable {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
  [CompactSpace α] [SecondCountableTopology α] [BorelSpace α]
  (μ : Measure α) [IsProbabilityMeasure μ]

/-- The entire mismatch is controlled by the actual regression defect in
the favorable covariance direction, including zero coupling and variance. -/
theorem mismatch_le_sqrt_regressionDefect (b s : ℝ)
    (hb : 0 ≤ b) (hs : s ^ 2 = 1) (F E : α → ℝ)
    (hF : Continuous F) (hE : Continuous E) (hEV : variance μ E = (1 / 4 : ℝ))
    (hC : s * covariance μ F E ≤ 0) :
    mismatch μ b s F E ≤ b * Real.sqrt (regressionDefect μ F E) := by
  have h := mismatch_le_optimized μ b s hb hs F E hF hE hEV
  have hu := optimalBudget_le_sqrt_defect b s (variance μ F) (covariance μ F E)
    hb (variance_nonneg μ F hF) hs
    (four_covariance_sq_le_variance μ F E hF hE hEV) hC
  exact h.trans hu

/-- Positive actual variance permits the sharper rationalized defect bound. -/
theorem mismatch_le_regressionDefect_div (b s : ℝ)
    (hb : 0 ≤ b) (hs : s ^ 2 = 1) (F E : α → ℝ)
    (hF : Continuous F) (hE : Continuous E) (hEV : variance μ E = (1 / 4 : ℝ))
    (hC : s * covariance μ F E ≤ 0) (hV : 0 < variance μ F) :
    mismatch μ b s F E ≤ b * regressionDefect μ F E /
      (Real.sqrt (variance μ F) - 2 * s * covariance μ F E) := by
  have hp : 0 < Real.sqrt (variance μ F) := Real.sqrt_pos.mpr hV
  have hden : Real.sqrt (variance μ F) - 2 * s * covariance μ F E ≠ 0 := by
    have : 0 < Real.sqrt (variance μ F) - 2 * s * covariance μ F E := by nlinarith
    exact this.ne'
  calc
    _ ≤ optimalBudget b s (variance μ F) (covariance μ F E) :=
      mismatch_le_optimized μ b s hb hs F E hF hE hEV
    _ = _ := optimalBudget_eq_defect_div b s (variance μ F) (covariance μ F E)
      hV.le hs hden

/-- Exact regression in the favorable orientation has no negative tail. -/
theorem mismatch_eq_zero_of_regressionDefect_zero (b s : ℝ)
    (hb : 0 ≤ b) (hs : s ^ 2 = 1) (F E : α → ℝ)
    (hF : Continuous F) (hE : Continuous E) (hEV : variance μ E = (1 / 4 : ℝ))
    (hC : s * covariance μ F E ≤ 0) (hD : regressionDefect μ F E = 0) :
    mismatch μ b s F E = 0 := by
  have h := mismatch_le_sqrt_regressionDefect μ b s hb hs F E hF hE hEV hC
  have hu : mismatch μ b s F E ≤ 0 := by
    simpa only [hD, Real.sqrt_zero, mul_zero] using h
  have hn : (0 : ℝ) ≤ mismatch μ b s F E := by
    unfold mismatch
    exact integral_nonneg (fun _ => le_max_right _ _)
  exact le_antisymm hu hn

end Probability
end
end MGAP4D.MathlibAnalytic.CompactEnergyMismatchMoment

#print axioms MGAP4D.MathlibAnalytic.CompactEnergyMismatchMoment.optimalBudget_add_opposite
#print axioms MGAP4D.MathlibAnalytic.CompactEnergyMismatchMoment.optimalBudget_mul_opposite
#print axioms MGAP4D.MathlibAnalytic.CompactEnergyMismatchMoment.optimalBudget_eq_defect_div
#print axioms MGAP4D.MathlibAnalytic.CompactEnergyMismatchMoment.optimalBudget_lt_iff_defect
#print axioms MGAP4D.MathlibAnalytic.CompactEnergyMismatchMoment.optimalBudget_lt_iff_defect_of_nonpos
#print axioms MGAP4D.MathlibAnalytic.CompactEnergyMismatchMoment.optimalBudget_le_sqrt_defect
#print axioms MGAP4D.MathlibAnalytic.CompactEnergyMismatchMoment.optimalBudget_eq_zero_iff
#print axioms MGAP4D.MathlibAnalytic.CompactEnergyMismatchMoment.optimalBudget_lt_mul_opposite_iff_linear
#print axioms MGAP4D.MathlibAnalytic.CompactEnergyMismatchMoment.optimalBudget_lt_mul_opposite_iff_defect
#print axioms MGAP4D.MathlibAnalytic.CompactEnergyMismatchMoment.mismatch_le_sqrt_regressionDefect
#print axioms MGAP4D.MathlibAnalytic.CompactEnergyMismatchMoment.mismatch_le_regressionDefect_div
#print axioms MGAP4D.MathlibAnalytic.CompactEnergyMismatchMoment.mismatch_eq_zero_of_regressionDefect_zero
