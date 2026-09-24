import MGAP4D.MathlibAnalytic.LikelihoodRatioQuadraticInfluenceIntegrated
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

/-!
# Real-integrable quadratic likelihood-ratio defect

The preceding unit bounds the quadratic density defect in ENNReal lower-integral
form.  This file promotes the same defect to an ordinary real Integrable
function and records the corresponding real integral estimate.

This is the interface needed by the pinned mathlib Hölder/Cauchy--Schwarz API,
which consumes MemLp/Integrable real-valued functions.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace HaarLikelihoodRatioInfluence

/-- Under nonnegative density hypotheses the defect is pointwise nonnegative. -/
theorem quadratic_defect_nonneg_of_density_nonneg
    {α : Type*}
    (p q : α → ℝ)
    (hp0 : ∀ x, 0 ≤ p x)
    (hq0 : ∀ x, 0 ≤ q x)
    (x : α) :
    0 ≤ ((p x - q x) ^ 2) / (p x + q x) := by
  exact div_nonneg (sq_nonneg _) (add_nonneg (hp0 x) (hq0 x))

/-- The integrated quadratic defect from the previous ENNReal theorem is an
ordinary real Integrable function. -/
theorem quadratic_defect_integrable
    {α : Type*}
    [MeasurableSpace α]
    (μ : Measure α)
    (p q : α → ℝ)
    (hpMeas : Measurable p)
    (hqMeas : Measurable q)
    (hpInt : Integrable p μ)
    (hqInt : Integrable q μ)
    (hp0 : ∀ x, 0 ≤ p x)
    (hq0 : ∀ x, 0 ≤ q x)
    (hpOne : ∫ x, p x ∂μ = 1)
    (hqOne : ∫ x, q x ∂μ = 1)
    (K : ℝ)
    (hK : 1 ≤ K)
    (hRatio : ∀ x, p x ≤ K * q x ∧ q x ≤ K * p x) :
    Integrable
      (fun x => ((p x - q x) ^ 2) / (p x + q x)) μ := by
  let d : α → ℝ := fun x => ((p x - q x) ^ 2) / (p x + q x)
  have hdMeas : Measurable d := by
    dsimp [d]
    exact ((hpMeas.sub hqMeas).pow_const 2).div (hpMeas.add hqMeas)
  have hd0 : ∀ x, 0 ≤ d x := by
    intro x
    dsimp [d]
    exact
      quadratic_defect_nonneg_of_density_nonneg p q hp0 hq0 x
  have hBound :=
    quadratic_defect_lintegral_le_fullL1_coefficient_sq
      μ p q hpMeas hqMeas hpInt hqInt hp0 hq0 hpOne hqOne
      K hK hRatio
  refine ⟨hdMeas.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  rw [lintegral_enorm_of_nonneg hd0]
  exact lt_of_le_of_lt hBound ENNReal.ofReal_lt_top

/-- Real-integral form of the quadratic likelihood-ratio influence estimate. -/
theorem quadratic_defect_integral_le_fullL1_coefficient_sq
    {α : Type*}
    [MeasurableSpace α]
    (μ : Measure α)
    (p q : α → ℝ)
    (hpMeas : Measurable p)
    (hqMeas : Measurable q)
    (hpInt : Integrable p μ)
    (hqInt : Integrable q μ)
    (hp0 : ∀ x, 0 ≤ p x)
    (hq0 : ∀ x, 0 ≤ q x)
    (hpOne : ∫ x, p x ∂μ = 1)
    (hqOne : ∫ x, q x ∂μ = 1)
    (K : ℝ)
    (hK : 1 ≤ K)
    (hRatio : ∀ x, p x ≤ K * q x ∧ q x ≤ K * p x) :
    (∫ x, ((p x - q x) ^ 2) / (p x + q x) ∂μ) ≤
      (2 * coefficient K) ^ 2 := by
  let d : α → ℝ := fun x => ((p x - q x) ^ 2) / (p x + q x)
  have hdMeas : Measurable d := by
    dsimp [d]
    exact ((hpMeas.sub hqMeas).pow_const 2).div (hpMeas.add hqMeas)
  have hd0 : ∀ x, 0 ≤ d x := by
    intro x
    dsimp [d]
    exact
      quadratic_defect_nonneg_of_density_nonneg p q hp0 hq0 x
  have hBound :=
    quadratic_defect_lintegral_le_fullL1_coefficient_sq
      μ p q hpMeas hqMeas hpInt hqInt hp0 hq0 hpOne hqOne
      K hK hRatio
  calc
    (∫ x, d x ∂μ) =
        ENNReal.toReal (∫⁻ x, ENNReal.ofReal (d x) ∂μ) := by
      exact integral_eq_lintegral_of_nonneg_ae
        (Filter.Eventually.of_forall hd0) hdMeas.aestronglyMeasurable
    _ ≤ ENNReal.toReal (ENNReal.ofReal ((2 * coefficient K) ^ 2)) := by
      exact ENNReal.toReal_mono ENNReal.ofReal_ne_top hBound
    _ = (2 * coefficient K) ^ 2 := by
      rw [ENNReal.toReal_ofReal (sq_nonneg _)]
  simpa [d]

end HaarLikelihoodRatioInfluence

end

end MGAP4D.MathlibAnalytic
