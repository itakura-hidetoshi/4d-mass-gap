import MGAP4D.MathlibAnalytic.LikelihoodRatioQuadraticInfluence
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

/-!
# Integrated quadratic likelihood-ratio influence

The pointwise quadratic density-defect estimate from the preceding theorem unit
is integrated here against an arbitrary base measure.

For two nonnegative probability densities p and q with mutual likelihood-ratio
bound K >= 1, the chi-square-type defect

  (p - q)^2 / (p + q)

has total mass bounded by the square of the full-L1 influence coefficient

  (2 * c(K))^2,  c(K) = (K - 1)/(K + 1).

This is the exact normalization needed by the subsequent weighted
Cauchy--Schwarz step: after taking a square root, the influence coefficient
remains linear rather than acquiring a square-root loss.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace HaarLikelihoodRatioInfluence

/-- Integrated quadratic defect for two normalized nonnegative real densities.
The right-hand side uses the full-L1 influence normalization, deliberately
matching the repository's later profile coefficient. -/
theorem quadratic_defect_lintegral_le_fullL1_coefficient_sq
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
    (∫⁻ x,
      ENNReal.ofReal (((p x - q x) ^ 2) / (p x + q x))
      ∂μ) ≤
      ENNReal.ofReal ((2 * coefficient K) ^ 2) := by
  let c : ℝ := coefficient K
  let a : ℝ := ((2 * c) ^ 2) / 2
  have hc0 : 0 ≤ c := by
    dsimp [c, coefficient]
    exact div_nonneg (sub_nonneg.mpr hK) (by linarith)
  have ha0 : 0 ≤ a := by
    dsimp [a]
    positivity
  have hPoint : ∀ x,
      ENNReal.ofReal (((p x - q x) ^ 2) / (p x + q x)) ≤
        ENNReal.ofReal a *
          (ENNReal.ofReal (p x) + ENNReal.ofReal (q x)) := by
    intro x
    have hQuad :=
      two_mul_quadratic_defect_le_fullL1_coefficient_sq_mul_add
        K (p x) (q x) hK (hp0 x) (hq0 x)
        (hRatio x).1 (hRatio x).2
    have hReal :
        ((p x - q x) ^ 2) / (p x + q x) ≤
          a * (p x + q x) := by
      dsimp [a, c]
      linarith
    calc
      ENNReal.ofReal (((p x - q x) ^ 2) / (p x + q x)) ≤
          ENNReal.ofReal (a * (p x + q x)) :=
        ENNReal.ofReal_le_ofReal hReal
      _ = ENNReal.ofReal a * ENNReal.ofReal (p x + q x) := by
        rw [ENNReal.ofReal_mul ha0]
      _ = ENNReal.ofReal a *
          (ENNReal.ofReal (p x) + ENNReal.ofReal (q x)) := by
        rw [ENNReal.ofReal_add (hp0 x) (hq0 x)]
  have hpOfMeas : Measurable (fun x => ENNReal.ofReal (p x)) :=
    ENNReal.measurable_ofReal.comp hpMeas
  have hqOfMeas : Measurable (fun x => ENNReal.ofReal (q x)) :=
    ENNReal.measurable_ofReal.comp hqMeas
  have hpLin :
      (∫⁻ x, ENNReal.ofReal (p x) ∂μ) = 1 := by
    calc
      (∫⁻ x, ENNReal.ofReal (p x) ∂μ) =
          ENNReal.ofReal (∫ x, p x ∂μ) := by
        symm
        exact ofReal_integral_eq_lintegral_ofReal hpInt
          (Filter.Eventually.of_forall hp0)
      _ = 1 := by rw [hpOne]; norm_num
  have hqLin :
      (∫⁻ x, ENNReal.ofReal (q x) ∂μ) = 1 := by
    calc
      (∫⁻ x, ENNReal.ofReal (q x) ∂μ) =
          ENNReal.ofReal (∫ x, q x ∂μ) := by
        symm
        exact ofReal_integral_eq_lintegral_ofReal hqInt
          (Filter.Eventually.of_forall hq0)
      _ = 1 := by rw [hqOne]; norm_num
  calc
    (∫⁻ x,
      ENNReal.ofReal (((p x - q x) ^ 2) / (p x + q x))
      ∂μ) ≤
      ∫⁻ x,
        ENNReal.ofReal a *
          (ENNReal.ofReal (p x) + ENNReal.ofReal (q x))
        ∂μ := lintegral_mono hPoint
    _ = ENNReal.ofReal a *
        (∫⁻ x, ENNReal.ofReal (p x) + ENNReal.ofReal (q x) ∂μ) := by
      rw [lintegral_const_mul'' _ (hpOfMeas.add hqOfMeas).aemeasurable]
    _ = ENNReal.ofReal a *
        ((∫⁻ x, ENNReal.ofReal (p x) ∂μ) +
          ∫⁻ x, ENNReal.ofReal (q x) ∂μ) := by
      rw [lintegral_add_left hpOfMeas]
    _ = ENNReal.ofReal a * 2 := by rw [hpLin, hqLin]; norm_num
    _ = ENNReal.ofReal ((2 * coefficient K) ^ 2) := by
      rw [← ENNReal.ofReal_mul ha0]
      apply congrArg ENNReal.ofReal
      dsimp [a, c]
      ring

end HaarLikelihoodRatioInfluence

end

end MGAP4D.MathlibAnalytic
