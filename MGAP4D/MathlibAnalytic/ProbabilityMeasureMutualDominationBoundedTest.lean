import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- Mutual multiplicative domination of two probability measures gives the
sharp bounded-test coefficient `(K - 1) / (K + 1)`.

The proof works directly at measure level.  For `f = (phi + 1) / 2`, both `f`
and `1 - f` are nonnegative.  Applying the two measure inequalities to these
two functions and adding the resulting inequalities gives the sharp symmetric
bound without introducing Radon--Nikodym derivatives. -/
theorem probabilityMeasure_boundedTest_integral_difference_abs_le_of_pairwise_le_smul
    {α : Type*}
    [MeasurableSpace α]
    (μ ν : Measure α)
    [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν]
    (K : ℝ)
    (hK : 1 ≤ K)
    (hμν : μ ≤ ENNReal.ofReal K • ν)
    (hνμ : ν ≤ ENNReal.ofReal K • μ)
    (phi : α → ℝ)
    (hphi : StronglyMeasurable phi)
    (hphiBound : ∀ x, |phi x| ≤ 1) :
    |(∫ x, phi x ∂μ) - (∫ x, phi x ∂ν)| ≤
      2 * ((K - 1) / (K + 1)) := by
  have hKnonneg : 0 ≤ K := by linarith
  have hKtop : ENNReal.ofReal K ≠ ∞ := ENNReal.ofReal_ne_top
  have hphiIntμ : Integrable phi μ := by
    apply (integrable_const (1 : ℝ)).mono hphi.aestronglyMeasurable
    filter_upwards with x
    simpa [Real.norm_eq_abs] using hphiBound x
  have hphiIntν : Integrable phi ν := by
    apply (integrable_const (1 : ℝ)).mono hphi.aestronglyMeasurable
    filter_upwards with x
    simpa [Real.norm_eq_abs] using hphiBound x
  let f : α → ℝ := fun x => (phi x + 1) / 2
  let g : α → ℝ := fun x => 1 - f x
  have hfNonneg : ∀ x, 0 ≤ f x := by
    intro x
    have hx := (abs_le.mp (hphiBound x)).1
    dsimp [f]
    linarith
  have hfLeOne : ∀ x, f x ≤ 1 := by
    intro x
    have hx := (abs_le.mp (hphiBound x)).2
    dsimp [f]
    linarith
  have hgNonneg : ∀ x, 0 ≤ g x := by
    intro x
    dsimp [g]
    exact sub_nonneg.mpr (hfLeOne x)
  have hfIntμ : Integrable f μ := by
    dsimp [f]
    exact (hphiIntμ.add (integrable_const (1 : ℝ))).div_const 2
  have hfIntν : Integrable f ν := by
    dsimp [f]
    exact (hphiIntν.add (integrable_const (1 : ℝ))).div_const 2
  have hgIntμ : Integrable g μ := by
    dsimp [g]
    exact (integrable_const (1 : ℝ)).sub hfIntμ
  have hgIntν : Integrable g ν := by
    dsimp [g]
    exact (integrable_const (1 : ℝ)).sub hfIntν
  have hFμν :
      (∫ x, f x ∂μ) ≤ K * ∫ x, f x ∂ν := by
    calc
      (∫ x, f x ∂μ) ≤ ∫ x, f x ∂(ENNReal.ofReal K • ν) := by
        exact integral_mono_measure hμν
          (Filter.Eventually.of_forall hfNonneg)
          (hfIntν.smul_measure hKtop)
      _ = K * ∫ x, f x ∂ν := by
        rw [integral_smul_measure]
        simp [ENNReal.toReal_ofReal hKnonneg, smul_eq_mul]
  have hFνμ :
      (∫ x, f x ∂ν) ≤ K * ∫ x, f x ∂μ := by
    calc
      (∫ x, f x ∂ν) ≤ ∫ x, f x ∂(ENNReal.ofReal K • μ) := by
        exact integral_mono_measure hνμ
          (Filter.Eventually.of_forall hfNonneg)
          (hfIntμ.smul_measure hKtop)
      _ = K * ∫ x, f x ∂μ := by
        rw [integral_smul_measure]
        simp [ENNReal.toReal_ofReal hKnonneg, smul_eq_mul]
  have hGμν :
      (∫ x, g x ∂μ) ≤ K * ∫ x, g x ∂ν := by
    calc
      (∫ x, g x ∂μ) ≤ ∫ x, g x ∂(ENNReal.ofReal K • ν) := by
        exact integral_mono_measure hμν
          (Filter.Eventually.of_forall hgNonneg)
          (hgIntν.smul_measure hKtop)
      _ = K * ∫ x, g x ∂ν := by
        rw [integral_smul_measure]
        simp [ENNReal.toReal_ofReal hKnonneg, smul_eq_mul]
  have hGνμ :
      (∫ x, g x ∂ν) ≤ K * ∫ x, g x ∂μ := by
    calc
      (∫ x, g x ∂ν) ≤ ∫ x, g x ∂(ENNReal.ofReal K • μ) := by
        exact integral_mono_measure hνμ
          (Filter.Eventually.of_forall hgNonneg)
          (hgIntμ.smul_measure hKtop)
      _ = K * ∫ x, g x ∂μ := by
        rw [integral_smul_measure]
        simp [ENNReal.toReal_ofReal hKnonneg, smul_eq_mul]
  have hGμ : (∫ x, g x ∂μ) = 1 - ∫ x, f x ∂μ := by
    dsimp [g]
    rw [integral_sub (integrable_const (1 : ℝ)) hfIntμ]
    simp
  have hGν : (∫ x, g x ∂ν) = 1 - ∫ x, f x ∂ν := by
    dsimp [g]
    rw [integral_sub (integrable_const (1 : ℝ)) hfIntν]
    simp
  rw [hGμ, hGν] at hGμν hGνμ
  have hden : 0 < K + 1 := by linarith
  have hUpper :
      (∫ x, f x ∂μ) - (∫ x, f x ∂ν) ≤
        (K - 1) / (K + 1) := by
    apply (le_div_iff₀ hden).2
    nlinarith [hFμν, hGνμ]
  have hUpperSwap :
      (∫ x, f x ∂ν) - (∫ x, f x ∂μ) ≤
        (K - 1) / (K + 1) := by
    apply (le_div_iff₀ hden).2
    nlinarith [hFνμ, hGμν]
  have hAbsF :
      |(∫ x, f x ∂μ) - (∫ x, f x ∂ν)| ≤
        (K - 1) / (K + 1) := by
    exact abs_le.mpr ⟨by linarith, hUpper⟩
  have hfμ :
      (∫ x, f x ∂μ) = ((∫ x, phi x ∂μ) + 1) / 2 := by
    dsimp [f]
    rw [integral_div, integral_add hphiIntμ (integrable_const (1 : ℝ))]
    simp
  have hfν :
      (∫ x, f x ∂ν) = ((∫ x, phi x ∂ν) + 1) / 2 := by
    dsimp [f]
    rw [integral_div, integral_add hphiIntν (integrable_const (1 : ℝ))]
    simp
  have hDiff :
      (∫ x, phi x ∂μ) - (∫ x, phi x ∂ν) =
        2 * ((∫ x, f x ∂μ) - (∫ x, f x ∂ν)) := by
    rw [hfμ, hfν]
    ring
  rw [hDiff, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  exact mul_le_mul_of_nonneg_left hAbsF (by norm_num)

end

end MathlibAnalytic
end MGAP4D
