import MGAP4D.MathlibAnalytic.CompactEnergyMismatchMoment
import Mathlib.Data.Real.Sqrt

/-!
# Exact transport of compact-probability covariance through receiver differences

A genuine receiver identity may contain an additive term that is constant
along a link section. Its two-copy difference removes that term exactly.
The covariance and variance therefore transport through the SAME signed
coefficient, without replacing the receiver or its reference measure.
-/

namespace MGAP4D.MathlibAnalytic.CompactEnergyMismatchMoment

open MeasureTheory
noncomputable section
set_option autoImplicit false

variable {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
  [CompactSpace α] [SecondCountableTopology α] [BorelSpace α]
  (μ : Measure α) [IsProbabilityMeasure μ]

/-- Covariance transport from an exact section-difference identity. The
coefficient is signed; in particular the physical coefficient may be negative. -/
theorem covariance_of_difference_eq (F U E : α → ℝ) (k : ℝ)
    (hF : Continuous F) (hU : Continuous U) (hE : Continuous E)
    (hDiff : ∀ g h, F g - F h = k * (U g - U h)) :
    covariance μ F E = k * covariance μ U E := by
  have hi :
      (∫ w : α × α, (F w.1 - F w.2) * (E w.1 - E w.2) ∂μ.prod μ) =
        k * (∫ w : α × α, (U w.1 - U w.2) * (E w.1 - E w.2) ∂μ.prod μ) := by
    calc
      _ = ∫ w : α × α,
          k * ((U w.1 - U w.2) * (E w.1 - E w.2)) ∂μ.prod μ := by
        apply integral_congr_ae
        filter_upwards with w
        rw [hDiff w.1 w.2]
        ring
      _ = _ := integral_const_mul _ _
  rw [difference_product_integral μ F E hF hE,
    difference_product_integral μ U E hU hE] at hi
  linarith

/-- Exact variance transport. No lower bound for the resulting variance
or for the physical coefficient is introduced. -/
theorem variance_of_difference_eq (F U : α → ℝ) (k : ℝ)
    (hF : Continuous F) (hU : Continuous U)
    (hDiff : ∀ g h, F g - F h = k * (U g - U h)) :
    variance μ F = k ^ 2 * variance μ U := by
  have hi :
      (∫ w : α × α, (F w.1 - F w.2) ^ 2 ∂μ.prod μ) =
        k ^ 2 * (∫ w : α × α, (U w.1 - U w.2) ^ 2 ∂μ.prod μ) := by
    calc
      _ = ∫ w : α × α, k ^ 2 * (U w.1 - U w.2) ^ 2 ∂μ.prod μ := by
        apply integral_congr_ae
        filter_upwards with w
        rw [hDiff w.1 w.2, mul_pow]
      _ = _ := integral_const_mul _ _
  rw [difference_square_integral μ F hF, difference_square_integral μ U hU] at hi
  linarith

omit [SecondCountableTopology α] in
/-- A proved pointwise source bound controls the actual centered variance.
The mean-square term is subtracted, rather than assumed to vanish. -/
theorem variance_le_sq_of_abs_le (F : α → ℝ) (K : ℝ)
    (hF : Continuous F) (hBound : ∀ x, |F x| ≤ K) :
    variance μ F ≤ K ^ 2 := by
  have hFsq : Integrable (fun x : α => (F x) ^ 2) μ :=
    (hF.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hSecond : (∫ x : α, (F x) ^ 2 ∂μ) ≤ K ^ 2 := by
    calc
      _ ≤ ∫ _x : α, K ^ 2 ∂μ := by
        apply integral_mono hFsq (integrable_const (K ^ 2))
        intro x
        have hx := abs_le.mp (hBound x)
        have hprod : 0 ≤ (K - F x) * (K + F x) :=
          mul_nonneg (sub_nonneg.mpr hx.2) (by linarith [hx.1])
        nlinarith [hprod]
      _ = K ^ 2 := by simp
  simp only [pow_two] at hSecond
  unfold variance covariance
  nlinarith [hSecond, sq_nonneg (∫ x : α, F x ∂μ)]

omit [SecondCountableTopology α] in
/-- A nonnegative, already proved source bound also controls the actual
standard deviation under the same probability measure. -/
theorem stddev_le_of_abs_le (F : α → ℝ) (K : ℝ)
    (hF : Continuous F) (hK : 0 ≤ K) (hBound : ∀ x, |F x| ≤ K) :
    Real.sqrt (variance μ F) ≤ K := by
  exact Real.sqrt_le_iff.mpr ⟨hK, variance_le_sq_of_abs_le μ F K hF hBound⟩

end
end MGAP4D.MathlibAnalytic.CompactEnergyMismatchMoment

#print axioms MGAP4D.MathlibAnalytic.CompactEnergyMismatchMoment.covariance_of_difference_eq
#print axioms MGAP4D.MathlibAnalytic.CompactEnergyMismatchMoment.variance_of_difference_eq
#print axioms MGAP4D.MathlibAnalytic.CompactEnergyMismatchMoment.variance_le_sq_of_abs_le
#print axioms MGAP4D.MathlibAnalytic.CompactEnergyMismatchMoment.stddev_le_of_abs_le
