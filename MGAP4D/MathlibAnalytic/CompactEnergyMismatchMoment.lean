import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

/-!
# Signed energy mismatch on a compact probability space

The full negative part of the two-copy signed energy pairing has an
exact covariance formula.  Removing any nonnegative aligned energy
component can only increase that negative part.  More strongly, square
completion bounds the full mismatch by the actual affine-energy residual
variance, without assuming that the residual or the tail is small.

All integrals use the same given probability measure.  These are analysis
identities and estimates, not replacements for any interacting law.
-/

namespace MGAP4D.MathlibAnalytic.CompactEnergyMismatchMoment

open MeasureTheory
open scoped Topology
noncomputable section
set_option autoImplicit false

variable {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
  [CompactSpace α] [SecondCountableTopology α] [BorelSpace α]
  (μ : Measure α) [IsProbabilityMeasure μ]

/-- Covariance for the original probability measure. -/
def covariance (F E : α → ℝ) : ℝ :=
  (∫ x, F x * E x ∂μ) - (∫ x, F x ∂μ) * (∫ x, E x ∂μ)

/-- The actual centered variance; `variance_eq_centered` identifies its
raw second-moment presentation with the centered square integral. -/
def variance (F : α → ℝ) : ℝ := covariance μ F F

/-- The same signed two-copy receiver/energy pairing, before taking a part. -/
def signedPair (b s : ℝ) (F E : α → ℝ) (w : α × α) : ℝ :=
  (2 * b) * (s * (F w.1 - F w.2) * (E w.2 - E w.1))

/-- The entire negative part, integrated over the original two-copy law. -/
def mismatch (b s : ℝ) (F E : α → ℝ) : ℝ :=
  ∫ w : α × α, max (-signedPair b s F E w) 0 ∂μ.prod μ

/-- Affine-energy residual.  Constants may be retained because variance
and the two-copy pairing annihilate them exactly. -/
def residual (s a : ℝ) (F E : α → ℝ) (x : α) : ℝ :=
  F x + s * a * E x

private theorem ci {β : Type*} [TopologicalSpace β] [MeasurableSpace β]
    [CompactSpace β] [BorelSpace β] (ρ : Measure β) [IsFiniteMeasure ρ]
    {f : β → ℝ} (hf : Continuous f) : Integrable f ρ :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem signedPair_continuous (b s : ℝ) (F E : α → ℝ)
    (hF : Continuous F) (hE : Continuous E) :
    Continuous (signedPair b s F E) := by
  exact continuous_const.mul
    ((continuous_const.mul ((hF.comp continuous_fst).sub (hF.comp continuous_snd))).mul
      ((hE.comp continuous_snd).sub (hE.comp continuous_fst)))

theorem mismatch_integrable (b s : ℝ) (F E : α → ℝ)
    (hF : Continuous F) (hE : Continuous E) :
    Integrable (fun w : α × α => max (-signedPair b s F E w) 0) (μ.prod μ) :=
  ci (μ.prod μ) ((signedPair_continuous b s F E hF hE).neg.max continuous_const)

/-- The exact two-copy covariance identity. -/
theorem difference_product_integral (F E : α → ℝ)
    (hF : Continuous F) (hE : Continuous E) :
    (∫ w : α × α, (F w.1 - F w.2) * (E w.1 - E w.2) ∂μ.prod μ) =
      2 * covariance μ F E := by
  have h11 := ci (μ.prod μ) ((hF.mul hE).comp continuous_fst)
  have h22 := ci (μ.prod μ) ((hF.mul hE).comp continuous_snd)
  have h12 := ci (μ.prod μ) ((hF.comp continuous_fst).mul (hE.comp continuous_snd))
  have h21 := ci (μ.prod μ) ((hE.comp continuous_fst).mul (hF.comp continuous_snd))
  calc
    _ = ∫ w : α × α,
        ((F w.1 * E w.1 + F w.2 * E w.2) - F w.1 * E w.2) -
          E w.1 * F w.2 ∂μ.prod μ := by
      apply integral_congr_ae
      filter_upwards with w
      ring
    _ = 2 * covariance μ F E := by
      rw [integral_sub ((h11.add h22).sub h12) h21,
        integral_sub (h11.add h22) h12, integral_add h11 h22,
        integral_fun_fst, integral_fun_snd, integral_prod_mul, integral_prod_mul]
      simp [covariance] <;> ring

/-- A genuine full pair-square integral, rather than a pointwise estimate. -/
theorem difference_square_integral (F : α → ℝ) (hF : Continuous F) :
    (∫ w : α × α, (F w.1 - F w.2) ^ 2 ∂μ.prod μ) =
      2 * variance μ F := by
  simpa only [variance, pow_two] using difference_product_integral μ F F hF hF

theorem variance_nonneg (F : α → ℝ) (hF : Continuous F) :
    0 ≤ variance μ F := by
  have h := integral_nonneg (μ := μ.prod μ)
    (fun w : α × α => sq_nonneg (F w.1 - F w.2))
  rw [difference_square_integral μ F hF] at h
  linarith

/-- The variance in the bound is precisely the centered L2 error. -/
theorem variance_eq_centered (F : α → ℝ) (hF : Continuous F) :
    variance μ F = ∫ x, (F x - ∫ y, F y ∂μ) ^ 2 ∂μ := by
  let m : ℝ := ∫ y, F y ∂μ
  have hFI := ci μ hF
  have hFF := ci μ (hF.mul hF)
  have hp (x : α) : (F x - m) ^ 2 = F x * F x - (2 * m) * F x + m ^ 2 := by
    ring
  change covariance μ F F = ∫ x, (F x - m) ^ 2 ∂μ
  simp_rw [hp]
  rw [integral_add (hFF.sub (hFI.const_mul (2 * m))) (integrable_const _),
    integral_sub hFF (hFI.const_mul (2 * m)), integral_const_mul]
  simp [covariance, m] <;> ring

/-- In the convention E(h)-E(g), the signed integral has a minus sign. -/
theorem signedPair_integral_eq_covariance (b s : ℝ) (F E : α → ℝ)
    (hF : Continuous F) (hE : Continuous E) :
    (∫ w : α × α, signedPair b s F E w ∂μ.prod μ) =
      -4 * b * s * covariance μ F E := by
  have hp (w : α × α) : signedPair b s F E w =
      (-2 * b * s) * ((F w.1 - F w.2) * (E w.1 - E w.2)) := by
    unfold signedPair
    ring
  simp_rw [hp]
  rw [integral_const_mul, difference_product_integral μ F E hF hE]
  ring

private theorem negPart_eq (x : ℝ) : max (-x) 0 = (|x| - x) / 2 := by
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx, max_eq_right (neg_nonpos.mpr hx)]
    ring
  · have hx0 : x ≤ 0 := (lt_of_not_ge hx).le
    rw [abs_of_nonpos hx0, max_eq_left (neg_nonneg.mpr hx0)]
    ring

/-- Exact full-tail decomposition; neither orientation is discarded. -/
theorem mismatch_eq_abs_covariance (b s : ℝ) (F E : α → ℝ)
    (hF : Continuous F) (hE : Continuous E) :
    mismatch μ b s F E =
      ((∫ w : α × α, |signedPair b s F E w| ∂μ.prod μ) +
        4 * b * s * covariance μ F E) / 2 := by
  have hi := ci (μ.prod μ) (signedPair_continuous b s F E hF hE)
  unfold mismatch
  simp_rw [negPart_eq]
  rw [integral_div, integral_sub hi.abs hi,
    signedPair_integral_eq_covariance μ b s F E hF hE]
  ring

/-- The two full orientations differ by the actual signed covariance.
Thus a nonnegative oriented covariance cannot give a positive signed
margin by merely dropping or bounding the opposite part. -/
theorem mismatch_opposite_sub_eq_covariance (b s : ℝ) (F E : α → ℝ)
    (hF : Continuous F) (hE : Continuous E) :
    mismatch μ b (-s) F E - mismatch μ b s F E =
      -4 * b * s * covariance μ F E := by
  have hp := mismatch_eq_abs_covariance μ b s F E hF hE
  have hn := mismatch_eq_abs_covariance μ b (-s) F E hF hE
  have heq (w : α × α) : signedPair b (-s) F E w = -signedPair b s F E w := by
    unfold signedPair
    ring
  simp_rw [heq, abs_neg] at hn
  linarith

/-- A nonnegative aligned energy component contributes a nonnegative square.
The result is valid for every real orientation scalar s. -/
theorem signedPair_eq_residual_add (b s a : ℝ) (F E : α → ℝ) (w : α × α) :
    signedPair b s F E w = signedPair b s (residual s a F E) E w +
      (2 * b * a * s ^ 2) * (E w.1 - E w.2) ^ 2 := by
  unfold signedPair residual
  ring

theorem mismatch_le_residual (b s a : ℝ) (hb : 0 ≤ b) (ha : 0 ≤ a)
    (F E : α → ℝ) (hF : Continuous F) (hE : Continuous E) :
    mismatch μ b s F E ≤ mismatch μ b s (residual s a F E) E := by
  have hR : Continuous (residual s a F E) :=
    hF.add (continuous_const.mul hE)
  apply integral_mono (mismatch_integrable μ b s F E hF hE)
    (mismatch_integrable μ b s (residual s a F E) E hR hE)
  intro w
  apply max_le_max_right 0
  rw [signedPair_eq_residual_add b s a F E w]
  have hp : 0 ≤ (2 * b * a * s ^ 2) * (E w.1 - E w.2) ^ 2 := by positivity
  linarith

/-- Square completion controls every point of the negative tail by the
actual residual difference.  No tail-cap or alignment hypothesis occurs. -/
theorem mismatch_pointwise_le_residual_square (b s a : ℝ)
    (hb : 0 ≤ b) (ha : 0 < a) (F E : α → ℝ) (w : α × α) :
    max (-signedPair b s F E w) 0 ≤
      b * (residual s a F E w.1 - residual s a F E w.2) ^ 2 / (2 * a) := by
  refine max_le ?_ (div_nonneg (mul_nonneg hb (sq_nonneg _)) (by positivity))
  apply (le_div_iff₀ (show (0 : ℝ) < 2 * a by positivity)).mpr
  dsimp [signedPair, residual]
  have hp := mul_nonneg hb
    (sq_nonneg (F w.1 - F w.2 - s * a * (E w.1 - E w.2)))
  nlinarith [hp]

/-- Full original-law mismatch is bounded by its genuine centered
affine-energy residual variance.  The factor b/a is explicit. -/
theorem mismatch_le_residual_variance (b s a : ℝ)
    (hb : 0 ≤ b) (ha : 0 < a)
    (F E : α → ℝ) (hF : Continuous F) (hE : Continuous E) :
    mismatch μ b s F E ≤ (b / a) * variance μ (residual s a F E) := by
  have hR : Continuous (residual s a F E) :=
    hF.add (continuous_const.mul hE)
  have hRSq : Continuous
      (fun w : α × α => (residual s a F E w.1 - residual s a F E w.2) ^ 2) :=
    ((hR.comp continuous_fst).sub (hR.comp continuous_snd)).pow 2
  calc
    _ ≤ ∫ w : α × α,
        b * (residual s a F E w.1 - residual s a F E w.2) ^ 2 / (2 * a)
          ∂μ.prod μ := by
      apply integral_mono (mismatch_integrable μ b s F E hF hE)
        (ci (μ.prod μ) ((continuous_const.mul hRSq).div_const (2 * a)))
      exact mismatch_pointwise_le_residual_square b s a hb ha F E
    _ = (b / a) * variance μ (residual s a F E) := by
      rw [integral_div, integral_const_mul, difference_square_integral μ _ hR]
      field_simp [ha.ne'] <;> ring

/-- Exact residual variance expansion, with the covariance sign retained. -/
theorem variance_residual (s a : ℝ) (F E : α → ℝ)
    (hF : Continuous F) (hE : Continuous E) :
    variance μ (residual s a F E) = variance μ F +
      2 * s * a * covariance μ F E + (s * a) ^ 2 * variance μ E := by
  let DF : α × α → ℝ := fun w => F w.1 - F w.2
  let DE : α × α → ℝ := fun w => E w.1 - E w.2
  have hDF : Continuous DF := (hF.comp continuous_fst).sub (hF.comp continuous_snd)
  have hDE : Continuous DE := (hE.comp continuous_fst).sub (hE.comp continuous_snd)
  have hR : Continuous (residual s a F E) :=
    hF.add (continuous_const.mul hE)
  have hFF := ci (μ.prod μ) (hDF.pow 2)
  have hFE := ci (μ.prod μ) (hDF.mul hDE)
  have hEE := ci (μ.prod μ) (hDE.pow 2)
  have hp (w : α × α) :
      (residual s a F E w.1 - residual s a F E w.2) ^ 2 =
        (DF w ^ 2 + (2 * s * a) * (DF w * DE w)) + (s * a) ^ 2 * DE w ^ 2 := by
    dsimp [residual, DF, DE]
    ring
  have hi : (∫ w : α × α,
      (residual s a F E w.1 - residual s a F E w.2) ^ 2 ∂μ.prod μ) =
        (∫ w, DF w ^ 2 ∂μ.prod μ) + (2 * s * a) *
          (∫ w, DF w * DE w ∂μ.prod μ) + (s * a) ^ 2 *
            (∫ w, DE w ^ 2 ∂μ.prod μ) := by
    simp_rw [hp]
    rw [integral_add (hFF.add (hFE.const_mul _)) (hEE.const_mul _),
      integral_add hFF (hFE.const_mul _), integral_const_mul, integral_const_mul]
  dsimp [DF, DE] at hi
  rw [difference_square_integral μ _ hR, difference_square_integral μ F hF,
    difference_square_integral μ E hE, difference_product_integral μ F E hF hE] at hi
  linarith

end
end MGAP4D.MathlibAnalytic.CompactEnergyMismatchMoment

#print axioms MGAP4D.MathlibAnalytic.CompactEnergyMismatchMoment.signedPair_continuous
#print axioms MGAP4D.MathlibAnalytic.CompactEnergyMismatchMoment.mismatch_integrable
#print axioms MGAP4D.MathlibAnalytic.CompactEnergyMismatchMoment.difference_product_integral
#print axioms MGAP4D.MathlibAnalytic.CompactEnergyMismatchMoment.difference_square_integral
#print axioms MGAP4D.MathlibAnalytic.CompactEnergyMismatchMoment.variance_nonneg
#print axioms MGAP4D.MathlibAnalytic.CompactEnergyMismatchMoment.variance_eq_centered
#print axioms MGAP4D.MathlibAnalytic.CompactEnergyMismatchMoment.signedPair_integral_eq_covariance
#print axioms MGAP4D.MathlibAnalytic.CompactEnergyMismatchMoment.mismatch_eq_abs_covariance
#print axioms MGAP4D.MathlibAnalytic.CompactEnergyMismatchMoment.mismatch_opposite_sub_eq_covariance
#print axioms MGAP4D.MathlibAnalytic.CompactEnergyMismatchMoment.signedPair_eq_residual_add
#print axioms MGAP4D.MathlibAnalytic.CompactEnergyMismatchMoment.mismatch_le_residual
#print axioms MGAP4D.MathlibAnalytic.CompactEnergyMismatchMoment.mismatch_pointwise_le_residual_square
#print axioms MGAP4D.MathlibAnalytic.CompactEnergyMismatchMoment.mismatch_le_residual_variance
#print axioms MGAP4D.MathlibAnalytic.CompactEnergyMismatchMoment.variance_residual
