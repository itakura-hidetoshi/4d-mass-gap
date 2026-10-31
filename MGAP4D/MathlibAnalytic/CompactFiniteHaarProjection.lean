import MGAP4D.MathlibAnalytic.CompactEnergyMismatchMoment

/-!
# Finite quarter-normalized projection on a compact probability space

For a finite continuous family with zero means and Gram matrix one quarter
of the identity, the projection coefficients and its centered remainder
have exact integral formulas. The hypotheses are generic analytic premises;
an application to a physical Haar family must prove them for that family.

All functions and integrals retain the same given probability measure.
-/

namespace MGAP4D.MathlibAnalytic.CompactFiniteHaarProjection

open MeasureTheory
open CompactEnergyMismatchMoment
open scoped Topology BigOperators

noncomputable section
set_option autoImplicit false

variable {α ι : Type*} [MeasurableSpace α] [Fintype ι]
  (μ : Measure α)

/-- The actual integral coefficient of a function against one finite mode. -/
def coefficient (F : α → ℝ) (φ : ι → α → ℝ) (i : ι) : ℝ :=
  ∫ x, F x * φ i x ∂μ

/-- The finite projection for modes with squared norm one quarter. -/
def projection (F : α → ℝ) (φ : ι → α → ℝ) (x : α) : ℝ :=
  4 * ∑ i, coefficient μ F φ i * φ i x

/-- Remove both the actual mean and the finite quarter-normalized projection. -/
def remainder (F : α → ℝ) (φ : ι → α → ℝ) (x : α) : ℝ :=
  F x - (∫ y, F y ∂μ) - projection μ F φ x

section Topological

variable [TopologicalSpace α]

/-- A finite projection of continuous modes is continuous. -/
theorem projection_continuous (F : α → ℝ) (φ : ι → α → ℝ)
    (hφ : ∀ i, Continuous (φ i)) : Continuous (projection μ F φ) := by
  unfold projection
  apply continuous_const.mul
  exact continuous_finset_sum _ (fun i _ => continuous_const.mul (hφ i))

/-- The true centered remainder is continuous whenever its inputs are. -/
theorem remainder_continuous (F : α → ℝ) (φ : ι → α → ℝ)
    (hF : Continuous F) (hφ : ∀ i, Continuous (φ i)) :
    Continuous (remainder μ F φ) :=
  (hF.sub continuous_const).sub (projection_continuous μ F φ hφ)

section CompactProbability

variable [CompactSpace α] [BorelSpace α] [IsProbabilityMeasure μ]

private theorem ci {F : α → ℝ} (hF : Continuous F) : Integrable F μ :=
  hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- The projection has zero mean when every mode has zero mean. -/
theorem projection_mean_zero (F : α → ℝ) (φ : ι → α → ℝ)
    (hφ : ∀ i, Continuous (φ i))
    (hmean : ∀ i, (∫ x, φ i x ∂μ) = 0) :
    (∫ x, projection μ F φ x ∂μ) = 0 := by
  unfold projection
  rw [integral_const_mul,
    integral_finset_sum _ (fun i _ => (ci μ (hφ i)).const_mul _)]
  simp only [integral_const_mul, hmean, mul_zero, Finset.sum_const_zero]

/-- Centering and removing zero-mean modes leaves zero mean. -/
theorem remainder_mean_zero (F : α → ℝ) (φ : ι → α → ℝ)
    (hF : Continuous F) (hφ : ∀ i, Continuous (φ i))
    (hmean : ∀ i, (∫ x, φ i x ∂μ) = 0) :
    (∫ x, remainder μ F φ x ∂μ) = 0 := by
  have hFI : Integrable F μ := ci μ hF
  have hMean : Integrable (fun _ : α => ∫ y, F y ∂μ) μ :=
    integrable_const (∫ y, F y ∂μ)
  have hCentered : Integrable (fun x : α => F x - ∫ y, F y ∂μ) μ :=
    hFI.sub hMean
  have hProjection : Integrable (fun x : α => projection μ F φ x) μ :=
    ci μ (projection_continuous μ F φ hφ)
  unfold remainder
  rw [integral_sub hCentered hProjection,
    integral_sub hFI hMean,
    projection_mean_zero μ F φ hφ hmean]
  simp

private theorem integral_mul_projection (F Q : α → ℝ) (φ : ι → α → ℝ)
    (hQ : Continuous Q) (hφ : ∀ i, Continuous (φ i)) :
    (∫ x, Q x * projection μ F φ x ∂μ) =
      4 * ∑ i, coefficient μ F φ i * (∫ x, Q x * φ i x ∂μ) := by
  have hTerm (i : ι) :
      Integrable (fun x : α => coefficient μ F φ i * (Q x * φ i x)) μ :=
    (ci μ (hQ.mul (hφ i))).const_mul (coefficient μ F φ i)
  calc
    _ = ∫ x, 4 * ∑ i, coefficient μ F φ i * (Q x * φ i x) ∂μ := by
      apply integral_congr_ae
      filter_upwards with x
      simp only [projection, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = 4 * ∑ i, coefficient μ F φ i * (∫ x, Q x * φ i x ∂μ) := by
      rw [integral_const_mul (4 : ℝ),
        integral_finset_sum (μ := μ) (Finset.univ : Finset ι)
          (f := fun i x => coefficient μ F φ i * (Q x * φ i x))
          (fun i _ => hTerm i)]
      simp only [integral_const_mul]

omit [Fintype ι] in
private theorem centered_pairing (F : α → ℝ) (φ : ι → α → ℝ)
    (hF : Continuous F) (hφ : ∀ i, Continuous (φ i))
    (hmean : ∀ i, (∫ x, φ i x ∂μ) = 0) (i : ι) :
    (∫ x, (F x - ∫ y, F y ∂μ) * φ i x ∂μ) = coefficient μ F φ i := by
  have hProduct : Integrable (fun x : α => F x * φ i x) μ :=
    ci μ (hF.mul (hφ i))
  have hMeanProduct : Integrable (fun x : α => (∫ y, F y ∂μ) * φ i x) μ :=
    (ci μ (hφ i)).const_mul (∫ y, F y ∂μ)
  simp_rw [sub_mul]
  rw [integral_sub hProduct hMeanProduct,
    integral_const_mul (∫ y, F y ∂μ), hmean i]
  simp only [coefficient, mul_zero, sub_zero]

variable [DecidableEq ι]

/-- Exact Gram identities recover every coefficient from the projection. -/
theorem projection_pairing (F : α → ℝ) (φ : ι → α → ℝ)
    (hφ : ∀ i, Continuous (φ i))
    (hgram : ∀ i j, (∫ x, φ i x * φ j x ∂μ) =
      if i = j then (1 / 4 : ℝ) else 0) (i : ι) :
    (∫ x, projection μ F φ x * φ i x ∂μ) = coefficient μ F φ i := by
  calc
    _ = ∫ x, φ i x * projection μ F φ x ∂μ := by
      apply integral_congr_ae
      filter_upwards with x
      exact mul_comm _ _
    _ = 4 * ∑ j, coefficient μ F φ j * (∫ x, φ i x * φ j x ∂μ) :=
      integral_mul_projection μ F (φ i) φ (hφ i) hφ
    _ = 4 * (coefficient μ F φ i * (1 / 4 : ℝ)) := by
      simp [hgram, mul_ite]
    _ = coefficient μ F φ i := by ring

/-- The centered remainder is orthogonal to every finite mode. -/
theorem remainder_orthogonal (F : α → ℝ) (φ : ι → α → ℝ)
    (hF : Continuous F) (hφ : ∀ i, Continuous (φ i))
    (hmean : ∀ i, (∫ x, φ i x ∂μ) = 0)
    (hgram : ∀ i j, (∫ x, φ i x * φ j x ∂μ) =
      if i = j then (1 / 4 : ℝ) else 0) (i : ι) :
    (∫ x, remainder μ F φ x * φ i x ∂μ) = 0 := by
  have hCentered : Continuous (fun x => F x - ∫ y, F y ∂μ) :=
    hF.sub continuous_const
  calc
    _ = ∫ x, (F x - ∫ y, F y ∂μ) * φ i x -
        projection μ F φ x * φ i x ∂μ := by
      apply integral_congr_ae
      filter_upwards with x
      exact sub_mul _ _ _
    _ = (∫ x, (F x - ∫ y, F y ∂μ) * φ i x ∂μ) -
        ∫ x, projection μ F φ x * φ i x ∂μ :=
      integral_sub (ci μ (hCentered.mul (hφ i)))
        (ci μ ((projection_continuous μ F φ hφ).mul (hφ i)))
    _ = 0 := by
      rw [centered_pairing μ F φ hF hφ hmean i,
        projection_pairing μ F φ hφ hgram i]
      exact sub_self _

/-- The projection carries exactly four times the sum of squared coefficients. -/
theorem projection_square (F : α → ℝ) (φ : ι → α → ℝ)
    (hφ : ∀ i, Continuous (φ i))
    (hgram : ∀ i j, (∫ x, φ i x * φ j x ∂μ) =
      if i = j then (1 / 4 : ℝ) else 0) :
    (∫ x, (projection μ F φ x) ^ 2 ∂μ) =
      4 * ∑ i, (coefficient μ F φ i) ^ 2 := by
  simp only [pow_two]
  rw [integral_mul_projection μ F (projection μ F φ) φ
    (projection_continuous μ F φ hφ) hφ]
  simp only [projection_pairing μ F φ hφ hgram]

omit [DecidableEq ι] in
private theorem centered_projection (F : α → ℝ) (φ : ι → α → ℝ)
    (hF : Continuous F) (hφ : ∀ i, Continuous (φ i))
    (hmean : ∀ i, (∫ x, φ i x ∂μ) = 0) :
    (∫ x, (F x - ∫ y, F y ∂μ) * projection μ F φ x ∂μ) =
      4 * ∑ i, (coefficient μ F φ i) ^ 2 := by
  rw [integral_mul_projection μ F (fun x => F x - ∫ y, F y ∂μ) φ
    (hF.sub continuous_const) hφ]
  simp only [centered_pairing μ F φ hF hφ hmean, pow_two]

/-- Exact Pythagoras with the actual centered integral remainder. -/
theorem pythagoras (F : α → ℝ) (φ : ι → α → ℝ)
    (hF : Continuous F) (hφ : ∀ i, Continuous (φ i))
    (hmean : ∀ i, (∫ x, φ i x ∂μ) = 0)
    (hgram : ∀ i j, (∫ x, φ i x * φ j x ∂μ) =
      if i = j then (1 / 4 : ℝ) else 0) :
    (∫ x, (remainder μ F φ x) ^ 2 ∂μ) =
      variance μ F - 4 * ∑ i, (coefficient μ F φ i) ^ 2 := by
  have hCentered : Continuous (fun x => F x - ∫ y, F y ∂μ) :=
    hF.sub continuous_const
  have hP := projection_continuous μ F φ hφ
  have hSquare : Integrable (fun x : α => (F x - ∫ y, F y ∂μ) ^ 2) μ :=
    ci μ (hCentered.pow 2)
  have hCross : Integrable (fun x : α =>
      2 * ((F x - ∫ y, F y ∂μ) * projection μ F φ x)) μ :=
    (ci μ (hCentered.mul hP)).const_mul (2 : ℝ)
  have hProjectionSquare : Integrable (fun x : α => (projection μ F φ x) ^ 2) μ :=
    ci μ (hP.pow 2)
  have hDifference : Integrable (fun x : α =>
      (F x - ∫ y, F y ∂μ) ^ 2 -
        2 * ((F x - ∫ y, F y ∂μ) * projection μ F φ x)) μ :=
    hSquare.sub hCross
  calc
    _ = ∫ x, ((F x - ∫ y, F y ∂μ) ^ 2 -
        2 * ((F x - ∫ y, F y ∂μ) * projection μ F φ x)) +
        (projection μ F φ x) ^ 2 ∂μ := by
      apply integral_congr_ae
      filter_upwards with x
      unfold remainder
      ring
    _ = (∫ x, (F x - ∫ y, F y ∂μ) ^ 2 ∂μ) -
        2 * (∫ x, (F x - ∫ y, F y ∂μ) * projection μ F φ x ∂μ) +
        (∫ x, (projection μ F φ x) ^ 2 ∂μ) := by
      rw [integral_add hDifference hProjectionSquare,
        integral_sub hSquare hCross, integral_const_mul (2 : ℝ)]
    _ = variance μ F - 4 * ∑ i, (coefficient μ F φ i) ^ 2 := by
      rw [← variance_eq_centered μ F hF,
        centered_projection μ F φ hF hφ hmean,
        projection_square μ F φ hφ hgram]
      ring

/-- The exact projection defect is nonnegative because it is a square integral. -/
theorem residual_nonneg (F : α → ℝ) (φ : ι → α → ℝ)
    (hF : Continuous F) (hφ : ∀ i, Continuous (φ i))
    (hmean : ∀ i, (∫ x, φ i x ∂μ) = 0)
    (hgram : ∀ i j, (∫ x, φ i x * φ j x ∂μ) =
      if i = j then (1 / 4 : ℝ) else 0) :
    0 ≤ variance μ F - 4 * ∑ i, (coefficient μ F φ i) ^ 2 := by
  rw [← pythagoras μ F φ hF hφ hmean hgram]
  exact integral_nonneg (fun x => sq_nonneg (remainder μ F φ x))

/-- Finite Bessel bound with the same quarter normalization and measure. -/
theorem bessel (F : α → ℝ) (φ : ι → α → ℝ)
    (hF : Continuous F) (hφ : ∀ i, Continuous (φ i))
    (hmean : ∀ i, (∫ x, φ i x ∂μ) = 0)
    (hgram : ∀ i j, (∫ x, φ i x * φ j x ∂μ) =
      if i = j then (1 / 4 : ℝ) else 0) :
    4 * ∑ i, (coefficient μ F φ i) ^ 2 ≤ variance μ F :=
  sub_nonneg.mp (residual_nonneg μ F φ hF hφ hmean hgram)

end CompactProbability
end Topological
end
end MGAP4D.MathlibAnalytic.CompactFiniteHaarProjection

#print axioms MGAP4D.MathlibAnalytic.CompactFiniteHaarProjection.projection_continuous
#print axioms MGAP4D.MathlibAnalytic.CompactFiniteHaarProjection.remainder_continuous
#print axioms MGAP4D.MathlibAnalytic.CompactFiniteHaarProjection.projection_mean_zero
#print axioms MGAP4D.MathlibAnalytic.CompactFiniteHaarProjection.remainder_mean_zero
#print axioms MGAP4D.MathlibAnalytic.CompactFiniteHaarProjection.projection_pairing
#print axioms MGAP4D.MathlibAnalytic.CompactFiniteHaarProjection.remainder_orthogonal
#print axioms MGAP4D.MathlibAnalytic.CompactFiniteHaarProjection.projection_square
#print axioms MGAP4D.MathlibAnalytic.CompactFiniteHaarProjection.pythagoras
#print axioms MGAP4D.MathlibAnalytic.CompactFiniteHaarProjection.residual_nonneg
#print axioms MGAP4D.MathlibAnalytic.CompactFiniteHaarProjection.bessel
