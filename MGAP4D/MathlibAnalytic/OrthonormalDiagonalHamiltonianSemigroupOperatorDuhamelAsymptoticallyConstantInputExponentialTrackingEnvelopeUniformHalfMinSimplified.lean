import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianSemigroupOperatorDuhamelAsymptoticallyConstantInputExponentialTrackingEnvelopeUniformHalfMin
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The canonical half-min denominator is at least half of the larger decay rate. -/
theorem max_sub_half_min_ge_half_max
    (δ μ : ℝ) :
    max δ μ / 2 ≤ max δ μ - min δ μ / 2 := by
  have hminmax : min δ μ ≤ max δ μ := min_le_max
  linarith

/-- The half-min forcing coefficient is bounded by the simpler coefficient
`2 * C / max δ μ`. -/
theorem div_max_sub_half_min_le_two_mul_div_max
    (δ μ C : ℝ) (hδpos : 0 < δ) (hμpos : 0 < μ) (hC : 0 ≤ C) :
    C / (max δ μ - min δ μ / 2) ≤ 2 * C / max δ μ := by
  have hmaxpos : 0 < max δ μ := lt_of_lt_of_le hδpos (le_max_left δ μ)
  have hdenpos : 0 < max δ μ - min δ μ / 2 := by
    have hminpos : 0 < min δ μ := lt_min hδpos hμpos
    have hhalfminpos : 0 < min δ μ / 2 := div_pos hminpos (by norm_num)
    have hhalfmin_lt_max : min δ μ / 2 < max δ μ := by
      have hmin_le_max : min δ μ ≤ max δ μ := min_le_max
      nlinarith
    linarith
  apply (div_le_div_iff₀ hdenpos hmaxpos).2
  have hden_ge := max_sub_half_min_ge_half_max δ μ
  nlinarith [mul_nonneg hC hmaxpos.le]

/-- Canonical resonance-free left tracking at half the slower rate, with the
simplified forcing constant `2 * C / max δ μ`. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_exponentialTrackingEnvelope_uniform_halfMin_simplified_left
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ μ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i) (hδpos : 0 < δ) (hμpos : 0 < μ)
    (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A : E →L[ℝ] E) (F U : ℝ → (E →L[ℝ] E))
    (F_lim : E →L[ℝ] E) (C : ℝ) (hC : 0 ≤ C) (hF : Continuous F)
    (hFC : ∀ s ∈ Set.Icc t₀ t,
      ‖F s - F_lim‖ ≤ C * Real.exp (-((s - t₀) * μ)))
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U ((-orthonormalDiagonalOperator b a) * U r + F r) r) :
    ‖U t - orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim‖ ≤
      (‖A - orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim‖ +
          2 * C / max δ μ) *
        Real.exp (-((t - t₀) * (min δ μ / 2))) := by
  have henv :=
    orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_exponentialTrackingEnvelope_uniform_halfMin_left
      b a δ μ hδ hδpos hμpos t₀ t ht A F U F_lim C hC hF hFC hU0 hU
  have hcoeff := div_max_sub_half_min_le_two_mul_div_max δ μ C hδpos hμpos hC
  exact henv.trans <|
    mul_le_mul_of_nonneg_right
      (add_le_add_right hcoeff ‖A - orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim‖)
      (Real.exp_pos _).le

/-- Canonical resonance-free right tracking at half the slower rate, with the
same simplified forcing constant and no commutation hypothesis. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_exponentialTrackingEnvelope_uniform_halfMin_simplified_right
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ μ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i) (hδpos : 0 < δ) (hμpos : 0 < μ)
    (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A : E →L[ℝ] E) (F U : ℝ → (E →L[ℝ] E))
    (F_lim : E →L[ℝ] E) (C : ℝ) (hC : 0 ≤ C) (hF : Continuous F)
    (hFC : ∀ s ∈ Set.Icc t₀ t,
      ‖F s - F_lim‖ ≤ C * Real.exp (-((s - t₀) * μ)))
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U (U r * (-orthonormalDiagonalOperator b a) + F r) r) :
    ‖U t - orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim‖ ≤
      (‖A - orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim‖ +
          2 * C / max δ μ) *
        Real.exp (-((t - t₀) * (min δ μ / 2))) := by
  have henv :=
    orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_exponentialTrackingEnvelope_uniform_halfMin_right
      b a δ μ hδ hδpos hμpos t₀ t ht A F U F_lim C hC hF hFC hU0 hU
  have hcoeff := div_max_sub_half_min_le_two_mul_div_max δ μ C hδpos hμpos hC
  exact henv.trans <|
    mul_le_mul_of_nonneg_right
      (add_le_add_right hcoeff ‖A - orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim‖)
      (Real.exp_pos _).le

end

end MathlibAnalytic
end MGAP4D
