import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianSemigroupOperatorDuhamelAsymptoticallyConstantInputExponentialTrackingEnvelopeUniformHalfMinSimplified
import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianSemigroupOperatorDuhamelAsymptoticallyConstantInputExponentialTrackingEnvelopeUniformHalfMinSimplifiedSettlingTime
import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianSemigroupOperatorConstantInputMatrixElementExponentialTrackingFullGapSettlingTime
import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianSemigroupOperatorConstantInputUnitBallMatrixElementSteadyStateDifferenceFullGapSettlingTime
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Under exponentially asymptotically constant input, the left tracking error acts
    pointwise at the canonical resonance-free half-min rate. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_pointwise_exponentialTracking_uniform_halfMin_simplified_left
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ μ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i) (hδpos : 0 < δ) (hμpos : 0 < μ)
    (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A : E →L[ℝ] E) (F U : ℝ → (E →L[ℝ] E))
    (F_lim : E →L[ℝ] E) (C : ℝ) (hC : 0 ≤ C) (hF : Continuous F)
    (hFC : ∀ s : ℝ, t₀ ≤ s →
      ‖F s - F_lim‖ ≤ C * Real.exp (-((s - t₀) * μ)))
    (y : E) (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U ((-orthonormalDiagonalOperator b a) * U r + F r) r) :
    ‖(U t - orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim) y‖ ≤
      ((‖A - orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim‖ +
          2 * C / max δ μ) *
        Real.exp (-((t - t₀) * (min δ μ / 2)))) * ‖y‖ := by
  have henv :=
    orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_exponentialTrackingEnvelope_uniform_halfMin_simplified_left
      b a δ μ hδ hδpos hμpos t₀ t ht A F U F_lim C hC hF
      (by intro s hs; exact hFC s hs.1) hU0 hU
  calc
    ‖(U t - orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim) y‖ ≤
        ‖U t - orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim‖ * ‖y‖ :=
      (U t - orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim).le_opNorm y
    _ ≤ ((‖A - orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim‖ +
          2 * C / max δ μ) *
        Real.exp (-((t - t₀) * (min δ μ / 2)))) * ‖y‖ :=
      mul_le_mul_of_nonneg_right henv (norm_nonneg y)

/-- The right tracking error has the identical pointwise half-min estimate, without
    a commutation hypothesis. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_pointwise_exponentialTracking_uniform_halfMin_simplified_right
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ μ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i) (hδpos : 0 < δ) (hμpos : 0 < μ)
    (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A : E →L[ℝ] E) (F U : ℝ → (E →L[ℝ] E))
    (F_lim : E →L[ℝ] E) (C : ℝ) (hC : 0 ≤ C) (hF : Continuous F)
    (hFC : ∀ s : ℝ, t₀ ≤ s →
      ‖F s - F_lim‖ ≤ C * Real.exp (-((s - t₀) * μ)))
    (y : E) (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U (U r * (-orthonormalDiagonalOperator b a) + F r) r) :
    ‖(U t - orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim) y‖ ≤
      ((‖A - orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim‖ +
          2 * C / max δ μ) *
        Real.exp (-((t - t₀) * (min δ μ / 2)))) * ‖y‖ := by
  have henv :=
    orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_exponentialTrackingEnvelope_uniform_halfMin_simplified_right
      b a δ μ hδ hδpos hμpos t₀ t ht A F U F_lim C hC hF
      (by intro s hs; exact hFC s hs.1) hU0 hU
  calc
    ‖(U t - orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim) y‖ ≤
        ‖U t - orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim‖ * ‖y‖ :=
      (U t - orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim).le_opNorm y
    _ ≤ ((‖A - orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim‖ +
          2 * C / max δ μ) *
        Real.exp (-((t - t₀) * (min δ μ / 2)))) * ‖y‖ :=
      mul_le_mul_of_nonneg_right henv (norm_nonneg y)

/-- Every left matrix element of the tracking error decays at the canonical
    resonance-free half-min rate. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_matrixElement_exponentialTracking_uniform_halfMin_simplified_left
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ μ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i) (hδpos : 0 < δ) (hμpos : 0 < μ)
    (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A : E →L[ℝ] E) (F U : ℝ → (E →L[ℝ] E))
    (F_lim : E →L[ℝ] E) (C : ℝ) (hC : 0 ≤ C) (hF : Continuous F)
    (hFC : ∀ s : ℝ, t₀ ≤ s →
      ‖F s - F_lim‖ ≤ C * Real.exp (-((s - t₀) * μ)))
    (x y : E) (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U ((-orthonormalDiagonalOperator b a) * U r + F r) r) :
    |inner ℝ x ((U t - orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim) y)| ≤
      ((‖A - orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim‖ +
          2 * C / max δ μ) *
        Real.exp (-((t - t₀) * (min δ μ / 2)))) * ‖x‖ * ‖y‖ := by
  have hpoint :=
    orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_pointwise_exponentialTracking_uniform_halfMin_simplified_left
      b a δ μ hδ hδpos hμpos t₀ t ht A F U F_lim C hC hF hFC y hU0 hU
  have hcs :
      |inner ℝ x ((U t - orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim) y)| ≤
        ‖x‖ * ‖(U t - orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim) y‖ := by
    simpa only [Real.norm_eq_abs] using
      (norm_inner_le_norm (𝕜 := ℝ) x
        ((U t - orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim) y))
  calc
    |inner ℝ x ((U t - orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim) y)| ≤
        ‖x‖ * ‖(U t - orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim) y‖ := hcs
    _ ≤ ‖x‖ *
        (((‖A - orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim‖ +
            2 * C / max δ μ) *
          Real.exp (-((t - t₀) * (min δ μ / 2)))) * ‖y‖) :=
      mul_le_mul_of_nonneg_left hpoint (norm_nonneg x)
    _ = ((‖A - orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim‖ +
          2 * C / max δ μ) *
        Real.exp (-((t - t₀) * (min δ μ / 2)))) * ‖x‖ * ‖y‖ := by ring

/-- Every right matrix element has the identical half-min estimate. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_matrixElement_exponentialTracking_uniform_halfMin_simplified_right
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ μ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i) (hδpos : 0 < δ) (hμpos : 0 < μ)
    (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A : E →L[ℝ] E) (F U : ℝ → (E →L[ℝ] E))
    (F_lim : E →L[ℝ] E) (C : ℝ) (hC : 0 ≤ C) (hF : Continuous F)
    (hFC : ∀ s : ℝ, t₀ ≤ s →
      ‖F s - F_lim‖ ≤ C * Real.exp (-((s - t₀) * μ)))
    (x y : E) (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U (U r * (-orthonormalDiagonalOperator b a) + F r) r) :
    |inner ℝ x ((U t - orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim) y)| ≤
      ((‖A - orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim‖ +
          2 * C / max δ μ) *
        Real.exp (-((t - t₀) * (min δ μ / 2)))) * ‖x‖ * ‖y‖ := by
  have hpoint :=
    orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_pointwise_exponentialTracking_uniform_halfMin_simplified_right
      b a δ μ hδ hδpos hμpos t₀ t ht A F U F_lim C hC hF hFC y hU0 hU
  have hcs :
      |inner ℝ x ((U t - orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim) y)| ≤
        ‖x‖ * ‖(U t - orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim) y‖ := by
    simpa only [Real.norm_eq_abs] using
      (norm_inner_le_norm (𝕜 := ℝ) x
        ((U t - orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim) y))
  calc
    |inner ℝ x ((U t - orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim) y)| ≤
        ‖x‖ * ‖(U t - orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim) y‖ := hcs
    _ ≤ ‖x‖ *
        (((‖A - orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim‖ +
            2 * C / max δ μ) *
          Real.exp (-((t - t₀) * (min δ μ / 2)))) * ‖y‖) :=
      mul_le_mul_of_nonneg_left hpoint (norm_nonneg x)
    _ = ((‖A - orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim‖ +
          2 * C / max δ μ) *
        Real.exp (-((t - t₀) * (min δ μ / 2)))) * ‖x‖ * ‖y‖ := by ring

/-- Every left matrix-element tracking error reaches a prescribed tolerance after
    the explicit half-min logarithmic waiting time. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_matrixElement_abs_le_epsilon_after_exponentialTracking_uniform_halfMin_simplified_left
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ μ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i) (hδpos : 0 < δ) (hμpos : 0 < μ) (t₀ : ℝ)
    (A : E →L[ℝ] E) (F U : ℝ → (E →L[ℝ] E))
    (F_lim : E →L[ℝ] E) (C : ℝ) (hC : 0 ≤ C) (hF : Continuous F)
    (hFC : ∀ s : ℝ, t₀ ≤ s →
      ‖F s - F_lim‖ ≤ C * Real.exp (-((s - t₀) * μ)))
    (x y : E) (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U ((-orthonormalDiagonalOperator b a) * U r + F r) r)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ t : ℝ,
      t₀ + max 0
          (Real.log
            ((((‖A - orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim‖ +
                2 * C / max δ μ) * ‖x‖ * ‖y‖) / ε)) /
              (min δ μ / 2)) ≤ t →
        |inner ℝ x
          ((U t - orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim) y)| ≤ ε := by
  have hmaxpos : 0 < max δ μ := lt_of_lt_of_le hδpos (le_max_left δ μ)
  have hcoeff :
      0 ≤ ‖A - orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim‖ +
        2 * C / max δ μ :=
    add_nonneg (norm_nonneg _)
      (div_nonneg (mul_nonneg (by norm_num) hC) hmaxpos.le)
  refine realFunction_abs_le_epsilon_after_exponentialBound
    (min δ μ / 2) ε
      ((‖A - orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim‖ +
          2 * C / max δ μ) * ‖x‖ * ‖y‖) t₀ ?_ hε ?_
      (fun t : ℝ => inner ℝ x
        ((U t - orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim) y)) ?_
  · exact div_pos (lt_min hδpos hμpos) (by norm_num)
  · exact mul_nonneg (mul_nonneg hcoeff (norm_nonneg x)) (norm_nonneg y)
  · intro t ht
    have hmatrix :=
      orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_matrixElement_exponentialTracking_uniform_halfMin_simplified_left
        b a δ μ hδ hδpos hμpos t₀ t ht A F U F_lim C hC hF hFC x y hU0 hU
    calc
      |inner ℝ x
          ((U t - orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim) y)| ≤
          ((‖A - orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim‖ +
              2 * C / max δ μ) *
            Real.exp (-((t - t₀) * (min δ μ / 2)))) * ‖x‖ * ‖y‖ := hmatrix
      _ = ((‖A - orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim‖ +
              2 * C / max δ μ) * ‖x‖ * ‖y‖) *
            Real.exp (-((t - t₀) * (min δ μ / 2))) := by ring

/-- Every right matrix-element tracking error has the identical explicit settling
    time, without a commutation hypothesis. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_matrixElement_abs_le_epsilon_after_exponentialTracking_uniform_halfMin_simplified_right
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ μ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i) (hδpos : 0 < δ) (hμpos : 0 < μ) (t₀ : ℝ)
    (A : E →L[ℝ] E) (F U : ℝ → (E →L[ℝ] E))
    (F_lim : E →L[ℝ] E) (C : ℝ) (hC : 0 ≤ C) (hF : Continuous F)
    (hFC : ∀ s : ℝ, t₀ ≤ s →
      ‖F s - F_lim‖ ≤ C * Real.exp (-((s - t₀) * μ)))
    (x y : E) (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U (U r * (-orthonormalDiagonalOperator b a) + F r) r)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ t : ℝ,
      t₀ + max 0
          (Real.log
            ((((‖A - orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim‖ +
                2 * C / max δ μ) * ‖x‖ * ‖y‖) / ε)) /
              (min δ μ / 2)) ≤ t →
        |inner ℝ x
          ((U t - orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim) y)| ≤ ε := by
  have hmaxpos : 0 < max δ μ := lt_of_lt_of_le hδpos (le_max_left δ μ)
  have hcoeff :
      0 ≤ ‖A - orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim‖ +
        2 * C / max δ μ :=
    add_nonneg (norm_nonneg _)
      (div_nonneg (mul_nonneg (by norm_num) hC) hmaxpos.le)
  refine realFunction_abs_le_epsilon_after_exponentialBound
    (min δ μ / 2) ε
      ((‖A - orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim‖ +
          2 * C / max δ μ) * ‖x‖ * ‖y‖) t₀ ?_ hε ?_
      (fun t : ℝ => inner ℝ x
        ((U t - orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim) y)) ?_
  · exact div_pos (lt_min hδpos hμpos) (by norm_num)
  · exact mul_nonneg (mul_nonneg hcoeff (norm_nonneg x)) (norm_nonneg y)
  · intro t ht
    have hmatrix :=
      orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_matrixElement_exponentialTracking_uniform_halfMin_simplified_right
        b a δ μ hδ hδpos hμpos t₀ t ht A F U F_lim C hC hF hFC x y hU0 hU
    calc
      |inner ℝ x
          ((U t - orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim) y)| ≤
          ((‖A - orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim‖ +
              2 * C / max δ μ) *
            Real.exp (-((t - t₀) * (min δ μ / 2)))) * ‖x‖ * ‖y‖ := hmatrix
      _ = ((‖A - orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim‖ +
              2 * C / max δ μ) * ‖x‖ * ‖y‖) *
            Real.exp (-((t - t₀) * (min δ μ / 2))) := by ring

/-- Left matrix elements reach the same steady-state tolerance after the explicit
    vector-dependent half-min waiting time. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_matrixElement_sub_steadyState_abs_le_epsilon_after_exponentialTracking_uniform_halfMin_simplified_left
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ μ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i) (hδpos : 0 < δ) (hμpos : 0 < μ) (t₀ : ℝ)
    (A : E →L[ℝ] E) (F U : ℝ → (E →L[ℝ] E))
    (F_lim : E →L[ℝ] E) (C : ℝ) (hC : 0 ≤ C) (hF : Continuous F)
    (hFC : ∀ s : ℝ, t₀ ≤ s →
      ‖F s - F_lim‖ ≤ C * Real.exp (-((s - t₀) * μ)))
    (x y : E) (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U ((-orthonormalDiagonalOperator b a) * U r + F r) r)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ t : ℝ,
      t₀ + max 0
          (Real.log
            ((((‖A - orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim‖ +
                2 * C / max δ μ) * ‖x‖ * ‖y‖) / ε)) /
              (min δ μ / 2)) ≤ t →
        |inner ℝ x (U t y) -
          inner ℝ x (orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim y)| ≤ ε := by
  intro t ht
  rw [continuousLinearMap_abs_inner_apply_sub_inner_apply_eq_abs_inner_sub_apply]
  exact
    orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_matrixElement_abs_le_epsilon_after_exponentialTracking_uniform_halfMin_simplified_left
      b a δ μ hδ hδpos hμpos t₀ A F U F_lim C hC hF hFC x y hU0 hU ε hε t ht

/-- Right matrix elements have the identical direct steady-state settling time. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_matrixElement_sub_steadyState_abs_le_epsilon_after_exponentialTracking_uniform_halfMin_simplified_right
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ μ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i) (hδpos : 0 < δ) (hμpos : 0 < μ) (t₀ : ℝ)
    (A : E →L[ℝ] E) (F U : ℝ → (E →L[ℝ] E))
    (F_lim : E →L[ℝ] E) (C : ℝ) (hC : 0 ≤ C) (hF : Continuous F)
    (hFC : ∀ s : ℝ, t₀ ≤ s →
      ‖F s - F_lim‖ ≤ C * Real.exp (-((s - t₀) * μ)))
    (x y : E) (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U (U r * (-orthonormalDiagonalOperator b a) + F r) r)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ t : ℝ,
      t₀ + max 0
          (Real.log
            ((((‖A - orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim‖ +
                2 * C / max δ μ) * ‖x‖ * ‖y‖) / ε)) /
              (min δ μ / 2)) ≤ t →
        |inner ℝ x (U t y) -
          inner ℝ x (orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim y)| ≤ ε := by
  intro t ht
  rw [continuousLinearMap_abs_inner_apply_sub_inner_apply_eq_abs_inner_sub_apply]
  exact
    orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_matrixElement_abs_le_epsilon_after_exponentialTracking_uniform_halfMin_simplified_right
      b a δ μ hδ hδpos hμpos t₀ A F U F_lim C hC hF hFC x y hU0 hU ε hε t ht

/-- A single half-min waiting time works uniformly for all left matrix elements on
    both closed unit balls. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_unitBall_matrixElement_sub_steadyState_abs_le_epsilon_after_exponentialTracking_uniform_halfMin_simplified_left
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ μ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i) (hδpos : 0 < δ) (hμpos : 0 < μ) (t₀ : ℝ)
    (A : E →L[ℝ] E) (F U : ℝ → (E →L[ℝ] E))
    (F_lim : E →L[ℝ] E) (C : ℝ) (hC : 0 ≤ C) (hF : Continuous F)
    (hFC : ∀ s : ℝ, t₀ ≤ s →
      ‖F s - F_lim‖ ≤ C * Real.exp (-((s - t₀) * μ)))
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U ((-orthonormalDiagonalOperator b a) * U r + F r) r)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ t : ℝ,
      t₀ + max 0
          (Real.log
            ((‖A - orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim‖ +
                2 * C / max δ μ) / ε) /
              (min δ μ / 2)) ≤ t →
        ∀ x y : E, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
          |inner ℝ x (U t y) -
            inner ℝ x (orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim y)| ≤ ε := by
  intro t ht x y hx hy
  have hmatrix :=
    continuousLinearMap_abs_inner_apply_sub_inner_apply_le_norm_of_norm_le_one
      (U t) (orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim) x y hx hy
  exact hmatrix.trans
    (orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_norm_sub_le_epsilon_after_exponentialTrackingEnvelope_uniform_halfMin_simplified_left
      b a δ μ hδ hδpos hμpos t₀ A F U F_lim C hC hF hFC hU0 hU ε hε t ht)

/-- The right action has the identical uniform unit-ball waiting time. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_unitBall_matrixElement_sub_steadyState_abs_le_epsilon_after_exponentialTracking_uniform_halfMin_simplified_right
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ μ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i) (hδpos : 0 < δ) (hμpos : 0 < μ) (t₀ : ℝ)
    (A : E →L[ℝ] E) (F U : ℝ → (E →L[ℝ] E))
    (F_lim : E →L[ℝ] E) (C : ℝ) (hC : 0 ≤ C) (hF : Continuous F)
    (hFC : ∀ s : ℝ, t₀ ≤ s →
      ‖F s - F_lim‖ ≤ C * Real.exp (-((s - t₀) * μ)))
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U (U r * (-orthonormalDiagonalOperator b a) + F r) r)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ t : ℝ,
      t₀ + max 0
          (Real.log
            ((‖A - orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim‖ +
                2 * C / max δ μ) / ε) /
              (min δ μ / 2)) ≤ t →
        ∀ x y : E, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
          |inner ℝ x (U t y) -
            inner ℝ x (orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim y)| ≤ ε := by
  intro t ht x y hx hy
  have hmatrix :=
    continuousLinearMap_abs_inner_apply_sub_inner_apply_le_norm_of_norm_le_one
      (U t) (orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim) x y hx hy
  exact hmatrix.trans
    (orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_norm_sub_le_epsilon_after_exponentialTrackingEnvelope_uniform_halfMin_simplified_right
      b a δ μ hδ hδpos hμpos t₀ A F U F_lim C hC hF hFC hU0 hU ε hε t ht)

end

end MathlibAnalytic
end MGAP4D
