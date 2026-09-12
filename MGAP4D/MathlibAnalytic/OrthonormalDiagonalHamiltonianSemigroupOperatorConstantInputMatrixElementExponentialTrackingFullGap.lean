import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianSemigroupOperatorConstantInputPointwiseExponentialTrackingFullGap

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- With exactly constant input, every left matrix element of the tracking error
    decays at the full spectral-gap rate. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_constantInput_matrixElement_exponentialTracking_fullGap_left
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i) (hδpos : 0 < δ)
    (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A : E →L[ℝ] E) (U : ℝ → (E →L[ℝ] E))
    (F_lim : E →L[ℝ] E) (x y : E)
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U ((-orthonormalDiagonalOperator b a) * U r + F_lim) r) :
    |inner ℝ x ((U t - orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim) y)| ≤
      (‖A - orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim‖ *
        Real.exp (-((t - t₀) * δ))) * ‖x‖ * ‖y‖ := by
  have hpoint :=
    orthonormalDiagonalHamiltonianSemigroup_operator_constantInput_pointwise_exponentialTracking_fullGap_left
      b a δ hδ hδpos t₀ t ht A U F_lim y hU0 hU
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
        ((‖A - orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim‖ *
          Real.exp (-((t - t₀) * δ))) * ‖y‖) :=
      mul_le_mul_of_nonneg_left hpoint (norm_nonneg x)
    _ = (‖A - orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim‖ *
          Real.exp (-((t - t₀) * δ))) * ‖x‖ * ‖y‖ := by
      ring

/-- With exactly constant input, every right matrix element has the same full-gap
    estimate, without a commutation hypothesis. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_constantInput_matrixElement_exponentialTracking_fullGap_right
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i) (hδpos : 0 < δ)
    (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A : E →L[ℝ] E) (U : ℝ → (E →L[ℝ] E))
    (F_lim : E →L[ℝ] E) (x y : E)
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U (U r * (-orthonormalDiagonalOperator b a) + F_lim) r) :
    |inner ℝ x ((U t - orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim) y)| ≤
      (‖A - orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim‖ *
        Real.exp (-((t - t₀) * δ))) * ‖x‖ * ‖y‖ := by
  have hpoint :=
    orthonormalDiagonalHamiltonianSemigroup_operator_constantInput_pointwise_exponentialTracking_fullGap_right
      b a δ hδ hδpos t₀ t ht A U F_lim y hU0 hU
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
        ((‖A - orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim‖ *
          Real.exp (-((t - t₀) * δ))) * ‖y‖) :=
      mul_le_mul_of_nonneg_left hpoint (norm_nonneg x)
    _ = (‖A - orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim‖ *
          Real.exp (-((t - t₀) * δ))) * ‖x‖ * ‖y‖ := by
      ring

end

end MathlibAnalytic
end MGAP4D
