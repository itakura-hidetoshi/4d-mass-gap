import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianSemigroupOperatorConstantInputMatrixElementExponentialTrackingFullGapSettlingTime

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The difference of two scalar matrix elements is exactly the matrix element of
    the operator difference. -/
theorem continuousLinearMap_abs_inner_apply_sub_inner_apply_eq_abs_inner_sub_apply
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (U S : E →L[ℝ] E) (x y : E) :
    |inner ℝ x (U y) - inner ℝ x (S y)| =
      |inner ℝ x ((U - S) y)| := by
  simp

/-- Every left matrix element approaches its steady-state matrix element within a
    prescribed tolerance after the explicit full-gap logarithmic waiting time. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_constantInput_matrixElement_sub_steadyState_abs_le_epsilon_after_exponentialTracking_fullGap_left
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i) (hδpos : 0 < δ) (t₀ : ℝ)
    (A : E →L[ℝ] E) (U : ℝ → (E →L[ℝ] E))
    (F_lim : E →L[ℝ] E) (x y : E)
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U ((-orthonormalDiagonalOperator b a) * U r + F_lim) r)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ t : ℝ,
      t₀ + max 0
          (Real.log
            ((‖A - orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim‖ *
                ‖x‖ * ‖y‖) / ε) / δ) ≤ t →
        |inner ℝ x (U t y) -
          inner ℝ x (orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim y)| ≤ ε := by
  intro t ht
  rw [continuousLinearMap_abs_inner_apply_sub_inner_apply_eq_abs_inner_sub_apply]
  exact
    orthonormalDiagonalHamiltonianSemigroup_operator_constantInput_matrixElement_abs_le_epsilon_after_exponentialTracking_fullGap_left
      b a δ hδ hδpos t₀ A U F_lim x y hU0 hU ε hε t ht

/-- Every right matrix element has the identical direct steady-state settling time,
    without a commutation hypothesis. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_constantInput_matrixElement_sub_steadyState_abs_le_epsilon_after_exponentialTracking_fullGap_right
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i) (hδpos : 0 < δ) (t₀ : ℝ)
    (A : E →L[ℝ] E) (U : ℝ → (E →L[ℝ] E))
    (F_lim : E →L[ℝ] E) (x y : E)
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U (U r * (-orthonormalDiagonalOperator b a) + F_lim) r)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ t : ℝ,
      t₀ + max 0
          (Real.log
            ((‖A - orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim‖ *
                ‖x‖ * ‖y‖) / ε) / δ) ≤ t →
        |inner ℝ x (U t y) -
          inner ℝ x (orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim y)| ≤ ε := by
  intro t ht
  rw [continuousLinearMap_abs_inner_apply_sub_inner_apply_eq_abs_inner_sub_apply]
  exact
    orthonormalDiagonalHamiltonianSemigroup_operator_constantInput_matrixElement_abs_le_epsilon_after_exponentialTracking_fullGap_right
      b a δ hδ hδpos t₀ A U F_lim x y hU0 hU ε hε t ht

end

end MathlibAnalytic
end MGAP4D
