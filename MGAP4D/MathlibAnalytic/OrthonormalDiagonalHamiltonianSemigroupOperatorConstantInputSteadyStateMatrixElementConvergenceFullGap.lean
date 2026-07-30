import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianSemigroupOperatorConstantInputWeakMatrixElementConvergenceFullGap

namespace MGAP4D
namespace MathlibAnalytic

open Filter

noncomputable section

/-- Operator-norm convergence implies convergence of every scalar matrix element
    directly to the corresponding matrix element of the limit operator. -/
theorem continuousLinearMap_tendsto_inner_apply_of_tendsto
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (U : ℝ → (E →L[ℝ] E)) (S : E →L[ℝ] E) (x y : E)
    (hU : Tendsto U atTop (nhds S)) :
    Tendsto (fun t : ℝ => inner ℝ x (U t y)) atTop
      (nhds (inner ℝ x (S y))) := by
  have hzero :=
    continuousLinearMap_tendsto_inner_sub_apply_zero_of_tendsto U S x y hU
  have hconst :
      Tendsto (fun _ : ℝ => inner ℝ x (S y)) atTop
        (nhds (inner ℝ x (S y))) :=
    tendsto_const_nhds
  simpa [inner_sub_right] using hzero.add hconst

/-- Under exactly constant input, every left matrix element converges directly to
    the corresponding left steady-state matrix element. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_constantInput_matrixElement_tendsto_steadyState_fullGap_left
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i) (hδpos : 0 < δ) (t₀ : ℝ)
    (A : E →L[ℝ] E) (U : ℝ → (E →L[ℝ] E))
    (F_lim : E →L[ℝ] E) (x y : E)
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U ((-orthonormalDiagonalOperator b a) * U r + F_lim) r) :
    Tendsto (fun t : ℝ => inner ℝ x (U t y)) atTop
      (nhds (inner ℝ x
        (orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim y))) := by
  exact continuousLinearMap_tendsto_inner_apply_of_tendsto
    U (orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim) x y
    (orthonormalDiagonalHamiltonianSemigroup_operator_constantInput_tendsto_steadyState_fullGap_left
      b a δ hδ hδpos t₀ A U F_lim hU0 hU)

/-- Under exactly constant input, every right matrix element converges directly to
    the corresponding right steady-state matrix element, without commutation. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_constantInput_matrixElement_tendsto_steadyState_fullGap_right
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i) (hδpos : 0 < δ) (t₀ : ℝ)
    (A : E →L[ℝ] E) (U : ℝ → (E →L[ℝ] E))
    (F_lim : E →L[ℝ] E) (x y : E)
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U (U r * (-orthonormalDiagonalOperator b a) + F_lim) r) :
    Tendsto (fun t : ℝ => inner ℝ x (U t y)) atTop
      (nhds (inner ℝ x
        (orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim y))) := by
  exact continuousLinearMap_tendsto_inner_apply_of_tendsto
    U (orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim) x y
    (orthonormalDiagonalHamiltonianSemigroup_operator_constantInput_tendsto_steadyState_fullGap_right
      b a δ hδ hδpos t₀ A U F_lim hU0 hU)

end

end MathlibAnalytic
end MGAP4D
