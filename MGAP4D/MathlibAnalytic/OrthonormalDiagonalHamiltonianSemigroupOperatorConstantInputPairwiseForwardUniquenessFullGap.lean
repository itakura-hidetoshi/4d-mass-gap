import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianSemigroupOperatorConstantInputPairwiseExponentialContractionFullGap

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Left constant-input Hamiltonian evolution is forward unique from a common
    initial operator. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_constantInput_eq_of_sameInitial_fullGap_left
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i) (hδpos : 0 < δ)
    (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A B : E →L[ℝ] E)
    (U V : ℝ → (E →L[ℝ] E))
    (F_lim : E →L[ℝ] E)
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U ((-orthonormalDiagonalOperator b a) * U r + F_lim) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V ((-orthonormalDiagonalOperator b a) * V r + F_lim) r)
    (hAB : A = B) :
    U t = V t := by
  have hcontract :=
    orthonormalDiagonalHamiltonianSemigroup_operator_constantInput_pairwise_exponentialContraction_fullGap_left
      b a δ hδ hδpos t₀ t ht A B U V F_lim hU0 hV0 hU hV
  have hzero : ‖U t - V t‖ ≤ 0 := by
    simpa [hAB] using hcontract
  have hnorm : ‖U t - V t‖ = 0 := le_antisymm hzero (norm_nonneg _)
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

/-- Right constant-input Hamiltonian evolution is forward unique from a common
    initial operator, without a commutation hypothesis. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_constantInput_eq_of_sameInitial_fullGap_right
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i) (hδpos : 0 < δ)
    (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A B : E →L[ℝ] E)
    (U V : ℝ → (E →L[ℝ] E))
    (F_lim : E →L[ℝ] E)
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U (U r * (-orthonormalDiagonalOperator b a) + F_lim) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V (V r * (-orthonormalDiagonalOperator b a) + F_lim) r)
    (hAB : A = B) :
    U t = V t := by
  have hcontract :=
    orthonormalDiagonalHamiltonianSemigroup_operator_constantInput_pairwise_exponentialContraction_fullGap_right
      b a δ hδ hδpos t₀ t ht A B U V F_lim hU0 hV0 hU hV
  have hzero : ‖U t - V t‖ ≤ 0 := by
    simpa [hAB] using hcontract
  have hnorm : ‖U t - V t‖ = 0 := le_antisymm hzero (norm_nonneg _)
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

end

end MathlibAnalytic
end MGAP4D
